;;;-*- Package: :user; Syntax: Common-Lisp; Mode: Lisp -*-; 

(in-package :user :use '(:delta-blue))

;; create-proto-constraint is a useful hack for defining constraints.  It
;; analyzes the forms given to it, and figures out the variable indices for
;; the method output variables.  See defn of create-equal-constraint below
;; for an example of using it.

(defstruct (proto-constraint (:type list)
			     :named)
  variable-keywords
  methods)

(defmacro create-proto-constraint (var-names . method-specs)
  (let* ((var-keywords (loop for var-name in var-names
			     collect (intern (symbol-name var-name)
					     (find-package "KEYWORD"))))
	 (method-output-indices
	  (loop for spec in method-specs collect
		(cond ((and (listp spec)
			    (eql 'setf (first spec))
			    (position (second spec) var-names))
		       (position (second spec) var-names))
		      (t (error "bad method form in create-proto-constraint: ~S" spec)))))
	 (method-forms
	  (loop for spec in method-specs collect `(progn ,@(cddr spec))))
	 (method-forms
	  (loop for output-var-index in method-output-indices
		as method-form in method-forms
		collect
		(let ((cn-var (gentemp))
		      (cn-vars-var (gentemp)))
		  `(create-method
		    :output-index ,output-var-index
		    :code
		    (function
		     (lambda (,cn-var)
		       (let* ((,cn-vars-var (CN-variables ,cn-var))
			      ;; create set of forms like
			      ;; (<varname> (VAR-value (nth <index> <varlist>)))
			      ;; to set variable names used in method form
			      ,@(loop for input-var in var-names
				      as index from 0 by 1
				      collect `(,input-var
						(VAR-value (nth ,index ,cn-vars-var))))
			      )
			 ,method-form)))
		    ))))
	 )	
    `(make-proto-constraint
      :variable-keywords (quote ,var-keywords)
      :methods (list ,@method-forms))))

(defun clone-proto-constraint (&rest key-vals)
  (let* ((proto (getf key-vals :proto nil))
	 (var-keywords (proto-constraint-variable-keywords proto))
	 (vars (loop for key in var-keywords
		     collect (getf key-vals key nil)))
	 (methods (proto-constraint-methods proto))
	 )
    (when (member nil vars)
	  (error " all vars ~S not specified in clone-proto-constraint ~S"
		 var-keywords key-vals))
    (create-constraint
     :strength (getf key-vals :strength :required)
     :input-flag (getf key-vals :input-flag nil)
     :methods methods
     :variables vars
     )))

;; simple constraints

(defvar *proto-stay-constraint*
  (create-proto-constraint (v)
			   (setf v v)))

(defun create-stay-constraint (var strength)
  ;; a stay constraint makes the var value stay the same
  ;; (though other stronger constraints may have changed it)
 (clone-proto-constraint
  :proto *proto-stay-constraint*
  :strength strength
  :v var))

(defun create-edit-constraint (var strength)
  ;; an edit constraint is exactly the same as a stay constraint,
  ;; except that the :input-flag of the constraint is set to t,
  ;; indicating that the variable is set from "outside" the solver.
 (clone-proto-constraint
  :proto *proto-stay-constraint*
  :strength strength
  :input-flag t
  :v var))

(defvar *proto-equal-constraint*
  (create-proto-constraint (a b)
			   (setf a b)
			   (setf b a)))

(defun create-equal-constraint (var1 var2 strength)
 (clone-proto-constraint
  :proto *proto-equal-constraint*
  :strength strength
  :a var1
  :b var2))

;; chain benchmark

(defun chain-create (count)
  (setq *chain-vars* (loop for cnt from 1 to count
		      collect (create-variable :value nil)))
  (setq *chain-first-var* (car *chain-vars*))
  (setq *chain-last-var* (car (last *chain-vars*)))
  (setq *chain-cns* (loop for (a b) on *chain-vars* when b collect
		      (create-equal-constraint b a :required)))
  (setq *chain-edit-first-strong*
    (create-edit-constraint *chain-first-var* :strong))
  (setq *chain-edit-last-strong*
    (create-edit-constraint *chain-last-var* :strong))
  (setq *chain-stay-last-medium*
    (create-stay-constraint *chain-last-var* :medium))
  )

(defun chain-add-eq-constraints ()
  (loop for cn in *chain-cns* do (add-constraint cn))
  (add-constraint *chain-stay-last-medium*))

(defun chain-case-1 ()
  (format t "~%...case 1: adding strong edit constraint to front...~%")
  (time (add-constraint *chain-edit-first-strong*))
  (format t "~%...make plan...~%")
  (time (setq *chain-plan* (extract-plan-from-constraints
			    (list *chain-edit-first-strong*))))
  (format t "~%...execute plan...~%")
  (setq *chain-value* (random 99999))
  (setf (VAR-value *chain-first-var*) *chain-value*)
  (time (execute-plan *chain-plan*))
  (when (not (equal (VAR-value *chain-last-var*) *chain-value*))
    (cerror "cont" "value not propagated through chain!"))
  (format t "~%...remove edit constraint...~%")
  (time (remove-constraint *chain-edit-first-strong*))
  )

(defun chain-case-2 ()
  (format t "~%...case 2: adding strong edit constraint to back...~%")
  (time (add-constraint *chain-edit-last-strong*))
  (format t "~%...make plan...~%")
  (time (setq *chain-plan* (extract-plan-from-constraints
			    (list *chain-edit-last-strong*))))
  (format t "~%...execute plan...~%")
  (setq *chain-value* (random 99999))
  (setf (VAR-value *chain-last-var*) *chain-value*)
  (time (execute-plan *chain-plan*))
  (when (not (equal (VAR-value *chain-first-var*) *chain-value*))
	(cerror "cont" "value not propagated through chain!"))
  (format t "~%...remove edit constraint...~%")
  (time (remove-constraint *chain-edit-last-strong*))
  )

(defun test-chain (count)
  ;; makes a chain of vars with equality constraints
  ;; between them, and a medium stay constraint on the last one.
  (format t "...creating chain of ~A constraints...~%" count)
  (time (chain-create count))
  (format t "~%...adding equality and stay constraints...~%")
  (time (chain-add-eq-constraints))
  (chain-case-1)
  (chain-case-2)
  )

(defvar *proto-scale-offset-constraint*
  (create-proto-constraint (source dest scale offset)
			   (setf dest (+ (* source scale) offset))
			   (setf source (/ (- dest offset) scale))))

(defun create-scale-offset-constraint (source-var
				       dest-var
				       scale-var
				       offset-var
				       strength)
 (clone-proto-constraint
  :proto *proto-scale-offset-constraint*
  :strength strength
  :source source-var
  :dest dest-var
  :offset offset-var
  :scale scale-var))

(defun test-projection (count)
  ;; makes a set of data points and projected points, with each pair
  ;; related by a single scale and offset value, and measure
  ;; how long it takes to change the scale.
  (format t "...creating data and projected point sets with ~A elements...~%" count)
  (time (progn 
	  (setq *proj-source-points*
		(loop for cnt from 1 to count
		      collect (create-variable :value 1.0)))
	  (setq *proj-dest-points*
		(loop for cnt from 1 to count
		      collect (create-variable :value 1.0)))
	  (setq *proj-scale* (create-variable :value 1.0))
	  (setq *proj-offset* (create-variable :value 1.0))
	  (setq *proj-scale-constraints*
		(loop for data in *proj-source-points*
		      as proj in *proj-dest-points*
		      collect (create-scale-offset-constraint
			       data proj *proj-scale* *proj-offset*
			       :required)))
	  (setq *proj-source-stays*
		(loop for data in *proj-source-points*
		      collect (create-stay-constraint data :weak)))
	  (setq *proj-edit-scale-constraint*
	    (create-edit-constraint *proj-scale* :strong))
	  ))
  (format t "~%...adding stay and scale constraints...~%")
  (time (progn
	  (loop for cn in *proj-source-stays* do (add-constraint cn))
	  (loop for cn in *proj-scale-constraints* do (add-constraint cn))
	  ))
  (format t "~%...adding strong edit constraint to scale...~%")
  (time (add-constraint *proj-edit-scale-constraint*))
  (format t "~%...make plan...~%")
  (time (setq *proj-plan* (extract-plan-from-constraints
			   (list *proj-edit-scale-constraint*))))
  (format t "~%...execute plan...~%")
  (setq *proj-scale-value* (* 1.0 (+ 1.0 (random 10))))
  (setf (VAR-value *proj-scale*) *proj-scale-value*)
  (time (execute-plan *proj-plan*))
  (when (loop for data in *proj-source-points*
	      as proj in *proj-dest-points*
	      thereis (not (equal (VAR-value proj)
				  (+ (VAR-value *proj-offset*)
				     (* *proj-scale-value* (VAR-value data))))))
	(cerror "cont" "value not propagated correctly!"))
  (format t "~%...remove edit constraint...~%")
  (time (remove-constraint *proj-edit-scale-constraint*))
  )





