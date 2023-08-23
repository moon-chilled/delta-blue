;;;-*- Package: :Delta-Blue; Syntax: Common-Lisp; Mode: Lisp -*-; 

;; This file implements the Delta Blue incremental constraint satisfaction
;; system using a constraint hierarchy with a local-predicate-better
;; comparator.  This code was translated directly from the pseudo-code in
;; the appendix to UW CS TR 91-08-12 ``Using Constraints for User Interface
;; Construction'' by John Maloney, using similar function and variable
;; names.  Refer to the pseudocode for detailed comments.  This file
;; contains comments where the code is changed significantly from the
;; pseudocode.

(eval-when (eval compile load)
  #+allegro-v4.0
  (setf excl::*cltl1-in-package-compatibility-p* t)
  #+allegro-v4.0
  (setf comp:*cltl1-compile-file-toplevel-compatibility-p* t)
  )

(in-package :Delta-Blue :nicknames '(:DBlue) :use '(Lisp))

#+allegro-v4.0 (cltl1:require :loop)
#-allegro-v4.0 (require :loop)

(export '(
          ;; structure constructors
          create-variable
          create-constraint
          create-method
	  ;; structure slot accessors
	  VAR-value
	  CN-selected-method
	  CN-variables
          ;; delta-blue entry points
          add-constraint
          remove-constraint
          extract-plan-from-variables
          extract-plan-from-constraints
	  execute-plan
          ))

;; numeric strength stuff

(defvar *strength-list*
  (list :required :strong :medium :weak :weakest))

(defvar *required-strength-num* (position :required *strength-list*))
(defvar *weakest-strength-num* (position :weakest *strength-list*))

(defun strength-to-num (strength)
  (if (member strength *strength-list*)
      (position strength *strength-list*)
    (error "bad strength keyword: ~S" strength)))

(defun num-to-strength (num)
  (nth num *strength-list*))

(defmacro weaker (s1 s2) `(> ,s1 ,s2))

;; Delta-Blue structure definitions

;; Constraint Representation:
;;   
;;   Field         | Type      | Description
;; ----------------+-----------+--------------------------------------------
;; variables       | Set of    | The variables that this constraint references.
;;                 | Variables |
;; strength        | Strength  | This constraint's level in the constraint
;;                 |           |  hierarchy.
;; input-flag      | Boolean   | True iff this is an input constraint.
;;                 |           | or depends on the external world.
;; methods         | Set of    | The potential methods for satisfying this
;;                 | Methods   | constraint.
;; selected-method | Method    | The method used to satisfy this constraint
;;                 |           | :none if the constraint is not satisfied.
;;		   |	       | Should only be manipulated by DeltaBlue.

(defstruct (Constraint
	    (:conc-name "CN-")
	    (:print-function (lambda (cn str lvl)
			       (declare (ignore lvl))
			       (format str "{cn-~Dst-~Dvar-~Dmt}"
				       (CN-strength cn)
				       (length (CN-variables cn))
				       (length (CN-methods cn)))))
	    )
  (variables       nil)
  (strength        0)
  (input-flag      nil)
  (methods         nil)
  (selected-method nil)
  )

(defun create-constraint (&key (variables nil)
			       (strength :required)
			       (input-flag nil)
			       (methods nil)
			       (selected-method nil))
  (make-constraint :variables variables
		   :strength (strength-to-num strength)
		   :input-flag input-flag
		   :methods methods
		   :selected-method selected-method))

;; Methods:
;;   A method represents one possible procedure for satisfying a constraint.
;;   Fields of a method representation are initialized at the constraint
;;   creation time and never modified.
;;
;;   Field        | Type      | Description
;;   -------------+-----------+--------------------------------------------
;;   code         | Procedure | The procedure to be called to execute this
;;                |           | method.
;;   output-index | Integer   | Index in constraint's variable list of
;;                |           | the  output variable of this method.

(defstruct (Method
	    (:conc-name "MT-")
	    (:print-function (lambda (mt str lvl)
			       (declare (ignore lvl mt))
			       (format str "{mt}")))
	    )
  (code         #'null)
  (output-index 0)
  )

(defun create-method (&key (code #'null)
			   (output-index 0))
  (make-method :code code
	       :output-index output-index))

;; Variables:
;;
;;   Field        | Type        | Description
;;  --------------+-------------+--------------------------------------------
;;  value         | anything    | The current value of this variable.
;;  constraints   | Set of      | All the constraints that reference this
;;                | Constraints | variable.
;;  determined-by | Constraint  | The constraint that determines this
;;                |             | variable's value.
;;  walk-strength | Strength    | The walkabout strength of this variable.
;;  mark          | Integer     | This variable's mark value.
;;  stay          | Boolean     | True if this variable is a constant at
;;                |             | planning time.

(defstruct (Variable
	    (:conc-name "VAR-")
	    (:print-function (lambda (var str lvl)
			       (declare (ignore lvl))
			       (format str "{var-~Sval}"
				       (VAR-value var))))
	    )
  (value         nil)
  (constraints   nil)
  (determined-by :none)
  (walk-strength 0)
  (mark          0)
  (stay          t)
  )

(defun create-variable (&key (value nil)
			     (constraints nil)
			     (determined-by :none)
			     (walk-strength :weakest)
			     (mark 0)
			     (stay t))
  (make-variable :value value
		 :constraints constraints
		 :determined-by determined-by
		 :walk-strength (strength-to-num walk-strength)
		 :mark mark
		 :stay stay))

;; macros (mostly for speed)

(defmacro method-output-var (c m)
  `(nth (MT-output-index ,m)
	(CN-variables ,c)))

(defmacro selected-method-output-var (c)
  (let ((cn-var (gentemp)))
    `(let ((,cn-var ,c))
       (method-output-var ,cn-var (CN-selected-method ,cn-var)))))

(defmacro do-consuming-constraints ((constraint-var var-form) . body)
  (let ((var-var (gentemp))
	(var-determined-by-var (gentemp)))
    `(let* ((,var-var ,var-form)
	    (,var-determined-by-var (VAR-determined-by ,var-var)))
       (loop for ,constraint-var in (VAR-constraints ,var-form)
	when (and (not (eq ,constraint-var ,var-determined-by-var))
		  (enforced ,constraint-var))		  
	do (progn ,@body)))
    ))

(defmacro do-inputs ((var-var constraint-form) . body)
  (let ((constraint-var (gentemp))
	(output-var-var (gentemp)))
    `(let* ((,constraint-var ,constraint-form)
	    (,output-var-var (selected-method-output-var ,constraint-var)))
       (loop for ,var-var in (CN-variables ,constraint-var)
	when (not (eq ,var-var ,output-var-var))
	do (progn ,@body)))
    ))

(defmacro inputs-always ((var-var constraint-form) . body)
  (let ((constraint-var (gentemp))
	(output-var-var (gentemp)))
    `(let* ((,constraint-var ,constraint-form)
	    (,output-var-var (selected-method-output-var ,constraint-var)))
       (loop for ,var-var in (CN-variables ,constraint-var)
	when (not (eq ,var-var ,output-var-var))
	always (progn ,@body)))
    ))

(defmacro enforced (c)
  `(not (eq :none (CN-selected-method ,c))))

;; Delta-Blue Entry Points

(defun add-constraint (c)
  (setf (CN-selected-method c) :none)
  (loop for v in (CN-variables c) do
	(push c (VAR-constraints v)))
  (incremental-add c)
  )

(defun incremental-add (c)
  (let* ((mark (new-mark))
         (retracted (enforce c mark)))
    (loop while (not (eq retracted :none)) do
          (setf retracted (enforce retracted mark)))
    ))

(defun select-method (c mark)
  (let ((best-out-strength (CN-strength c))
	(best-out-method :none))
    (loop for m in (CN-methods c) do
          (let* ((out-var (method-output-var c m))
                 (out-mark (VAR-mark out-var))
                 (out-strength (VAR-walk-strength out-var)))
            (when (and (not (= mark out-mark))
                       (weaker out-strength best-out-strength))
              (setf best-out-method m)
              (setf best-out-strength out-strength))
            ))
    (setf (CN-selected-method c) best-out-method)
    ))

(defun enforce (c mark)
  (select-method c mark)
  (cond ((enforced c)
         (let* ((output-var (selected-method-output-var c))
		(retracted (VAR-determined-by output-var)))
	   (do-inputs (v c)
		      (setf (VAR-mark v) mark))
	   (when (not (eq retracted :none))
             (setf (CN-selected-method retracted) :none))
           (setf (VAR-determined-by output-var) c)
           (cond ((not (add-propagate c mark))
                  (delta-blue-error "Cycle encountered")
                  :none)
                 (t
                  (setf (VAR-mark
			 ;; don't use output-var in case
			 ;; call to add-propagate may have
			 ;; changed c's selected method
                         (selected-method-output-var c))
                        mark)
                  retracted))
           ))
        (t
         (when (eq *required-strength-num* (CN-strength c))
           (delta-blue-error "Failed to enforce a required constraint"))
         :none)
        ))

(defun add-propagate (c mark)
  (let ((todo (list c)))
    (loop (when (null todo)
	    (return t))
          (let* ((d (pop todo))
		 (d-output-var (selected-method-output-var d)))
            (when (= mark (VAR-mark d-output-var))
              (incremental-remove c)
              (return nil)
              )
            (recalculate d d-output-var)
	    (do-consuming-constraints (consumer d-output-var)
				      (push consumer todo))
            )
          )))

(defun remove-constraint (c)
  (when (enforced c)
    (incremental-remove c))
  (loop for v in (CN-variables c) do
        (setf (VAR-constraints v)
              (remove c (VAR-constraints v))))
  )

(defun incremental-remove (c)
  (let ((out (selected-method-output-var c))
        unenforced)
    (setf (CN-selected-method c) :none)
    (loop for v in (CN-variables c) do
          (setf (VAR-constraints v)
                (remove c (VAR-constraints v))))
    (setf unenforced (remove-propagate-from out))
    (setf unenforced (sort unenforced
                           #'(lambda (c1 c2)
                               (weaker (CN-strength c2)
                                       (CN-strength c1)))))
    (loop for d in unenforced do
          (incremental-add d))
    ))

(defun remove-propagate-from (out)
  (let ((unenforced nil)
	(todo (list out)))
    (setf (VAR-determined-by out) :none)
    (setf (VAR-walk-strength out) *weakest-strength-num*)
    (setf (VAR-stay out) t)
    (loop while (not (null todo)) do
      (let ((v (pop todo)))
	(loop for c in (VAR-constraints v)
	 when (not (enforced c))
	 do (push c unenforced))
	(do-consuming-constraints
	 (c v)
	 (let ((output-var (selected-method-output-var c)))
	   (recalculate c output-var)
	   (push output-var todo))
	)))
    unenforced))

;; plan extraction

(defun extract-plan-from-variables (variables)
  (let ((sources nil))
    (loop for v in variables do
	  (loop for c in (VAR-constraints v)
		when (and (CN-input-flag c)
			  (enforced c))
		do (push c sources)))
    (make-plan sources)))

(defun extract-plan-from-constraints (constraints)
  (let ((sources nil))
    (loop for c in constraints
	  when (and (CN-input-flag c)
		    (enforced c))
	  do (push c sources))
    (make-plan sources)))

(defun make-plan (sources)
  (let ((plan nil)
        (mark (new-mark))
        (hot sources))
    (loop while (not (null hot)) do
          (let* ((c (pop hot))
                 (v (selected-method-output-var c)))
            (when (and (not (= mark (VAR-mark v)))
		       (inputs-always (v c)
				      (or (VAR-stay v)
					  (= mark (VAR-mark v)))))
              ;; add c to beginning of plan
              ;; (will reverse plan before returning)
              (push c plan)
              (setf (VAR-mark v) mark)
	      (do-consuming-constraints (c v)
					(push c hot))
              )))
    (nreverse plan)))

;; utilities

;; recalculate takes the constraint to recalculate
;; AND the output variable of that constraint
;; (to avoid some calls to selected-method-output-var)
(defun recalculate (c v)
  (setf (VAR-walk-strength v) (output-walk-strength c))
  (setf (VAR-stay v) (constant-output c))
  (when (VAR-stay v)
	(setf (VAR-value v) (execute-selected-method c)))
  )

(defun output-walk-strength (c)
  (let ((min-strength (CN-strength c))
	(selected-method-output-var (selected-method-output-var c)))
    (loop for m in (CN-methods c) do
	  (let ((output-var (method-output-var c m)))
	    (when (not (eq output-var selected-method-output-var))
		  (let ((output-walk-strength (VAR-walk-strength output-var)))
		    (when (weaker output-walk-strength min-strength)
			  (setf min-strength output-walk-strength))))
	    ))
    min-strength))

(defun constant-output (c)
  (not (or (CN-input-flag c)
	   (not (inputs-always (v c)
			       (VAR-stay v))))))

(defvar *mark-counter* 0)

(defun new-mark ()
  (incf *mark-counter* 1)
  *mark-counter*)

;; other functions not explicitly defined in the pseudo-code

(defun execute-selected-method (c)
  (funcall (MT-code (CN-selected-method c)) c))

(defun execute-plan (plan)
  ;; a plan is just a list of constraints, to be executed in order
  (loop for cn in plan do (setf (VAR-value (selected-method-output-var cn))
			    (execute-selected-method cn))))

;; delta-blue-error is called if delta-blue detects a cycle,
;; or is unable to enforce a required constraint
(defun delta-blue-error (error-string)
  (cerror "cont" error-string))


