(in-package "RRL")

;; This file contains certain functions that are used to
;; output successful solutions.


; dumped get-all-vars and process-vars - siva.
(defun s-show-ans (node)
;; The function is called by SOLVE-IDFS to print out
;; solutions.
    (let  ((depth   (s-get-depth  node))
           (ans     (s-get-ans    node)))
       (cond ((> depth *prv-depth*)
                    (s-show-answer ans)
                    (format t "Found at Depth ~a. ~%" depth)
                    (terpri) t) 
             ( t  nil) ) ) )

(defun s-show-answer (unifier)
   (terpri)
   (do* ((lst   *list-of-vars*    (cdr lst))
         (var   (car lst)         (car lst))
         (bind  (assoc var unifier)
                (assoc var unifier) ))
       ((null lst)(terpri))
       (if bind
        (format t "   ~a  |--> ~a ~%" (car bind) (cdr bind))) ) )


(defun output-trace (lhs rhs op ans)
;; This function is called by RESTRUCTURE. The action is to print
;; some relevant information about the node that is being restru-
;; ctured, depending on the level of the debugging parameter.
    (cond  ((not (numberp *debug*)) nil)
           (t  (if (>= *debug* 0) 
                   (format t "Operator: ~a ~%" op))
               (if (>= *debug* 1)
		   (format t "Lhs: ~a ~%" (applysubst ans lhs)))
	       (if (>= *debug* 2)
		   (format t "Rhs: ~a ~%" (applysubst ans rhs))))))


(defun show-rules (rules)
	(cond ((null rules) (terpri))
	      (t (show-rule (car rules))
		 (show-rules (cdr rules)))))


(defun show-rule (rule)
	(princ " ")
	(print (get-rule-lhs rule))
	(princ "   --->   ")
	(print (get-rule-rhs rule))
	(terpri))

(defun stop-if-depth-too-large (depth)
;; This function is called when a certain *MAX-DEPTH* is reached.
;; At this stage the user is asked to continue / abort.
    (if (> depth *MAX-LIM*)
        (progn 
           (format t "~%Current depth is ~a .... " depth)
           (let  ((temp))
             (if (eq 'n (ask-choice temp '(y n) " Want to continue?"))
                 (throw '*solve* nil)
                 (progn (format t "~%Set new bound for MAXIMUM DEPTH : ")
                        (setq *MAX-LIM* (read)))))) ) )
