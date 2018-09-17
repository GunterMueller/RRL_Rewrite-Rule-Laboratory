;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")

#-franz (in-package "USER")


;; ================================================
;; Output Functions
;; ================================================

#+franz
(declare (special l__2 l__3 l__ctr))

(defun display (&optional (disp-rules t) port)
  ; Prints a list of the equations and rules.  If DISP-RULES is nil
  ; then only the equations are displayed.
  (display-type-arity $operlist port)
  (if* $ac then (terpri port)
      (princ (uconcat "Associative & commutative operator set = "
		      (display-ops $ac)) port) (terpri port))
  (if* $commutative then (terpri port)
      (princ (uconcat "Commutative operator set = " (display-ops $commutative)) port)
      (terpri port))
  (if* (or $eqn-set $post-set $post-ass-set) then
      (princ "Equations:" port) (terpri port)
      (list-equations (append $eqn-set $post-set) port)
      (if* $post-ass-set 
	  (list-assertions $post-ass-set (length (append $eqn-set $post-set)) port))
      else 
      (princ "No equations in current system." port) (terpri port))
  (terpri port)
  (if* disp-rules then
      (if* $rule-set
	  then (princ "Rules:" port) (terpri port) (list-rules $rule-set port)
	  else (princ "No rules in current system." port) (terpri port))))

(defun writef-sys (&aux port)
  (user-selectq
    (quit "Quit without save anything. " nil)
    (equations-only 
      "Save only equations"
      (if* (setq port (open-write-file "eqn" t)) then
	  (write-eqns (append $eqn-set $post-set) port)
	  (if* $post-ass-set then (write-assertions $post-ass-set port))
	  (close port)
	  (princ "Equations written in the file.") (terpri)))
    (rules-only 
      "Save only rules. "
      (if* (setq port (open-write-file "eqn" t)) then
	  (write-rules $rule-set port) (close port)
	  (princ "Rules written in the file.") (terpri)))
    (all
      "Save both equations and rules. "
      (if* (setq port (open-write-file "eqn" t)) then
	  (write-eqns (append $eqn-set $post-set) port) (terpri port) 
	  (write-rules $rule-set port) 
	  (close port)
	  (princ "System written in the file.") (terpri)))
    (kb-status
      "Save KB statistics in a file with the suffix `.out'. "
      (if* (setq port (open-write-file "out" t)) then
	  (display t port)
	  (terpri port)
	  (display-kb-stat nil port)
	  (terpri port) 
	  (close port)))))

(defun open-write-file (&optional suffix no-detroy)
  ; Read in a file name and try to open it to write. 
  ; If the filename has no default suffix, then append SUFFIX
  ; to it. If the file exists, then open the file to append.
  (let (filename filename2 port)
    (if* (is-empty-line $in-port) then (princ "Type filename: "))
    (setq filename (read-atom 'end)
	  filename2 #+franz (if* (is-subsequence suffix filename)
			      then filename else (uconcat filename "." suffix))
	            #-franz (string-downcase (uconcat filename "." suffix)))
    (if* (or (not no-detroy) 
	    (not (my-probef filename2))
	    (ok-to-continue "Overwrite the old file ? ")) then 
	(cond
	  ((setq port (outfile filename2))
	   (princ (uconcat "    '" filename2 "' is open to write")))
	  (t (princ (uconcat "Error: Couldn't open file: " filename))))
	(terpri))
    port))

(defun list-rules (rset &optional port)
  (sloop for xa in rset do (write-rule xa port)))

(defun write-rules (rset &optional port)
  (sloop for xa in rset do (write-f-rule xa port)))

(defun list-equations (eqns &optional port)
  (sloop for eqn in eqns  for i from 1 do
    (princ (if* (< i 10) then (uconcat " " i ". ") else (uconcat i ". ")) port)
    (write-eqn eqn port)))

(defun write-eqns (eqns &optional port)
  ;  Writes out equations EQNS to port PORT.
  (sloop for eqn in eqns do (write-f-eqn eqn port)))

(defun write-f-rule (rule &optional port)
  ;  Writes out RULE to PORT.
  (setq l__2 nil l__3 nil l__ctr 0) 
  (write-term-simple (lhs rule) port)
  (princ " ---> " port)
  (write-f-rhs (rhs rule) (ctx rule) port)
  (terpri port))

(defun write-rule (rule &optional port)
  ; writes out RULE to PORT, precedes it with its rule number.
  (princ (uconcat (if* (< (ruleno rule) 10) then "  [" else " [")
		  (ruleno rule) "] ") port)
  (write-term (lhs rule) port)
  (princ " ---> " port)
  (write-rhs (rhs rule) (ctx rule) port)
  (setq rule (rule-source rule)) 
  (princ (uconcat "  [" (car rule) ", " (cadr rule) "]") port)
  (terpri port))

(defun write-goal-rule (rule &optional port)
  ; writes out RULE to PORT, precedes it with its rule number.
  (princ (uconcat (if* (< (ruleno rule) 10) then "  [" else " [")
		  (ruleno rule) "] ") port)
  (write-term (lhs rule) port)
  (princ " =\= " port)
  (write-rhs (rhs rule) (ctx rule) port)
  (setq rule (rule-source rule)) 
  (princ (uconcat "  [" (car rule) ", " (cadr rule) "]") port)
  (terpri port))

(defun write-f-eqn (eqn &optional port flag)
  ;  Writes out equation EQN to port PORT.
  (if* (null flag) then (setq l__2 nil l__3 nil l__ctr 0))
  (write-term-simple (lhs eqn) port)
  (if* (or (is-condi-eqn eqn) (not (is-assertion eqn))) then 
     (princ " == " port)
     (write-f-rhs (rhs eqn) (ctx eqn) port))
  (terpri port))

(defun write-eqn (eqn &optional port)
  ;  Writes out equation EQN to port PORT.
  (write-term (lhs eqn) port)
  (if* (or (is-condi-eqn eqn) (not (is-assertion eqn))) then 
     (princ " == " port)
     (write-rhs (rhs eqn) (ctx eqn) port))
  (setq eqn (eqn-source eqn)) 
  (princ (uconcat "  [" (car eqn) ", " (cadr eqn) "]") port)
  (terpri port))

(defun write-goal-eqn (eqn &optional port)
  ;  Writes out equation EQN to port PORT.
  (write-term (lhs eqn) port)
  (if* (or (is-condi-eqn eqn) (not (is-assertion eqn))) then 
     (princ " =\= " port)
     (write-rhs (rhs eqn) (ctx eqn) port))
  (setq eqn (eqn-source eqn)) 
  (princ (uconcat "  [" (car eqn) ", " (cadr eqn) "]") port)
  (terpri port))

(defun write-rhs (rhs ctx &optional port)
  (if* (truep rhs) then (princ 'true port) else (write-disjunctions rhs 2 port))
  (if* ctx then (princ "  if  " port)
      (if* (is-premise-set ctx) 
	  then (write-premises (cdr ctx) port)
	  else (write-disjunctions ctx 3 port))))

(defun write-f-rhs (rhs ctx &optional port)
  (if* (truep rhs) then (princ 'true port) else (write-term-simple rhs port))
  (if* ctx then (princ " if " port) 
      (if* (is-premise-set ctx) 
	  then (write-f-premises (cdr ctx) port)
	  else (write-term-simple ctx port))))

#| 
(defun write-cterm (ct &optional port)
  (write-term (t-cterm ct) port)
  (if* (c-cterm ct) then (princ " if " port)
			(write-disjunctions (c-cterm ct) 3 port)))

(defun write-f-cterm (ct &optional port)
  (setq l__2 nil l__3 nil l__ctr 0) 
  (write-term-simple (t-cterm ct) port)
  (if* (c-cterm ct) then (princ " if " port) (write-term-simple (c-cterm ct))))
|#

(defun list-assertions (asss num &optional port)
  (sloop for xa in asss for i from (1+ num) do 
        (princ (if* (< i 10) then (uconcat " " i ". ") else (uconcat i ". ")))
	(write-assertion (cdr xa) port)))

(defun write-assertions (asss &optional port)
  (sloop for xa in asss do 
	(setq l__2 nil l__3 nil l__ctr 0) 
	(write-term-simple (cddr xa) port) (terpri)))

(defun write-assertion (ass &optional port)
  (write-term (cdr ass) port)
  (princ (uconcat "  [" (caar ass) ", " (cadar ass) "]") port)
  (terpri port))

(defun write-term (term &optional port)
  (setq l__2 nil l__3 nil l__ctr 0) 
  (write-term-bool term port))

(defun write-term-bool (ct &optional port)
  (if* (variablep ct) then (write-variable ct port) else
  (caseq (op-of ct)
    (xor (princ "(" port) 
	 (write-term-bool (first-arg ct) port)
         (sloop for xa in (cdr (args-of ct)) do
	       (princ " xor " port) (write-term-bool xa port))
	 (princ ")" port))
    (and (write-term-simple (first-arg ct) port)
         (sloop for xa in (cdr (args-of ct)) do
            (princ " & " port) (write-term-simple xa port)))
    (t (write-term-simple ct port)))))

(defun write-term-simple (term &optional port &aux op)
  ; Recursive function used by write-term.
  (if* (variablep term) then (write-variable term port)
     elseif (and (infixp (setq op (op-of term))) (not (eq op 'eq))) then
     (if* (and $polynomial (eq op '+)) then
	 (setq term (mult-form (args-of term)))
	 (if* (> (cdar term) 1) (princ (cdar term) port))
	 (write-term-simple (caar term) port)
	 (sloop for xa in (cdr term) do
	   (princ (uconcat " " op " ") port)
	   (if* (> (cdr xa) 1) (princ (cdr xa) port))
	   (write-term-simple (car xa) port))
	 else
	 (princ "(" port)
	 (write-term-simple (first-arg term) port)
	 (sloop for xa in (cdr (args-of term)) do
	   (princ (uconcat " " op " ") port)
	   (write-term-simple xa port))
	 (princ ")" port))
     else 
     (princ op port)
     (caseq op 
       ((all exist) (princ " " port)
	(write-variable (first-arg term) port)
	(princ " (" port)
	(write-term-simple (second-arg term) port)
	(princ ")" port))
       (t (if* (args-of term) then
	      (princ "(" port)
	      (write-term-simple (first-arg term) port)
	      (sloop for xa in (cdr (args-of term)) do
		(princ ", " port) (write-term-simple xa port))
	      (princ ")" port))))))

(defun write-variable (var port &aux l1)
  (if* (assoc var l__2) then (princ (cdr (assoc var l__2)) port)
    elseif (member0 (get_pname var) l__3)
    then (setq l1 (uconcat var (setq l__ctr (1+ l__ctr))))
	 (push l1 l__3)
	 (push (cons var l1) l__2)
	 (princ l1 port)
    else (princ var port)
	 (push (cons var (get_pname var)) l__2)
	 (push (get_pname var) l__3)))
  
(defun write-disjunctions (ct spn &optional port)
  (if* (variablep ct) then (write-variable ct port)
    elseif (and (eq (op-of ct) 'xor) (cdddr ct)) 
    then (terpri port) (princ "       " port)
	 (sloop for xx from 1 to spn do (princ "        " port))
	 (princ "(" port)
         (write-term-bool (car (args-of ct)) port)
         (sloop for xa in (cdr (args-of ct)) do
            (princ " xor " port) (terpri port)
 	    (sloop for xx from 0 until (eq xx spn) do (princ "        " port))
	    (write-term-bool xa port))
	 (princ ")" port)
    else (write-term-bool ct port)))

(defun write-premises (pres &optional port)
  (if* (cdr pres) then
    (terpri port) (princ "        " port)
    (princ "{ " port)
    (write-one-pre (car pres) port)
    (sloop for xa in (cdr pres) do
      (princ "," port) 
      (terpri port)
      (princ "          " port)
      (write-one-pre xa port))
    else
    (princ " { " port) 
    (write-one-pre (car pres) port))
    (princ " } " port))

(defun write-f-premises (pres &optional port)
  (if* (cdr pres) then
    (terpri port)
    (princ "          (" port)
    (write-one-pre (car pres) port)
    (sloop for xa in (cdr pres) do
      (princ ") and " port) 
      (terpri port)
      (princ "          (" port)
      (write-one-pre xa port))
    (princ ")" port)
    else
    (write-one-pre (car pres) port)))

(defun write-one-pre (pre &optional port first)
  (if* first then (setq l__2 nil l__3 nil l__ctr 0))
  (if* (equal (cadr pre) '(false))
      then 
      (princ "not(" port) (write-term-bool (car pre) port)
      (princ ")" port)
      else
      (write-term-bool (car pre) port)
      (if* (cadr pre) then 
	(if* (variablep (car pre)) 
	    then (princ " = " port)
	    else (princ " equ " port)) 
	(write-term-bool (cadr pre) port))))

(defun print-atoms (list separator)
  (if* list then
    (let ((l1 (uconcat "(" (car list))))
	(sloop for xa in (cdr list) do (setq l1 (uconcat l1 separator xa)))
	(uconcat l1 ") " ))
   else ""))

(defun print-head (choices)
   (if* (is-empty-line $in-port) then
     (let ((num 0))
        (princ "Type ")
        (sloop for xa in (cdr choices) do 
   	   (if* (> (setq num (+ num 2 (pntlen xa))) 74) then
 	       (terpri) (princ "     ") (setq num (+ 2 (pntlen xa))))
	   (princ xa) (princ ", "))
        (if* (> (+ num (pntlen (car choices))) 70) then
           (terpri) (princ "     "))
        (princ (car choices)) (princ " --> "))))


(defun write-detail-rule (rul port &aux source)
  (setq source (rule-source rul))
  (caseq (first source)
    (user (princ (uconcat "Input #" (second source) ",") port))
    (detach (princ (uconcat "Rule [" (second source) 
			    "] superposed with the detachment rule,") port))
    (idem (princ (uconcat "Rule [" (second source) "] superposed itself,") port))
    (insta (princ (uconcat "Instanciating Rule [" (second source) "],") port))
    (distr (princ (uconcat "Superposing X*(Y+Z) ---> (X*Y)+(X*Z) into Rule ["
			   (second source) "], ") port))
    (deleted 
     (princ (uconcat "Rule [" (second source) "],") port)
     (if* (neq (third source) 'ac-op) then
       (princ (uconcat " deleted by Rule [" (third source) "],") port)
       (pop source)))
    (divided (princ (uconcat (rule-name (second source))
			     " was divided by disgreement of arguements,") port))
    (t (princ (uconcat (rule-name (first source) 
				  (memq (third source) '(ext1 ext2)))
		       " superposed into "
		       (if* (eq (first source) (second source))
			   "itself"
			   (rule-name (second source) (eq (third source) 'ext2)))
		       ",")
	      port)))

  ;(setq source (rem-dups (cddr source)))
  (setq source (cddr source))
  ; >>>>> 1/30/89
  (caseq (car source) 
	 ((ext1 ext2) (pop source))
	 (ac-op 
	  (princ " reformulated by the commutativity law obtained by " port)
	  (terpri port)
	  (if* (eq (nth 1 source) 'deleted) then
	      (princ (uconcat "    reducing Rule [" (nth 2 source) 
			      "] using Rule ["
			      (nth 3 source) "],") port)
	      (setq source (cddddr source))
	      else
	      (princ (uconcat "    superposing Rule [" (nth 1 source)
			      "] into Rule [" 
			      (nth 2 source) "],") port)
	      (setq source (cdddr source))))
	 (t nil))

  (if* source then
      (if* (cdr source) then
	  (princ " reduced by Rules " port)
	  (sloop for xa in (butlast (reverse source))
		do (princ (uconcat "[" xa "], ") port))
	  (princ "and " port)
	  else (princ " reduced by Rule " port))
      (princ (uconcat "[" (car source) "],") port))

  (princ " produces:" port)
  (terpri port) (princ "    " port) 
  (princ (uconcat (if* (< (ruleno rul) 10) then "  [" else " [")
		  (ruleno rul) "] ") port)
  (write-f-rule rul port))

(defun rule-name (num &optional ext) 
  (if* ext 
      then (uconcat "Extension of Rule [" num "]") 
      else (uconcat "Rule [" num "]")))

(defun write-sigma (sigma &optional flag)
  (if* flag (setq l__2 nil l__3 nil l__ctr 0))
  (write-variable (caar sigma) nil)
  (princ "|")
  (write-term-simple (cdar sigma))
  (sloop for xa in (cdr sigma) do 
    (princ ", ")
    (write-variable (car xa) nil)
    (princ "|")
    (write-term-simple (cdr xa))))

;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-

;#+franz (include "datamacs.l")
;#-franz (in-package "USER")

; put all help type things here to avoid mess in other files
; like top-level, order, parser etc.

(defun help-file (string-list)
  ;  Displays string-list and prompts for more whenever encountering
  ; a \m in the file.  If the user hits [return] or [space][return]
  ; then the display continues; otherwise, returns.  Returns NIL.
  ; >>>>>> 1/30/89
  (clean-line nil)
  (sloop for line = 0 then (1+ line)
	as xa in string-list do
    (princ xa) (terpri)
    (if* (= line 20) then
	(princ "---- More [Type q (quit)  return (more)] ----")
	(caseq #+franz (my-tyi nil)
               #-franz (read-char nil nil)
	  (#+franz (#\newline #\return)
	   #-franz #\newline (setq line 0))
	  (#\space (setq line 0))
	  (t (return nil)))
	(terpri))))

; makes some code easier. this is for short messages.
(defun show-message (str-list) 
   (sloop for xa in str-list do (princ xa) (terpri)))

(setq $helpfile '(
"Currently you can do the following:"
""
"  Add     - Input equations from the terminal."
"  Akb     - Run the automatic Knuth-Bendix completion procedure."
"  Auto    - Automatically execute a sequence of commands in a cmd file."
"  Break   - Talk to Lisp directly."
"  Clean   - Clean the history stack to save space."
"  Delete  - Delete a list of equations or rules of RRL."
"  Grammer - Display the input grammer of RRL."
"  History - Put a copy of the current system into the history stack."
"  Init    - Initialize RRL."
"  Kb      - Run the Knuth-Bendix completion procedure."
"  List    - List equations and rules in current system."
"  Load    - Load a system saved in a file by the save command."
"  Log     - Registry all the next commands in a file (to be used by auto)."
"  Makerule- Orient equations into rewrite rules without superposition."
"  Narrow  - Solving an equation by narrowing."
"  Norm    - Using different strategies to normalize a term."
"  Option  - Set RRL flags and parameters."
"  Operator- Set properties of operators (precedence, constructors, etc.)."
; "  Order   - Prove the termination of RRL."
"  Prove   - Prove an equation by rewriting or by induction."
"  Quit    - Quit RRL."
"  Read    - Input equations from a file."
"  Refute  - Read a set of equations and negate the last one for refutation."
"  Save    - Save the current status of RRL into a file."
"  Stats   - List the current state of RRL."
"  Suffice - Test sufficient completeness."
"  Undo    - Undo RRL to the last user's interaction."
"  Unlog   - Stop registrying commands into a file."
"  Write   - Write equations and/or rules to a file."
"  Help    - Print this message."
""
"Note: You do not need to type whole command, a substring will suffice except"
"      that the first letter must be given. If what you type matches more than"
"      one command, the first one is chosen. For example, when you give 'o' or"
"      'or', RRL takes it for 'operator'. When you give 'od', RRL takes it for"
"      'order'. Arguments to commands may be typed on the same line."
"      There is no distinction between uppercase and lowercase characters."
;"	  Ex: d e 1 for delete equation 1 "
;"              p x==f(x) for prove x==f(x)."
))

(setq  $orderhelp 
; >>>>>>>> 1/7/89
'(
"  Abort     - Quit to the top of RRL."
"  Cyclerule - Make it as a permutative rule. "
"  Display   - Display equivalence, precedence, and status of operators. "
"  Drop      - Throw it away."
"  Equiv     - Make two operators equivalent. "
"  LR        - Hand orient equation left-to-right. "
"  MakeEq    - Make a rule as (lhs = rhs) ---> true ."
"  Operator  - Introduce new operator. "
"  Postpone  - Postpone orienting this equation."
"  Quit      - Interrupt and go to top level. "
"  RL        - Orient equation right-to-left. "
"  Status    - Set lexicographic status of an operator. "
"  NoReduc   - Use it not for reduction but for superposition only."
"  Twoway    - Make it orientable in two directions."
"  Undo      - Undo previous operation. "
"  Help      - Print this message."
""
))



(setq $grammar
  ; Put a description of the new grammar on the screen.
 '(
   "                      RRL'S    INPUT    SYNTAX "
   " "
   " <arity> ::= [<function> : <type>, <type>, ..., <type> -> <type>]"
   "              |  [<type> < <type>]"
   " <type> ::= Any sequence of alphanumeric characters"
   " <equation> ::= <assertion> == <rightside> |  <assertion> := <rightside>"
   "                | <assertion> ---> <rightside> | <formula>"
   " <rightside> ::= <assertion> | <assertion> if <assertion>"
   " <formula> ::= all <varlist> <formula> | exist <varlist> <formula>"
   "              | (<formula> <connective> <formula>) | not(<formula>) "
   "              | <assertion>"
   " <assertion> ::= (<assertion> <connective> <assertion>) | not(<assertion>)"
   "              | true | false | <atom>"
   " <connective> ::= and | or | xor | -> | equ "
   " <atom> ::= <predicate> <term-args>"
   " <predicate> ::= <function> | = | eq | cond"
   " <term> ::= <item> | <item> <infix-operator> <term>"
   " <item> ::= <variable> | <constant> | <function> <term-args> |(<term>)"
   " <term-args> ::= <nothing> | ( <term> <comma-args> )"
   " <comma-args> ::= <nothing> | , <term> <comma-args>"
   " <varlist> ::= ( <variable> <comma-varlist> ) | <variable>"
   " <comma-varlist> ::= <nothing> | , <variable> <comma-varlist>"
   " <infix-operator> ::= <function>"
   " <constant> ::= A number | <function>"
   " <function> ::= A letter in [a .. t] or in [A .. Z] followed by a sequence"
   "                of alphanumeric  characters or a word of"
   "                {+ - & ^ $ # @ ! | : . =}, except --->, ==, :=, if"
   " <variable> ::= A letter in [u .. z] followed by a sequence of "
   "                alphanumeric characters"
   " <nothing> ::= "
   " "
   " No distinctions are made between lowcase and upcase characters."
   " Formulas are any first-order logic formulas. "
   " Assertions are quantifier-free formulas. "
   " Terms are built from variables and operators."
   " Numbers can only be used as constants."
   " All functions must be used with the same number of arguments."
   " All free variables are considered as universally quantified variables."
   " "
   " Pre-defined precedence: "
   "  {<function>} > {not} > {and} > {->} > {all, exists} > {equ} > {or, xor}"
   " "
   " Note that all infix binary operators associate to the left if no "
   " parentheses or no precedence are given."
   " "
   ))

(setq $order-help '(
         "  Add-op   - Add new operator." 
         "  Give-stat - Gives statistics." 
	 "  LR       - Hand orient equation left-to-right." 
	 "  RL       - Hand orient equation right-to-left." 
	 "  Postpone - Postpone orienting this equation for now."
	 "  Quit     - Interrupt and go to top level." 
	 "  Undo     - Undo previous operation." ))
