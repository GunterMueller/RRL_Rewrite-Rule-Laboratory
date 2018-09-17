;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-

#+franz (include "datamacs.l")

#-franz (in-package "RRL")

; put all help type things here to avoid mess in other files
; like top-level, order, parser etc.

(defun help-file (string-list)
  ;  Displays string-list and prompts for more whenever encountering
  ; a \m in the file.  If the user hits [return] or [space][return]
  ; then the display continues; otherwise, returns.  Returns NIL.
  ; >>>>>> 1/30/89
  (clean-line nil)
  (loop for line = 0 then (1+ line)
	as xa in string-list do
    (princ xa) (terpri)
    (if (= line 20) then
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
   (loop for xa in str-list do (princ xa) (terpri)))

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
