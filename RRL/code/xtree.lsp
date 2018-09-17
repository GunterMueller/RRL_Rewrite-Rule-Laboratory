(in-package 'user)

#|
===============================================================================

  File: x_tree.lsp

  Index:
    1. print-node (node)
    2. show-tree (node &optional (leader "")
		                 (addition "")
				 (arrow1 "")
				 (arrow2 ""))
    3. write-tree (root &aux next nodelist)
    4. write-node (node)
    5. print-node (node) ;; same as 1.
    6. cuttree (node)
    7. breadth-search (id ltree &aux result)
    8. search-tree (id tree &aux buffer result)
    9. show-tree-info (root &aux next nodelist)
   10. show-node (node)
   11. cursor_up ()
   12. cursor_down ( &optional offset &aux childlist)
   13. add_child (node label source seqno state status info )
   14. search_by_id  (id ltree &aux result)
   15. search_by_eqn (eqn ltree &aux result)

===============================================================================
|#

(defstruct (node (:print-function print-node))   ; structure def of a node
        label     ; id of the node 
        source    ; where the info comes from
        seqno     ; sequence number ( unique id )
	state     ; state of the eqn ( Nor Ind Gen )
        status    ; status of proving (True Fail Halt)
	info      ; contents of the node
	parent    ; pointer to its parent
	chdlst    ; list of chidren 
	)


(defvar $root (make-node))      ; root pointer of the proof tree
(defvar $leaf (make-node))      ; front leaf pointer
(defvar $peek (make-node))      ; tree pointer
(defvar $eqn-pool)              ; list of equations need to prove
(defvar $seq-no)                ; sequence number for each node
(defvar $xnode)                 ; template for new node

(setf (node-label $root) nil)
(setf $peek $root)
(setf $leaf $root)
(setf $eqn-pool nil)
(setf $seq-no   '1)

#|
(defun print-node (node)
  (cond ((endp (node-label node))
	     (princ "Eqn") (princ "#") (princ (node-seqno node))
        )
        (t  (princ "[")
            (dolist (l (butlast (node-label node))) (princ l) (princ "."))
            (princ  (first (last (node-label node)))) (princ "]")
            (princ "#") (princ (node-seqno node))
	)
  )	
)
|#

(defun show-tree (node &optional (leader "")
		                 (addition "")
				 (arrow1 "")
				 (arrow2 "")
                       &aux state status source)
  (setf state  (node-state  node))
  (setf status (node-status node))
  (setf source (node-source node))
  (if* (equal state 'gen) 
         (if* (string= arrow1 "*-") (setf arrow1 "*="
                                         arrow2 "=>") 
	                           (setf arrow1 "|="
                                         arrow2 "=>"))
         nil )
 (if* (> 50 (length leader)) then
  (if* (null status)
    (format t "~&~a~a~a~a~a" leader arrow1 state arrow2 node)
    (if* (equal status 'fail)
     (format t "~&~a~a~a~a~a(~a)" leader arrow1 state arrow2 node source)
     (format t "~&~a~a~a~a~a(~a)" leader arrow1 state arrow2 node status))
  )
  else
   (if* (> 70 (length leader)) then
	(format t "~&~a~a~a~a~a" leader arrow1 state arrow2 '" ..."))
 )
  (when  (node-chdlst node)
    (dolist  (node (butlast  (node-chdlst node) 1))
      (show-tree node
		 (concatenate 'string leader addition)
		 "|     "
                 "|-"
		      "->"))
    (show-tree (first (last (node-chdlst node)))
	       (concatenate 'string leader addition)
	       "      "
               "*-"
	            "->")))       




   
(defun write-tree (root &aux next nodelist)
#|
---------------------------------------------------------------------

  Parameters:
      root     --  the root of given subtree
      next     --  the node to visit
      nodelist --  thlist of nodes to visit

  Function:
      travel the given subtree with breadth-first strategy and print
      out contents of each node

  Return:
           . t

  Calling:
           write-node

---------------------------------------------------------------------
|#
  (setf nodelist nil)
  (setf next root)
  (sloop while t do
   (when (null next) (return t))
   (write-node next)
   (setf nodelist (append nodelist (node-chdlst next)))
   (setf next (first nodelist))
   (setf nodelist (rest nodelist))
  )
)


(defun write-node (node)
#|
---------------------------------------------------------------------

  Parameters:
       node -- the node to display

  Function:
      display the contents of the given node

  Return:
      the info of the give node
      
  Callees: 
         write-eqn,  print-node
     
---------------------------------------------------------------------
|#
  (print-node node)
  (princ "  ")
  (write-eqn (node-info node))
)



;------------------------------------------------------------------------------

(defun print-node (node)
  (cond ((endp (node-label node))
	     (princ "Eqn") (princ "#") (princ (node-seqno node))
        )
        (t  (princ "[")
            (dolist (l (butlast (node-label node))) (princ l) (princ "."))
            (princ  (first (last (node-label node)))) (princ "]")
            (princ "#") (princ (node-seqno node))
	)
  )	
)

(defun cuttree (node)
  (setf (node-chdlst node) nil)) 



(defun breadth-search (id ltree &aux result)
#|
---------------------------------------------------------------------

      id     : given label
      ltree   : the list of roots of given subtree
      result : return variable

     If id is found in subtree after breadth-first search then
           result = the node whose label is equal to id
     else
           result = (not find)

---------------------------------------------------------------------
|#
  (let ((current (first ltree))
	(next    (rest ltree))
       )
    (cond ((endp ltree)  (setf result '(not find)))
          ((equal id (node-label current))
	           (setf result current))
	  ((and (endp (node-chdlst current)) (endp next))
	           (setf result '(not find)))
          (t       (breadth-search id (append next (node-chdlst current))))
    )
  )
)





(defun search-tree (id tree &aux buffer result)
#|
---------------------------------------------------------------------

  Parameters:
      id     -- given label
      tree   -- the root of given subtree
      buffer -- storage for intermediate result
      result -- return variable

  Function:
      finding the deep-most node in given subtree whose label is
    equal to id.

  Return:
      . (not find)      if no match
      . the pointer of the found node

---------------------------------------------------------------------
|#
  (setf buffer (breadth-search id (list tree)))
  (setf result buffer)
  (sloop while t do
   (when (equal buffer '(not find)) (return result))
   (setf result buffer)
   (setf buffer (breadth-search id (node-chdlst buffer)))
  )
)
   
(defun show-tree-info (root &aux next nodelist)
#|
---------------------------------------------------------------------

  Parameters:
      root     --  the root of given subtree
      next     --  the node to visit
      nodelist --  thlist of nodes to visit

  Function:
      travel the given subtree with breadth-first strategy and print
      out contents of each node

  Return:
           . t

  Calling:
           show-node

---------------------------------------------------------------------
|#
  (setf nodelist nil)
  (setf next root)
  (sloop while t do
   (when (null next) (return t))
   (show-node next)
   (setf nodelist (append nodelist (node-chdlst next)))
   (setf next (first nodelist))
   (setf nodelist (rest nodelist))
  )
)


(defun show-node (node)
#|
---------------------------------------------------------------------

  Parameters:
       node -- the node to display

  Function:
      display the contents of the given node

  Return:
      the info of the give node
      
  Callees: 
         write-eqn,  print-node
     
---------------------------------------------------------------------
|#
  (print-node node)
  (princ "  ")
  (write-eqn (node-info node))
)



(defun cursor_up ()
  (setf $cursor (node-parent $cursor))
)

(defun cursor_down ( &optional offset &aux childlist)
  (setf childlist (rest (node-chdlst $cursor)))
  (setf $cursor (first (node-chdlst $cursor)))
  (sloop while t do
    (when (or (eq offset nil) (zerop (- offset 1)))
          (return nil))
    (setf $cursor (first childlist))
    (setf childlist (rest childlist))
    (setf offset (- offset 1))
  )
)




(defun add_child (node label source seqno state status info )
#|
---------------------------------------------------------------------

  Parameters: node -- the node to add new child in
              label,source,seqno,state,status,info -- initial value 
                                         of the new child

  Global Variable:  $xnode

  Function: create a new child-node, fill in it with given initial
            value and add it into the chdlst of given node

  Return:  new generated child-node

---------------------------------------------------------------------
|#
  (if* (and (equal label (node-label node)) (equal info (node-info node)))
    then  node
    else
          (setf $xnode (make-node))

          (setf (node-label  $xnode) label)
          (setf (node-source $xnode) source)
          (setf (node-seqno  $xnode) seqno)
          (setf (node-state  $xnode) state)
          (setf (node-status $xnode) status)
          (setf (node-info   $xnode) info)
          (setf (node-parent $xnode) node)
          (setf (node-chdlst $xnode) nil)

          (setf (node-chdlst node) (append (node-chdlst node) (list $xnode)))
	  $xnode
  )
)


; -- 10/02/90 --

(defun search_by_id  (id ltree &aux result)
#|
---------------------------------------------------------------------

      id      : the given seqno
      ltree   : the list of roots of given subtree
      result  : return variable

     If id is found in subtree after breadth-first search then
           result = the node  whose seqno is equal to id
     else
           result = (not find)

---------------------------------------------------------------------
|#
  (let ((current (first ltree))
	(next    (rest ltree))
       )
    (cond ((endp ltree)  (setf result '(not find)))
          ((equal id (node-seqno current))
	           (setf result  current))
	  ((and (endp (node-chdlst current)) (endp next))
	           (setf result '(not find)))
          (t       (search_by_id id (append next (node-chdlst current))))
    )
  )
)

; -- 10/09/90 --

(defun search_by_eqn (eqn ltree &aux result)
#|
---------------------------------------------------------------------

      eqn     : the given equation
      ltree   : the list of roots of given subtree
      result  : return variable

     If eqn is found in subtree after breadth-first search then
           result = the node  whose info is equal to eqn
     else
           result = (not find)

---------------------------------------------------------------------
|#
  (let ((current (first ltree))
	(next    (rest ltree))
       )
    (cond ((endp ltree)  (setf result '(not find)))
          ((equal eqn (node-info current))
	           (setf result  current))
	  ((and (endp (node-chdlst current)) (endp next))
	           (setf result '(not find)))
          (t       (search_by_eqn eqn (append next (node-chdlst current))))
    )
  )
)

