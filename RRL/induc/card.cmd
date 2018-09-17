;; This file contains RRL's input for the Gilbreath card trick.

; Hantao Zhang, July 17, 1992

; The following is quote from:

; Bob Boyer: A Mechanical Checking of a Theorem About a Card Trick


;;;; Here is Moore's statement of the trick:
;;;;
;;;;   ; Suppose you have a deck of cards of even length.  Suppose the cards
;;;;   ; alternate between red ones and black ones.	 Cut the deck into to two
;;;;   ; piles, a and b.  Shuffle a and b together.	 Then the following is
;;;;   ; true of the shuffled deck.	 If the bottom-most cards in a and b are
;;;;   ; of different color, then when the cards of the shuffled deck are
;;;;   ; taken from the top in adjacent pairs, each pair contains a card of
;;;;   ; each color.  On the other hand, if the bottom-most cards in a and b
;;;;   ; are the same color, the above pairing property holds after rotating
;;;;   ; the shuffled deck by one card, i.e., moving the bottom card to the
;;;;   ; top.
;;;;
;;;; The Gilbreath Trick: A Case Study in Axiomatization and Proof Development 
;;;; in the COQ Proof Assistant, Gerard Huet, Technical Report 1511, INRIA, 
;;;; September, 1991.
;;;;
;;;; M. Gardner, Mathematical Recreation Column, Scientific American, Aug. 1960.
;;;;
;;;; N. Gilbreath, Magnetic Colors, The Linking Ring, 38(5), 1959.


;; It takes 15 seconds to replay the following inputs, which consists
;; of 9 definitions and 23 lemmas, on a sparc 2 in AKCL (1.615).
;; The time to prepare this file is approximately 16 hours. 

init ;; initialize RRL

option prove e ;; select the cover set induction.

add ;; input function definitions.

;; there are two kind of cards: true = black and false = red.

;; the constructors for lists of cards. 
[ null : list]               
[ cons : card, list -> list] 

[ paired : bool, bool -> bool ]
;; paired(x, y) = true iff x and y are cards of opposite color.
paired(x, y) := (not(x) = y)

[ append : list, list -> list]
;; append two lists.
append(null, y) := y
append(cons(x, y), z) := cons(x, append(y, z)) 

[ rotate : list -> list ]
;; rotate the first element to the end of a list.
rotate(null) := null
rotate(cons(x, y)) := append(y, cons(x, null))

[ even : list -> bool ]
;; even(x) = true iff x is of even length.
even(null) := true
even(cons(x, null)) := false
even(cons(x1, cons(x2, y))) := even(y)

[ opposite : list, list -> bool ]
;; opposite(x, y) = true iff the first cards of x and y, respectively, 
;; are of opposite color.
opposite(null, y) := true
opposite(x, null) := true
opposite(cons(x1, y1), cons(x2, y2)) := paired(x1, x2)

[ pairedlist : list -> bool ]
;; pairedlist(x) = true iff x is a list of cards such that 
;; if we repeatedly take two cards from its top, the two cards
;; are found to be of opposite color.  
pairedlist(null) := true
pairedlist(cons(x, null)) := true
pairedlist(cons(x1, cons(x2, x))) := paired(x1, x2) and pairedlist(x)

[ alternate : list -> bool ]
; alternate(x) = true iff x is a list of cards whose colors alternate.
alternate(null) := true
alternate(cons(x1, null)) := true
alternate(cons(x1, cons(x2, x))) := paired(x1, x2) and alternate(cons(x2, x))

[ shuffle : list, list, list -> bool ]
;; shuffle(x, y, z) = true iff z is a merge of x and y.
shuffle(null, x, z) := (x = z)
shuffle(x, null, z) := (x = z)
shuffle(x, y, null) := (x = null) and (y = null)
shuffle(cons(x1, y1), cons(x2, y2), cons(x3, z)) :=
    ((x1 = x3) and shuffle(y1, cons(x2, y2), z)) or
    ((x2 = x3) and shuffle(cons(x1, y1), y2, z)) 
] ;; end of input.

;; Declare constructors for cards and lists.
operator
constructor
null cons
y ;; confirm that cons is a free-constructor

;; declare a precedence for making terminating rewrite rules.
operator precedence 
shuffle pairedlist opposite rotate alternate append even paired

makerule

prove
pairedlist(x) if alternate(x)

prove
not alternate(cons(x, y)) if not alternate(y)

prove
even(append(u, v)) == even(v) if even(u)

prove
opposite(x, cons(y, z)) if alternate(cons(y, x))

prove
opposite(cons(y, z), x) if alternate(cons(y, x))

add
;; the same trick used in Boyer's proof: 
;; the function `silly' defines an induction scheme.
[ silly : list, list, list -> bool ]
silly(null, y, z) := true
silly(x, null, z) := true
silly(x, y, null) := true
silly(x, y, cons(z1, null)) := true
silly(cons(x1, null), cons(y1, null), cons(z1, cons(z2, z))) := true
silly(cons(x1, null), cons(y1, cons(y2, y)), cons(z1, cons(z2, z))) :=
        silly(null, cons(y2, y), z) and silly(cons(x1, null), y, z)
silly(cons(x1, cons(x2, x)), cons(y1, null), cons(z1, cons(z2, z))) :=
        silly(cons(x2, x), null, z) and silly(x, cons(y1, null), z)
silly(cons(x1, cons(x2, x)), cons(y1, cons(y2, y)), cons(z1, cons(z2, z))) :=
        silly(cons(x1, cons(x2, x)), y, z) and 
        silly(x, cons(y1, cons(y2, y)), z) and 
        silly(cons(x2, x), cons(y2, y), z)
]
makerule

prove
not shuffle(u, v, w) if not(pairedlist(w)) and
          (opposite(u, v)) and alternate(u) and 
           alternate(v) and hint(induc(silly(u, v, w)))

prove
opposite(rotate(u), v) if not(opposite(u, v)) and alternate(u) and even(u)

prove
opposite(u, rotate(v)) if not(opposite(u, v)) and alternate(v) and even(v)

prove
not alternate(cons(x1, append(y, x))) if
          not alternate(cons(x1, x)) and (even(y)) 

prove
alternate(cons(x2, append(y, x))) == alternate(cons(x2, x)) if 
          (even(y)) and (alternate(cons(x2, y)))

prove
alternate(rotate(u)) if alternate(u) and even(u)

prove
shuffle(cons(x1, null), y, cons(x1, y)) 

prove
shuffle(x, cons(x1, null), cons(x1, x))

prove
shuffle(u, append(v, x), append(z, x)) if shuffle(u, v, z)

prove
shuffle(append(u, x), v, append(z, x)) if shuffle(u, v, z)

prove
not shuffle(u, v, w) if
      not shuffle(rotate(u), v, rotate(w)) and
      not shuffle(u, rotate(v), rotate(w)) 
;; the above is the second nontrivial lemma in Boyer's proof.

prove
not shuffle(u, v, w) if
     not(pairedlist(rotate(w))) and
     (opposite(rotate(u), v)) and alternate(rotate(u)) and alternate(v) and
     (opposite(u, rotate(v))) and alternate(rotate(v)) and alternate(u) 
n
y

prove
not shuffle(u, v, w) if
     not(pairedlist(rotate(w))) and  not(opposite(u, v)) and
     even(u) and alternate(u) and
     even(v) and alternate(v) 
n
y
;; the above two lemmas are "bridge lemmas", i.e., they
;; easily follow (by rewriting only) the second-non-trivial lemma.

prove
even(cons(x, y)) == not even(y)

prove
even(u) if alternate(append(u, v)) and not(opposite(u, v))

prove
alternate(u) if alternate(append(u, v))

prove
alternate(v) if alternate(append(u, v))

prove
cond(opposite(u, v), pairedlist(w), pairedlist(rotate(w))) if
    (x = append(u, v)) and alternate(x) and even(x) and shuffle(u, v, w)
y

list
