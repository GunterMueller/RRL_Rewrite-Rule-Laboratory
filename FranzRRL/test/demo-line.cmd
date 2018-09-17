init
option
prove
c
add
; For any two distinct points, there is a unique line through them.
on(z1, ln(z1, z2)) or (z1 = z2) or not point(z1) or not point(z2)
on(z2, ln(z1, z2)) or (z1 = z2) or not point(z1) or not point(z2)
line(ln(z1, z2)) or (z1 = z2) or not point(z1) or not point(z2)
not on(z1, y3) or (z1 = z2) or not on(z2, y3) or (y3 = y4) or not on(z1, y4) or  
  not on(z2, y4) or not point(z1) or not point(z2) or not line(y3) or not line(y4)
; For any line, there are at least two distinct points on the line.
on(pt1(y1), y1) or not line(y1) 
on(pt2(y1), y1) or not line(y1) 
point(pt1(y1)) or not line(y1) 
point(pt2(y1)) or not line(y1) 
not (pt1(y1) = pt2(y1)) or not line(y1)
; For any line, there is a point not on the line.
not on(pt3(y1), y1) or not line(y1)
point(pt3(y1)) or not line(y1) 
; There is a point on every line.
on(pt, y1) or not line(y1)
; There exists a line.
line(a)
; There is a point on every line.
point(pt)       
]
kb
p
p
p
p
n
