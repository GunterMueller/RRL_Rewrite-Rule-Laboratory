init
option
prove
c
add
iswolf (awolf) == true
isfox (fox) == true
isbird (bird) == true
issnail (snail) == true
isgrain (grain) == true
isplant (splant) == true
isplant (splant2) == true
isanimal(x) == true if iswolf(x) 
isanimal(x) == true if isfox(x)
isanimal(x) == true if isbird(x)
isanimal(x) == true if issnail(x)
isanimal(x) == true if iscaterpillar(x) 
isplant(x) == true if isgrain(x)
smaller (x, y) == true if issnail(x) and isbird (y)
smaller (x,y) == true if  isbird(x) and isfox (y)
smaller (x, y) == true if isfox(x) and iswolf(y)
eats (x, y) == false if iswolf(x) and isfox (y)
eats (x, y) == false if iswolf(x) and isgrain (y)
eats (x, y) == false if isbird(x) and issnail (y)
eats (x, y) == true if isbird(x) and iscaterpillar (y)
smaller (x, y) == true if iscaterpillar(x) and isbird (y)
eats (y, splant2) == true if iscaterpillar (y)
eats (y, splant) == true if issnail(y)
eats (x, y) == false if iswolf(x) and isgrain(x)
smaller(z, x) == false if isanimal(x) and isplant(y) and isanimal(z) and
                          isplant(w) and eats(z, w) and not(eats(x, y)) and not eats(x, z)
eats(x, y) == false if eats(y, z) and isanimal(x) and isanimal(y) and isgrain(z)
]
operator
precedence
smaller eats isanimal isplant iswolf isfox isbird issnail isgrain awolf bird snail splant grain 
kb

