
add

app((e), x) == x
app(con(u, v), x) == con(u, app(v,x))

rev((e)) == (e)
rev(con(u,v)) == app(rev(v),con(u,(e)))

]

oper pre rev app con e

kb

