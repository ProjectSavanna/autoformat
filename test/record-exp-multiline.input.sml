val _ = {a= 1, b = 2, c = let in 3 end, d = 4}

val {y=result,...} = {x = "a", y=let val x = 3 in x+x end,z = () }
