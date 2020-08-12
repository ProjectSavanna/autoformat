signature FOO = sig
    structure First : FIRST
and Second : SECOND = Integer eqtype foo = int type t and 'a u
    and ('b,'c) foo = ('c,'b) Either.either

    val x : 'a list * int

    and y : int * ('a,string) foo * unit
    val z : (int list)  option*string

    datatype foo = Foo | Bar of int | Baz of string | StuffAndThings of int * string * bool
		and ('a,'b) either = Left of 'a | Right of 'a * 'b

  datatype bar = datatype option
    exception Foo and Bar
    of int
    sharing Stuff = Things = Bar

  sharing type t1 = t2 = Int.int = t3


   end
    where
    type
     t = int
and type ('a,'b) First.Bar.Baz.u = Either.either
