functor AddMeta (type meta) (F : FUNCTOR) :> FUNCTOR where type 'a t = { meta : meta, data : 'a F.t } =
  struct
    type 'a t = { meta : meta, data : 'a F.t }

    val map = fn f =>
      fn { meta = meta, data = data } => { meta = meta, data = F.map f data }
  end

functor AddMeta2 (type meta) (F : FUNCTOR2) :> FUNCTOR2 where type ('a1, 'a2) t = { meta : meta, data : ('a1, 'a2) F.t } =
  struct
    type ('a1, 'a2) t = { meta : meta, data : ('a1, 'a2) F.t }

    val map = fn f =>
      fn { meta = meta, data = data } => { meta = meta, data = F.map f data }
  end

type meta = {
  comment : string option
}

functor ParseTree (Template : FUNCTOR) =
  Recursive (AddMeta (type meta = meta) (Template))

functor ParseTree2 (
  structure Template1 : FUNCTOR2
  structure Template2 : FUNCTOR2
) =
  Recursive2 (
    structure Template1 = AddMeta2 (type meta = meta) (Template1)
    structure Template2 = AddMeta2 (type meta = meta) (Template2)
  )

structure VId =
  struct
    type t = string
  end
and TyVar =
  struct
    type t = string
  end
and TyCon =
  struct
    type t = string
  end
and Lab =
  struct
    type t = string
  end
and StrId =
  struct
    type t = string
  end

functor Long (Ident : sig type t end) =
  struct
    datatype 'long t
      = Ident of Ident.t
      | Module of StrId.t * 'long

    fun map f =
      fn Ident id             => Ident id
       | Module (strid, long) => Module (strid, f long)
  end

structure LongVId   = Long (VId)
      and LongTyCon = Long (TyCon)
      and LongStrId = Long (StrId)

structure LongVId'   = ParseTree (LongVId)
      and LongTyCon' = ParseTree (LongTyCon)
      and LongStrId' = ParseTree (LongStrId)

type 'a seq = 'a list
type 'a seq1 = 'a * 'a seq
val map1 = fn f => fn (x1, xs) => (f x1, List.map f xs)
type 'a seq2 = 'a * 'a * 'a seq
val map2 = fn f => fn (x1, x2, xs) => (f x1, f x2, List.map f xs)

structure Ty =
  struct
    datatype 'ty t
      = Var of TyVar.t
      | Cons of 'ty seq * LongTyCon'.t
      | Record of (Lab.t * 'ty) list
      | Tuple of 'ty seq2
      | Arrow of { dom : 'ty, cod : 'ty }

    fun map f =
      fn Var tyvar                      => Var tyvar
       | Cons (tyseq, longtycon)        => Cons (List.map f tyseq, longtycon)
       | Record tyrows                  => Record (List.map (fn (lab, ty) => (lab, f ty)) tyrows)
       | Tuple tys                      => Tuple (map2 f tys)
       | Arrow { dom = dom, cod = cod } => Arrow { dom = f dom, cod = f cod }
  end

structure Ty' = ParseTree (Ty)

structure Pat =
  struct
    datatype 'pat t
      = Wildcard

    fun map f =
      fn Wildcard => Wildcard
  end

structure Pat' = Recursive (Pat)

structure Dec =
  struct
    datatype ('dec, 'exp) t
      = Val of TyVar.t seq * (Pat'.t * 'exp) seq1

    fun map (fdec, fexp) =
      fn Val (tyvarseq, binds) => Val (tyvarseq, map1 (fn (pat, exp) => (pat, fexp exp)) binds)
  end

structure Exp =
  struct
    datatype ('dec, 'exp) t
      = VId of { op' : bool, id : LongVId'.t }
      | Unit
      | Tuple of 'exp seq2
      | List of 'exp list
      | Sequence of 'exp seq2
      | Typed of 'exp * Ty'.t

    fun map (fdec, fexp) =
      fn VId { op' = op', id = id }  => VId { op' = op', id = id }
       | Unit                        => Unit
       | Tuple exps                  => Tuple (map2 fexp exps)
       | List exps                   => List (List.map fexp exps)
       | Sequence exps               => Sequence (map2 fexp exps)
       | Typed (exp, ty)             => Typed (fexp exp, ty)
  end

structure DecExp' =
  ParseTree2 (
    structure Template1 = Dec
    structure Template2 = Exp
  )
