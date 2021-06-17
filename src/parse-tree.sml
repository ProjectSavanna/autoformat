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

local
  structure Ident =
    struct
      type t = string
      val toString = Fn.id
    end
in
  structure VId   = Ident
        and TyVar = Ident
        and TyCon = Ident
        and Lab   = Ident
        and StrId = Ident
end

functor Long (Ident : SHOW) =
  struct
    local
      structure Template' =
        struct
          datatype 'long t
            = Ident of Ident.t
            | Module of StrId.t * 'long

          fun map f =
            fn Ident id             => Ident id
             | Module (strid, long) => Module (strid, f long)
        end

      structure R = Recursive (Template')
    in
      open R

      structure Template = Template'

      val toString =
        R.fold (
          let
            open Template
          in
            fn Ident id             => Ident.toString id
             | Module (strid, long) => strid ^ "." ^ long
          end
        )
    end
  end

structure LongVId   = Long (VId)
      and LongTyCon = Long (TyCon)
      and LongStrId = Long (StrId)

structure SCon =
  struct
    datatype t
      = Int of int
      | Real of real
      | Word of word
      | Char of char
      | String of string

    val toString =
      fn Int i    => Int.toString i
       | Real r   => Real.toString r
       | Word w   => Word.toString w
       | Char c   => Char.toString c
       | String s => String.toString s
  end

structure Op =
  struct
    type 'a t = { hasOp : bool, data : 'a }

    val map = fn f => fn { hasOp , data } =>
      { hasOp = hasOp, data = f data }

    val toString = fn f => fn { hasOp, data } =>
      if hasOp
        then "op " ^ f data
        else f data
  end

type 'a seq = 'a list
type 'a seq1 = 'a * 'a seq
val map1 = fn f => fn (x1, xs) => (f x1, List.map f xs)
type 'a seq2 = 'a * 'a * 'a seq
val map2 = fn f => fn (x1, x2, xs) => (f x1, f x2, List.map f xs)

structure Ty =
  struct
    datatype 'ty t
      = Var of TyVar.t
      | Cons of 'ty seq * LongTyCon.t
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
      | SCon of SCon.t
      | Var of LongVId.t Op.t
      (* | Record *)
      | Unit
      | Tuple of 'pat seq2
      | List of 'pat list
      | Constructor of LongVId.t Op.t * 'pat

    fun map f =
      fn Wildcard              => Wildcard
       | SCon scon             => SCon scon
       | Var id                => Var id
       | Unit                  => Unit
       | Tuple pats            => Tuple (map2 f pats)
       | List pats             => List (List.map f pats)
       | Constructor (id, pat) => Constructor (id, f pat)
  end

structure Pat' = Recursive (Pat)

structure Prototype =
  struct
    val prettyPrintPat =
      #string o Pat'.fold (
        let
          open Pat

          type t = { atomic : bool, string : string }
          val aux = fn b => fn s => { atomic = b, string = s }
          val atomic = aux true
          val general = aux false
          val wrap = fn { atomic, string } : t => if atomic then string else "(" ^ string ^ ")"
        in
          fn Wildcard              => atomic "_"
           | SCon scon             => atomic (SCon.toString scon)
           | Var id                => atomic (Op.toString LongVId.toString id)
           | Constructor (id, pat) => general (Op.toString LongVId.toString id ^ " " ^ wrap pat)
        end
    )

    local
      open LongVId
    in
      val Ident' = hide o Template.Ident
      val Module' = hide o Template.Module
    end
    val id = fn s => { hasOp = false, data = Module' ("Test", Ident' s) }
    val var = fn s => { hasOp = false, data = Ident' s }
    val ex =
      let
        open Pat
      in
        Pat'.hide (Constructor (id "Foo", Pat'.hide (Constructor (id "Bar", Pat'.hide (Var (var "x"))))))
      end
  end

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
      = Var of LongVId.t Op.t
      | Unit
      | Tuple of 'exp seq2
      | List of 'exp list
      | Sequence of 'exp seq2
      | Typed of 'exp * Ty'.t

    fun map (fdec, fexp) =
      fn Var id          => Var id
       | Unit            => Unit
       | Tuple exps      => Tuple (map2 fexp exps)
       | List exps       => List (List.map fexp exps)
       | Sequence exps   => Sequence (map2 fexp exps)
       | Typed (exp, ty) => Typed (fexp exp, ty)
  end

structure DecExp' =
  ParseTree2 (
    structure Template1 = Dec
    structure Template2 = Exp
  )
