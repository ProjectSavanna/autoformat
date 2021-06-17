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

structure List =
  struct
    open List

    type 'a t = 'a list

    local
      fun aux f nil        = "]"
        | aux f (x :: nil) = f x ^ "]"
        | aux f (x :: xs)  = f x ^ ", " ^ aux f xs
    in
      val toString = fn f => fn l => "[" ^ aux f l
    end
  end

structure Seq =
  struct
    type 'a t = 'a list
    val map = List.map
  end

structure Seq1 =
  struct
    type 'a t = 'a * 'a list
    val map = fn f => fn (x1, xs) => (f x1, List.map f xs)
  end

structure Tuple =
  struct
    type 'a t = 'a * 'a * 'a list
    val map = fn f => fn (x1, x2, xs) => (f x1, f x2, List.map f xs)

    val toString : ('a -> string) -> 'a t -> string =
      fn f => fn (x1, x2, xs) => "(" ^ f x1 ^ String.concat (List.map (fn x => ", " ^ f x) (x2 :: xs)) ^ ")"
  end

structure Seq2 =
  struct
    type 'a t = 'a * 'a * 'a list
    val map = fn f => fn (x1, x2, xs) => (f x1, f x2, List.map f xs)
  end

structure Ty =
  struct
    datatype 'ty t
      = Var of TyVar.t
      | Cons of 'ty Seq.t * LongTyCon.t
      | Record of (Lab.t * 'ty) list
      | Tuple of 'ty Tuple.t
      | Arrow of { dom : 'ty, cod : 'ty }

    fun map f =
      fn Var tyvar                      => Var tyvar
       | Cons (tyseq, longtycon)        => Cons (Seq.map f tyseq, longtycon)
       | Record tyrows                  => Record (List.map (fn (lab, ty) => (lab, f ty)) tyrows)
       | Tuple tys                      => Tuple (Tuple.map f tys)
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
      | Tuple of 'pat Tuple.t
      | List of 'pat list
      | Constructor of LongVId.t Op.t * 'pat

    fun map f =
      fn Wildcard              => Wildcard
       | SCon scon             => SCon scon
       | Var id                => Var id
       | Unit                  => Unit
       | Tuple pats            => Tuple (Tuple.map f pats)
       | List pats             => List (List.map f pats)
       | Constructor (id, pat) => Constructor (id, f pat)
  end

structure Pat' = Recursive (Pat)

structure Atomic :>
  sig
    include FUNCTOR

    val atomic : 'a -> 'a t
    and complex : 'a -> 'a t

    val extract : 'a t -> 'a

    val toString : string t -> string
  end =
  struct
    type 'a t = { atomic : bool, data : 'a }

    val map = fn f => fn { atomic, data } => { atomic = atomic, data = f data }

    val atomic = fn x => { atomic = true, data = x }
    and complex = fn x => { atomic = false, data = x }

    val extract : 'a t -> 'a = #data

    val toString = fn { atomic, data = string } : string t =>
      if atomic
        then string
        else "(" ^ string ^ ")"
  end

structure Prototype =
  struct
    val prettyPrintPat =
      Pat'.fold (
        let
          open Pat
        in
          fn Wildcard              => Atomic.atomic "_"
           | SCon scon             => Atomic.atomic (SCon.toString scon)
           | Var id                => Atomic.atomic (Op.toString LongVId.toString id)
           | Unit                  => Atomic.atomic "()"  (* TODO: factor out *)
           | Tuple pats            => Atomic.atomic (Tuple.toString Atomic.extract pats)
           | List pats             => Atomic.atomic (List.toString Atomic.extract pats)
           | Constructor (id, pat) => Atomic.complex (Op.toString LongVId.toString id ^ " " ^ Atomic.toString pat)
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
        val Wildcard' = Pat'.hide Wildcard
        val SCon' = Pat'.hide o SCon
        val Var' = Pat'.hide o Var
        val Unit' = Pat'.hide Unit
        val Tuple' = Pat'.hide o Tuple
        val List' = Pat'.hide o List
        val Constructor' = Pat'.hide o Constructor
      in
        Constructor' (id "Qux",
          Tuple' (
            Constructor' (id "Foo",
              Constructor' (id "Bar",
                Tuple' (Var' (var "x"), Unit', [SCon' (SCon.Int 3), Constructor' (id "Baz", Unit')])
              )
            ),
            Wildcard',
            [List' [Wildcard', Var' (var "y"), Wildcard']]
          )
        )
      end
  end

structure Dec =
  struct
    datatype ('dec, 'exp) t
      = Val of TyVar.t Seq.t * (Pat'.t * 'exp) Seq1.t

    fun map (fdec, fexp) =
      fn Val (tyvarseq, binds) => Val (tyvarseq, Seq1.map (fn (pat, exp) => (pat, fexp exp)) binds)
  end

structure Exp =
  struct
    datatype ('dec, 'exp) t
      = Var of LongVId.t Op.t
      | Unit
      | Tuple of 'exp Tuple.t
      | List of 'exp list
      | Sequence of 'exp Seq2.t
      | Typed of 'exp * Ty'.t

    fun map (fdec, fexp) =
      fn Var id          => Var id
       | Unit            => Unit
       | Tuple exps      => Tuple (Tuple.map fexp exps)
       | List exps       => List (List.map fexp exps)
       | Sequence exps   => Sequence (Seq2.map fexp exps)
       | Typed (exp, ty) => Typed (fexp exp, ty)
  end

structure DecExp' =
  ParseTree2 (
    structure Template1 = Dec
    structure Template2 = Exp
  )
