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
signature SYMBOL =
  sig
    include READ SHOW
  end

local
  structure Ident :> SYMBOL =
    struct
      type t = string
      val fromString = SOME
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
             | Module (strid, long) => StrId.toString strid ^ "." ^ long
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

structure SeqFormat =
  struct
    local
      fun aux stop sep f nil        = stop
        | aux stop sep f (x :: nil) = f x ^ stop
        | aux stop sep f (x :: xs)  = f x ^ sep ^ aux stop sep f xs
    in
      val format = fn { start, stop, sep } => fn f => fn l => start ^ aux stop sep f l
    end
  end

structure List =
  struct
    open List

    type 'a t = 'a list
    val toString = fn f => SeqFormat.format { start = "[", stop = "]", sep = ", " } f
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
      | Tuple of 'ty Seq2.t
      | Arrow of { dom : 'ty, cod : 'ty }

    fun map f =
      fn Var tyvar                      => Var tyvar
       | Cons (tyseq, longtycon)        => Cons (Seq.map f tyseq, longtycon)
       | Record tyrows                  => Record (List.map (fn (lab, ty) => (lab, f ty)) tyrows)
       | Tuple tys                      => Tuple (Seq2.map f tys)
       | Arrow { dom = dom, cod = cod } => Arrow { dom = f dom, cod = f cod }
  end

structure Ty' = Recursive (Ty)

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

functor Precedence (Precedence : ORDERED) :>
  sig
    type t
    val hide : Precedence.t -> string -> t
    val show : Precedence.t -> t -> string
  end =
  struct
    type t = { precedence : Precedence.t, string : string }

    val hide = fn precedence => fn s => { precedence = precedence, string = s }

    val op <= = fn (precedence1, precedence2) =>
      case Precedence.compare (precedence1, precedence2) of
        LESS    => true
      | EQUAL   => true
      | GREATER => false

    val show = fn precedence' => fn { precedence, string } =>
      if precedence' <= precedence
        then string
        else "(" ^ string ^ ")"
  end

structure Prototype =
  struct
    local
      open LongVId
    in
      val Ident' = hide o Template.Ident
      val Module' = hide o Template.Module
    end
    val $ = valOf o StrId.fromString
    val id = fn s => { hasOp = false, data = Module' ($"Test", Ident' ($s)) }
    val var = fn s => { hasOp = false, data = Ident' ($s) }

    structure Ty =
      struct
        structure Prec =
          struct
            datatype t = Arrow | Tuple | Atomic

            val eq = op =
            val compare =
             fn (Arrow , Arrow ) => EQUAL
              | (Arrow , _     ) => LESS
              | (Tuple , Arrow ) => GREATER
              | (Tuple , Tuple ) => EQUAL
              | (Tuple , _     ) => LESS
              | (Atomic, Arrow ) => GREATER
              | (Atomic, Tuple ) => GREATER
              | (Atomic, Atomic) => EQUAL

            val zero = Arrow
            val succ =
             fn Arrow => Tuple
              | Tuple => Atomic
              | Atomic => Atomic
          end

        structure TyPrec = Precedence (Prec)


        val prettyPrint =
          Ty'.fold (
            let
              open Ty

              val intercalate = fn sep => fn (ty1, ty2, tys) =>
                SeqFormat.format { start = "", stop = "", sep = sep } Fn.id (ty1 :: ty2 :: tys)
            in
              fn Var tyvar                      => TyPrec.hide Prec.Atomic (TyVar.toString tyvar)
               | Cons (tyseq, longtycon)        => 
                  TyPrec.hide Prec.Atomic (
                    (
                      case tyseq of
                        nil            => ""
                      | x :: nil       => TyPrec.show Prec.Atomic x ^ " "
                      | x1 :: x2 :: xs => Tuple.toString (TyPrec.show Prec.zero) (x1, x2, xs) ^ " "
                    ) ^ LongTyCon.toString longtycon
                  )
               | Record tyrows                  => TyPrec.hide Prec.Atomic (SeqFormat.format { start = "{ ", stop = " }", sep = ", " } (fn (lab, ty) => Lab.toString lab ^ " : " ^ TyPrec.show Prec.zero ty) tyrows)
               | Tuple tys                      => TyPrec.hide Prec.Tuple (intercalate " * " (Seq2.map (TyPrec.show (Prec.succ Prec.Tuple)) tys))
               | Arrow { dom = dom, cod = cod } => TyPrec.hide Prec.Arrow (TyPrec.show (Prec.succ Prec.Arrow) dom ^ " -> " ^ TyPrec.show Prec.Arrow cod)
            end
          )

        val ex =
          let
            open Ty
            val Var' = Ty'.hide o Var
            val Cons' = Ty'.hide o Cons
            val Tuple' = Ty'.hide o Tuple
            val Arrow' = Ty'.hide o Arrow

            val Ident' = LongTyCon.hide o LongTyCon.Template.Ident
            val Module' = LongTyCon.hide o LongTyCon.Template.Module

            infixr ==>
            val op ==> = fn (dom, cod) => Arrow' { dom = dom, cod = cod }
            infixr **
            val op ** = fn (ty1, ty2) => Tuple' (ty1, ty2, [])

            val ty = fn s => Module' ($s, Ident' ($"t"))
            val dott = fn s => Cons' ([], ty s)
          in
            (* Tuple' (Tuple' (dott "Int", dott "String", []), dott "Bool", []) *)
            (* Arrow' { dom = Tuple' (dott "Int", dott "String", []), cod = Arrow' { dom = dott "Bool", cod = dott "Real" } } *)
            (* dott "List" ==> Tuple' (dott "Int", dott "String", [dott "Foo", dott "Bar" ** dott "Baz", dott "Qux"]) ==> (dott "Bool" ** dott "Real") *)
            Cons' ([dott "Int" ** dott "String"], ty "List") ==> Cons' ([dott "Bool"], ty "List")
            (* Cons' ([Var' ($"'a"), Cons' ([Var' ($"'b"), Cons' ([], Ident' ($"int"))], ty "Either")], ty "List") *)
          end
      end

    structure Pat =
      struct
        structure Prec =
          struct
            datatype t = Complex | Atomic

            val eq = op =
            val compare =
              fn (Complex, Complex) => EQUAL
               | (Complex, Atomic ) => LESS
               | (Atomic , Complex) => GREATER
               | (Atomic , Atomic ) => EQUAL

            val zero = Complex
            val succ =
             fn Complex => Atomic
              | Atomic  => Atomic
          end
        structure Atomic = Precedence (Prec)

        val prettyPrint =
          Pat'.fold (
            let
              open Pat
            in
              fn Wildcard              => Atomic.hide Prec.Atomic "_"
               | SCon scon             => Atomic.hide Prec.Atomic (SCon.toString scon)
               | Var id                => Atomic.hide Prec.Atomic (Op.toString LongVId.toString id)
               | Unit                  => Atomic.hide Prec.Atomic "()"  (* TODO: factor out *)
               | Tuple pats            => Atomic.hide Prec.Atomic (Tuple.toString (Atomic.show Prec.zero) pats)
               | List pats             => Atomic.hide Prec.Atomic (List.toString (Atomic.show Prec.zero) pats)
               | Constructor (id, pat) => Atomic.hide Prec.Complex (Op.toString LongVId.toString id ^ " " ^ Atomic.show Prec.Atomic pat)
            end
          )

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
