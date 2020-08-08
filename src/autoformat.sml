structure AutoFormat :> AUTOFORMAT =
  struct
    structure A = Ast

    type t = A.dec

    local
      infix |>
      fun x |> f = f x

      exception Invalid of string
      exception TODO

      val printPath = fn
        nil => raise Invalid "empty path"
      | path => String.concatWithMap "." Symbol.name path

      val listToString = fn toString => ListFormat.fmt { init = "[", sep = ", ", final = "]", fmt = toString}
      val tupleToString = fn toString => ListFormat.fmt { init = "(", sep = ", ", final = ")", fmt = toString}

      val rec printExp = fn
        A.VarExp path => printPath path
      | A.FlatAppExp exps => (case exps of [exp] => printExp (#item exp) | _ => raise Invalid "unexpected FlatAppExp")
      | A.SeqExp exps => (
          case exps of
            nil => raise Invalid "empty SeqExp"
          | [e] => printExp e
          | _   => ListFormat.fmt { init = "(", sep = "; ", final = ")", fmt = printExp} exps
        )
      | A.IntExp (s,_) => s
      | A.MarkExp (exp,_) => printExp exp
      and printRule = fn
        A.Rule {pat=pat,exp=exp} => printPat pat ^ " => " ^ printExp exp
      and printPat = fn
        A.WildPat => "_"
      | A.VarPat path => printPath path
      | A.IntPat (s,_) => s
      | A.WordPat (s,_) => s
      | A.StringPat s => "\"" ^ String.toString s ^ "\""
      | A.CharPat s => "#\"" ^ String.toString s ^ "\""
      | A.ListPat pats => listToString printPat pats
      | A.TuplePat pats => tupleToString printPat pats
      | A.FlatAppPat pats => (case pats of [pat] => printPat (#item pat) | _ => raise Invalid "unexpected FlatAppPat")
      | A.ConstraintPat {pattern=pat,constraint=ty} => printPat pat ^ " : " ^ printTy ty
      | A.MarkPat (pat,_) => printPat pat
      and printStrexp = fn _ => raise TODO
      and printFctexp = fn _ => raise TODO
      and printWherespec = fn _ => raise TODO
      and printSigspec = fn _ => raise TODO
      and printFsigexp = fn _ => raise TODO
      and printSpec = fn _ => raise TODO
      and printDec = fn
        A.ValDec (vbs,tyvars) => (
          "val " ^ (case printTys (List.map A.VarTy tyvars) of NONE => "" | SOME s => s ^ " ") ^
            String.concatWithMap "\nand " printVb vbs
        )
      | A.SeqDec decs => decs |> List.map (fn dec => printDec dec ^ "\n") |> String.concat
      | A.MarkDec (dec,_) => printDec dec
      and printVb = fn
        A.Vb {pat=pat,exp=exp,lazyp=false} => printPat pat ^ " = " ^ printExp exp
      | A.MarkVb (vb,_) => printVb vb
      and printRvb = fn _ => raise TODO
      and printFb = fn _ => raise TODO
      and printClause = fn _ => raise TODO
      and printTb = fn _ => raise TODO
      and printDb = fn _ => raise TODO
      and printEb = fn _ => raise TODO
      and printStrb = fn _ => raise TODO
      and printFctb = fn _ => raise TODO
      and printSigb = fn _ => raise TODO
      and printFsigb = fn _ => raise TODO
      and printTyvar = fn
        A.Tyv a => Symbol.name a
      | A.MarkTyv (tyvar,_) => printTyvar tyvar
      and printTy = fn
        A.VarTy tyvar => printTyvar tyvar
      | A.ConTy (path,tyvars) => (case printTys tyvars of NONE => "" | SOME s => s ^ " ") ^ printPath path
      | A.TupleTy tys => String.concatWithMap " * " printTy tys
      | A.MarkTy (ty,_) => printTy ty
      and printTys = fn
        nil     => NONE
      | [tyvar] => SOME (printTy tyvar)
      | tyvars  => SOME ("(" ^ String.concatWithMap "," printTy tyvars ^ ")")
    in
      val toString = printDec
    end
  end
