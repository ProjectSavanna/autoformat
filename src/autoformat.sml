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
        A.VarExp path => {string = printPath path, safe = true}
      | A.FnExp rules => {string = "fn " ^ printRules rules, safe = false}
      | A.FlatAppExp exps => (
          case exps of
            nil => raise Invalid "empty FlatAppExp"
          | [exp] => printExp (#item exp)
          | _     => {string = String.concatWith " " (List.map (printExp' o #item) exps), safe = false}
        )
      | A.CaseExp {expr=exp,rules=rules} => {string = "case " ^ printExp' exp ^ " of\n" ^ printRules rules, safe = false}
      | A.SeqExp exps => (
          case exps of
            nil => raise Invalid "empty SeqExp"
          | [e] => printExp e
          | _   => {string = ListFormat.fmt { init = "(", sep = "; ", final = ")", fmt = #string o printExp} exps, safe = true}
        )
      | A.IntExp (s,_) => {string = s, safe = true}
      | A.StringExp s => {string = "\"" ^ String.toString s ^ "\"", safe = true}
      | A.HandleExp {expr=exp,rules=rules} => {string = printExp' exp ^ " handle " ^ printRules rules, safe = false}
      | A.MarkExp (exp,_) => printExp exp
      and printExp' = fn exp => wrapExp (printExp exp)
      and wrapExp = fn
        {string = string, safe = false} => "(" ^ string ^ ")"
      | {string = string, safe = true } => string
      and printRules = fn rules => (
          let
            val wrap =
              case rules of
                nil => raise Invalid "empty rules"
              | [r] => #string
              | _   => wrapExp

            val printed = List.map (fn A.Rule {pat=pat,exp=exp} => {pat=printPat pat, exp=wrap (printExp exp)}) rules
            val pad =
              printed
              |> List.map (String.size o #pat)
              |> List.foldr Int.max 0
              |> StringCvt.padRight #" "
          in
            "  " ^ String.concatWith "\n| " (
              List.map
                (fn {pat=pat,exp=exp} => pad pat ^ " => " ^ exp)
                printed
            )
          end
        )
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
        A.Vb {pat=pat,exp=exp,lazyp=false} => printPat pat ^ " = " ^ #string (printExp exp)
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
