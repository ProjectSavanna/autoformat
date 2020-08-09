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

      val wrap = fn
        {string = string, safe = false} => "(" ^ string ^ ")"
      | {string = string, safe = true } => string

      val rec printExp = fn
        A.VarExp path => {string = printPath path, safe = true}
      | A.FnExp rules => {string = "fn " ^ printRules rules, safe = false}
      | A.FlatAppExp exps => (
          case exps of
            nil => raise Invalid "empty FlatAppExp"
          | [exp] => printExp (#item exp)
          | _     => {string = String.concatWith " " (List.map (printExp' o #item) exps), safe = false}
        )
      | A.AppExp {function=function,argument=argument} => {string = printExp' function ^ " " ^ printExp' argument, safe = false}
      | A.CaseExp {expr=expr,rules=rules} => {string = "case " ^ printExp' expr ^ " of\n" ^ printRules rules, safe = false}
      | A.LetExp {dec=dec, expr=expr} => {string = "let " ^ printDec dec ^ " in " ^ printExp' expr ^ " end", safe = true}
      | A.SeqExp exps => (
          case exps of
            nil => raise Invalid "empty SeqExp"
          | [e] => printExp e
          | _   => {string = ListFormat.fmt { init = "(", sep = "; ", final = ")", fmt = #string o printExp} exps, safe = true}
        )
      | A.IntExp (s,_) => {string = s, safe = true}
      | A.WordExp (s,_) => {string = s, safe = true}
      | A.RealExp (s,_) => {string = s, safe = true}
      | A.StringExp s => {string = "\"" ^ String.toString s ^ "\"", safe = true}
      | A.CharExp s => {string = "#\"" ^ String.toString s ^ "\"", safe = true}
      | A.RecordExp l => {string = ListFormat.fmt { init = "{ ", sep = ", ", final = " }", fmt = fn (sym,exp) => Symbol.name sym ^ " = " ^ #string (printExp exp)} l, safe = true}
      | A.ListExp exps => {string = listToString (#string o printExp) exps, safe = true}
      | A.TupleExp exps => {string = tupleToString (#string o printExp) exps, safe = true}
      | A.SelectorExp sym => {string = "#" ^ Symbol.name sym, safe = true}
      | A.ConstraintExp {expr=exp,constraint=ty} => {string = printExp' exp ^ " : " ^ printTy ty, safe = false}
      | A.HandleExp {expr=exp,rules=rules} => {string = printExp' exp ^ " handle " ^ printRules rules, safe = false}
      | A.RaiseExp exp => {string = "raise " ^ #string (printExp exp), safe = false}
      | A.IfExp {test=test,thenCase=thenCase,elseCase=elseCase} => {string = "if " ^ #string (printExp test) ^ " then " ^ #string (printExp thenCase) ^ " else " ^ #string (printExp elseCase), safe = false}
      | A.AndalsoExp (e1,e2) => {string = #string (printExp e1) ^ " andalso " ^ #string (printExp e2), safe = false}
      | A.OrelseExp (e1,e2) => {string = #string (printExp e1) ^ " orelse " ^ #string (printExp e2), safe = false}
      | A.VectorExp exps => {string = "#" ^ listToString (#string o printExp) exps, safe = true}
      | A.WhileExp {test=test,expr=expr} => {string = "while " ^ #string (printExp test) ^ " do " ^ #string (printExp expr), safe = false}
      | A.MarkExp (exp,_) => printExp exp
      and printExp' = fn exp => wrap (printExp exp)
      and printRules = fn rules => (
          let
            val wrap' =
              case rules of
                nil => raise Invalid "empty rules"
              | [r] => #string
              | _   => wrap

            val printed = List.map (fn A.Rule {pat=pat,exp=exp} => {pat = #string (printPat pat), exp=wrap' (printExp exp)}) rules
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
        A.WildPat => {string = "_", safe = true}
      | A.VarPat path => {string = printPath path, safe = true}
      | A.IntPat (s,_) => {string = s, safe = true}
      | A.WordPat (s,_) => {string = s, safe = true}
      | A.StringPat s => {string = "\"" ^ String.toString s ^ "\"", safe = true}
      | A.CharPat s => {string = "#\"" ^ String.toString s ^ "\"", safe = true}
      | A.RecordPat {def=defs,flexibility=flexibility} => {string = ListFormat.fmt { init = "{", sep = ", ", final = if flexibility then ", ...}" else "}", fmt = fn (sym,pat) => Symbol.name sym ^ " = " ^ #string (printPat pat)} defs, safe = true}
      | A.ListPat pats => {string = listToString (#string o printPat) pats, safe = true}
      | A.TuplePat pats => {string = tupleToString (#string o printPat) pats, safe = true}
      | A.FlatAppPat pats => (
          case pats of
            nil   => raise Invalid "empty FlatAppPat"
          | [pat] => printPat (#item pat)
          | _     => {string = String.concatWith " " (List.map (printPat' o #item) pats), safe = false}
        )
      | A.AppPat {constr=constr,argument=argument} => {string = printPat' constr ^ " " ^ printPat' argument, safe = false}
      | A.ConstraintPat {pattern=pat,constraint=ty} => {string = printPat' pat ^ " : " ^ printTy ty, safe = true}
      | A.LayeredPat {varPat=varPat,expPat=expPat} => {string = printPat' varPat ^ " as " ^ printPat' expPat, safe = false}
      | A.VectorPat pats => {string = "#" ^ listToString (#string o printPat) pats, safe = true}
      | A.MarkPat (pat,_) => printPat pat
      | A.OrPat pats => (
          case pats of
            nil => raise Invalid "empty OrPat"
          | [pat] => printPat pat
          | _ => {string = ListFormat.fmt { init = "(", sep = " | ", final = ")", fmt = #string o printPat} pats, safe = true}
        )
      and printPat' = fn pat => wrap (printPat pat)
      and printStrexp = fn
        A.VarStr path => printPath path
      | A.BaseStr dec => "struct " ^ printDec dec ^ " end"
      | A.ConstrainedStr (strexp,sigconst) => printStrexp strexp ^ printSigConst sigconst
      | A.AppStr (path,args) => printPath path ^ " " ^ String.concatWithMap " " (fn (strexp,b) => "(" ^ (if b then "struct" else "") ^ printStrexp strexp ^ (if b then "end" else "") ^ ")") args
      | A.AppStrI (path,args) => printPath path ^ " " ^ String.concatWithMap " " (fn (strexp,b) => "(" ^ (if b then "struct" else "") ^ printStrexp strexp ^ (if b then "end" else "") ^ ")") args
      | A.LetStr (dec,strexp) => "let " ^ printDec dec ^ " in " ^ printStrexp strexp ^ " end"
      | A.MarkStr (strexp,_) => printStrexp strexp
      and printFctexp = fn _ => raise TODO
      and printWherespec = fn _ => raise TODO
      and printSigexp = fn _ => raise TODO
      and printFsigexp = fn _ => raise TODO
      and printSpec = fn _ => raise TODO
      and printSigConst = fn
        A.NoSig          => ""
      | A.Transparent sg => ": " ^ printSigexp sg ^ " "
      | A.Opaque      sg => ":> " ^ printSigexp sg ^ " "
      and printDec = fn
        A.ValDec (vbs,tyvars) => (
          "val " ^ (case printTys (List.map A.VarTy tyvars) of NONE => "" | SOME s => s ^ " ") ^
            String.concatWithMap "\nand " printVb vbs
        )
      | A.StrDec strbs => "structure " ^ String.concatWithMap "\nand " printStrb strbs
      | A.SeqDec decs => decs |> List.map (fn dec => printDec dec ^ "\n") |> String.concat
      | A.MarkDec (dec,_) => printDec dec
      and printVb = fn
        A.Vb {pat=pat,exp=exp,lazyp=false} => #string (printPat pat) ^ " = " ^ #string (printExp exp)
      | A.MarkVb (vb,_) => printVb vb
      and printRvb = fn _ => raise TODO
      and printFb = fn _ => raise TODO
      and printClause = fn _ => raise TODO
      and printTb = fn _ => raise TODO
      and printDb = fn _ => raise TODO
      and printEb = fn _ => raise TODO
      and printStrb = fn
        A.Strb {name=name,def=def,constraint=constraint} => Symbol.name name ^ printSigConst constraint ^ " = " ^ printStrexp def
      | A.MarkStrb (strb,_) => printStrb strb
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
