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
      | A.CaseExp {expr=expr,rules=rules} => {string = "case " ^ printExp' expr ^ " of " ^ printRules rules, safe = false}
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
            "  " ^ String.concatWith " | " (
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
      | A.AppStr (path,args) => printPath path ^ " " ^ String.concatWithMap " " (fn (strexp,_) => "(" ^ printStrexp strexp ^ ")") args
      | A.AppStrI (path,args) => printPath path ^ " " ^ String.concatWithMap " " (fn (strexp,_) => "(" ^ printStrexp strexp ^ ")") args
      | A.LetStr (dec,strexp) => "let " ^ printDec dec ^ " in " ^ printStrexp strexp ^ " end"
      | A.MarkStr (strexp,_) => printStrexp strexp
      and printFctexp = fn _ => raise TODO
      and printWherespec = fn
        A.WhType (path,tyvars,ty) => "type " ^ printTys (List.map A.VarTy tyvars) ^ printPath path ^ " = " ^ printTy ty
      | A.WhStruct (src,dst) => printPath src ^ " = " ^ printPath dst
      and printSigexp = fn
        A.VarSig sym => Symbol.name sym
      | A.AugSig (sigexp,wherespecs) => printSigexp sigexp ^ " where " ^ String.concatWithMap " and " printWherespec wherespecs
      | A.BaseSig specs => "sig " ^ String.concatWithMap " " printSpec specs ^ " end"
      | A.MarkSig (sigexp,_) => printSigexp sigexp
      and printFsigexp = fn _ => raise TODO
      and printSpec = fn
        A.StrSpec structures => "structure " ^ String.concatWithMap " and " (fn (name,sigexp,pathOpt) => Symbol.name name ^ " : " ^ printSigexp sigexp ^ (case pathOpt of NONE => "" | SOME path => " = " ^ printPath path)) structures
      | A.TycSpec (types,eq) => (if eq then "eqtype" else "type") ^ " " ^ String.concatWithMap " and " (fn (name,tyvars,tyOpt) => printTys (List.map A.VarTy tyvars) ^ Symbol.name name ^ (case tyOpt of NONE => "" | SOME ty => " = " ^ printTy ty)) types
      | A.FctSpec _ => raise Invalid "<fctsig> ignored"
      | A.ValSpec vals => "val " ^ String.concatWithMap " and " (fn (name,ty) => Symbol.name name ^ " : " ^ printTy ty) vals
      | A.DataSpec {datatycs=datatycs, withtycs=withtycs} => (
          case withtycs of
            nil => "datatype " ^ String.concatWithMap " and " printDb datatycs
          | _ => raise Invalid "nonempty withtycs"
        )
      | A.DataReplSpec (name,path) => "datatype " ^ Symbol.name name ^ " = datatype " ^ printPath path
      | A.ExceSpec exns => "exception " ^ String.concatWithMap " and " (fn (name,NONE) => Symbol.name name | (name,SOME ty) => Symbol.name name ^ " of " ^ printTy ty) exns
      | A.ShareStrSpec paths => "sharing " ^ String.concatWithMap " = " printPath paths
      | A.ShareTycSpec paths => "sharing type " ^ String.concatWithMap " = " printPath paths
      | A.IncludeSpec sigexp => "include " ^ printSigexp sigexp
      | A.MarkSpec (spec,_) => printSpec spec
      and printSigConst = fn
        A.NoSig          => ""
      | A.Transparent sg => ": " ^ printSigexp sg ^ " "
      | A.Opaque      sg => ":> " ^ printSigexp sg ^ " "
      and printDec = fn
        A.ValDec (vbs,tyvars) => "val " ^ printTys (List.map A.VarTy tyvars) ^ String.concatWithMap " and " printVb vbs
      | A.StrDec strbs => "structure " ^ String.concatWithMap " and " printStrb strbs
      | A.SigDec sigbs => "signature " ^ String.concatWithMap " and " printSigb sigbs
      | A.SeqDec decs => decs |> List.map (fn dec => printDec dec ^ " ") |> String.concat
      | A.MarkDec (dec,_) => printDec dec
      and printVb = fn
        A.Vb {pat=pat,exp=exp,lazyp=_} => #string (printPat pat) ^ " = " ^ #string (printExp exp)
      | A.MarkVb (vb,_) => printVb vb
      and printRvb = fn _ => raise TODO
      and printFb = fn _ => raise TODO
      and printClause = fn _ => raise TODO
      and printTb = fn _ => raise TODO
      and printDb = fn
        A.Db {tyc=tyc, tyvars=tyvars, rhs=rhs, lazyp=_} => (
          printTys (List.map A.VarTy tyvars) ^ Symbol.name tyc ^ " = " ^
            String.concatWithMap " | " (fn (name,NONE) => Symbol.name name | (name,SOME ty) => Symbol.name name ^ " of " ^ printTy ty) rhs
        )
      | A.MarkDb (db,_) => printDb db
      and printEb = fn _ => raise TODO
      and printStrb = fn
        A.Strb {name=name,def=def,constraint=constraint} => Symbol.name name ^ printSigConst constraint ^ " = " ^ printStrexp def
      | A.MarkStrb (strb,_) => printStrb strb
      and printFctb = fn _ => raise TODO
      and printSigb = fn
        A.Sigb {name=name,def=def} => Symbol.name name ^ " = " ^ printSigexp def
      | A.MarkSigb (sigb,_) => printSigb sigb
      and printFsigb = fn _ => raise TODO
      and printTyvar = fn
        A.Tyv a => Symbol.name a
      | A.MarkTyv (tyvar,_) => printTyvar tyvar
      and printTy = fn
        A.VarTy tyvar => printTyvar tyvar
      | A.ConTy (path,tyvars) => printTys tyvars ^ printPath path
      | A.TupleTy tys => String.concatWithMap " * " printTy tys
      | A.MarkTy (ty,_) => printTy ty
      and printTys = fn
        nil     => ""
      | [tyvar] => printTy tyvar ^ " "
      | tyvars  => "(" ^ String.concatWithMap "," printTy tyvars ^ ") "
    in
      val toString = printDec
    end
  end
