structure AutoFormat :> AUTOFORMAT =
  struct
    structure A = Ast

    type t = A.dec

    local
      infix |>
      fun x |> f = f x

      exception Invalid of string
      exception TODO

      val printTys = fn f => fn
        nil     => ""
      | [tyvar] => f tyvar ^ " "
      | tyvars  => "(" ^ String.concatWithMap "," f tyvars ^ ") "

      val indent = List.map (fn "" => "" | s => "  " ^ s)
      val rec putOnFirst = fn s => fn
        nil => nil
      | x :: xs => s ^ x :: xs
      val rec putOnLast = fn s => fn
        nil => nil
      | [x] => [x ^ s]
      | x :: xs => x :: putOnLast s xs

      val rec separateWithNewlines = fn f => fn
        nil     => nil
      | x :: xs => List.tl (List.concatMap (Fn.curry (op ::) "" o f) (x :: xs))

      val removeWhitespace = String.translate (fn #" " => "" | c => str c)
      fun commas sep [] = []
        | commas sep [x] = x
        | commas sep (x::xs) = putOnLast sep x @ commas sep xs
      val iterFormat = fn { init = init, sep = sep, final = final, fmt = fmt } => fn l => (
        let
          val l' = List.map fmt l
        in
          {
            string =
              if List.exists (fn l => List.length l > 1) l'
                then removeWhitespace init :: indent (commas sep l') @ [removeWhitespace final]
                else [ListFormat.fmt { init = init, sep = sep ^ " ", final = final, fmt = Fn.id } (List.concat l')],
            safe = true
          }
        end
      )

      val printPath = fn
        nil => raise Invalid "empty path"
      | path => String.concatWithMap "." Symbol.name path

      val listToString = fn toString => ListFormat.fmt { init = "[", sep = ", ", final = "]", fmt = toString}
      val tupleToString = fn toString => ListFormat.fmt { init = "(", sep = ", ", final = ")", fmt = toString}

      val concatMapWith = fn sep => fn init => fn f =>
        List.concatMapi (fn (0,x) => f (init,x) | (_,x) => f (sep,x))
      val concatMapAnd = fn keyword => concatMapWith "and " keyword  (* eta-expanded to account for NJ bug? *)

      val wrapStr = fn
        {string = string, safe = false} => "(" ^ string ^ ")"
      | {string = string, safe = true } => string
      val wrapList = fn
        {string = [line], safe = false} => ["(" ^ line ^ ")"]
      | {string = string, safe = false} => "(" :: indent string @ [")"]
      | {string = string, safe = true } => string

      val rec printExp = fn
        A.VarExp path => {string = [printPath path], safe = true}
      | A.FnExp rules => {
          string =
            case printRules rules of
              [rule] => (
                case rule of
                  [line] => ["fn " ^ line]
                | lines  => putOnFirst "fn " lines
              )
            | lines  => concatMapWith " | " "fn " (Fn.uncurry putOnFirst) lines,
          safe = false
        }
      | A.FlatAppExp exps => (
          case exps of
            nil => raise Invalid "empty FlatAppExp"
          | [exp] => printExp (#item exp)
          | _     => {
              string =
                let
                  val l' = List.map (printExp' o #item) exps
                in
                  if List.exists (fn l => List.length l > 1) l'
                    then commas " " l'
                    else [ListFormat.fmt { init = "", sep = " ", final = "", fmt = Fn.id } (List.concat l')]
                end,
              safe = false
            }
        )
      | A.AppExp {function=function,argument=argument} => {
          string =
            case (printExp' function, printExp' argument) of
              ([fLine],[aLine]) => [fLine ^ " " ^ aLine]
            | ([fLine],aLines) => fLine :: indent aLines
            | (fLines,aLines) => fLines @ indent aLines,
          safe = false
        }
      | A.CaseExp {expr=expr,rules=rules} => {
          string =
            case printExp' expr of
              [line] => "case " ^ line ^ " of" :: concatMapWith "| " "  " (Fn.uncurry putOnFirst) (printRules rules)
            | lines  => putOnLast " of" (putOnFirst "case " lines) @ concatMapWith "| " "  " (Fn.uncurry putOnFirst) (printRules rules),
          safe = false
        }
      | A.LetExp {dec=dec, expr=expr} => {string = "let" :: indent (printDec dec) @ ["in"] @ indent (printExp' expr) @ ["end"], safe = true}
      | A.SeqExp exps => (
          case exps of
            nil => raise Invalid "empty SeqExp"
          | [e] => printExp e
          | _   => iterFormat { init = "(", sep = ";", final = ")", fmt = #string o printExp} exps
        )
      | A.IntExp (s,_) => {string = [s], safe = true}
      | A.WordExp (s,_) => {string = [s], safe = true}
      | A.RealExp (s,_) => {string = [s], safe = true}
      | A.StringExp s => {string = ["\"" ^ String.toString s ^ "\""], safe = true}
      | A.CharExp s => {string = ["#\"" ^ String.toString s ^ "\""], safe = true}
      | A.ListExp exps => iterFormat { init = "[", sep = ",", final = "]", fmt = #string o printExp} exps
      | A.RecordExp l => (
          case l of
            nil => {string = ["()"], safe = true}
          | _   => iterFormat { init = "{ ", sep = ",", final = " }", fmt = (fn (sym,exp) => case #string (printExp exp) of [line] => [Symbol.name sym ^ " = " ^ line] | lines => Symbol.name sym ^ " =" :: indent lines)} l
        )
      | A.TupleExp exps => iterFormat { init = "(", sep = ",", final = ")", fmt = #string o printExp} exps
      | A.SelectorExp sym => {string = ["#" ^ Symbol.name sym], safe = true}
      | A.ConstraintExp {expr=exp,constraint=ty} => {string = putOnLast (" : " ^ printTy ty) (printExp' exp), safe = false}
      | A.HandleExp {expr=exp,rules=rules} => {
          string =
            case printExp' exp of
              [line] => putOnFirst line (concatMapWith (StringCvt.padLeft #" " (8 + String.size line) "      | ") " handle " (Fn.uncurry putOnFirst) (printRules rules))
            | lines  => lines @ concatMapWith "     | " "handle " (Fn.uncurry putOnFirst) (printRules rules),
          safe = false
        }
      | A.RaiseExp exp => {string = putOnFirst "raise " (#string (printExp exp)), safe = false}
      | A.IfExp {test=test,thenCase=thenCase,elseCase=elseCase} => {
          string =
            case (#string (printExp test), #string (printExp thenCase), #string (printExp elseCase)) of
              ([testLine],[thenLine],[elseLine]) => ["if " ^ testLine ^ " then " ^ thenLine ^ " else " ^ elseLine]
            | ([testLine],thenLines,elseLines) => "if " ^ testLine :: indent ("then" :: indent thenLines @ ["else"] @ indent elseLines)
            | (testLines,thenLines,elseLines) => "if" :: indent (testLines @ "then" :: indent thenLines @ ["else"] @ indent elseLines),
          safe = false
        }
      | A.AndalsoExp (e1,e2) => {
          string =
            case (#string (printExp e1), #string (printExp e2)) of
              ([line1],[line2]) => [line1 ^ " andalso " ^ line2]
            | ([line1],lines2)  => line1 ^ " andalso" :: lines2
            | (lines1,[line2])  => lines1 @ ["andalso " ^ line2]
            | (lines1,lines2)   => lines1 @ [" andalso "] @ lines2,
          safe = false
        }
      | A.OrelseExp (e1,e2) => {
          string =
            case (#string (printExp e1), #string (printExp e2)) of
              ([line1],[line2]) => [line1 ^ " orelse " ^ line2]
            | ([line1],lines2)  => line1 ^ " orelse" :: lines2
            | (lines1,[line2])  => lines1 @ ["orelse " ^ line2]
            | (lines1,lines2)   => lines1 @ [" orelse "] @ lines2,
          safe = false
        }
      | A.VectorExp exps => raise Invalid "vectors not supported"
      | A.WhileExp {test=test,expr=expr} => {
          string =
            case (#string (printExp test), #string (printExp expr)) of
              ([lineTest],[lineExpr]) => ["while " ^ lineTest ^ " do " ^ lineExpr]
            | ([lineTest],linesExpr)  => "while " ^ lineTest ^ " do" :: linesExpr
            | (linesTest,linesExpr)   => "while" :: linesTest @ ["  do"] @ linesExpr,
          safe = false
        }
      | A.MarkExp (exp,_) => printExp exp
      and printExp' = fn exp => wrapList (printExp exp)
      and printRules = fn rules => (
          let
            val wrap' =
              case rules of
                nil => raise Invalid "empty rules"
              | [r] => #string
              | _   => wrapList

            val printed = List.map (fn A.Rule {pat=pat,exp=exp} => {pat = #string (printPat pat), exp=wrap' (printExp exp)}) rules
            val pad =
              printed
              |> List.map (String.size o #pat)
              |> List.foldr Int.max 0
              |> StringCvt.padRight #" "
          in
            List.map
              (fn {pat=pat,exp=exp} => putOnFirst (pad pat ^ " => ") exp)
              printed
          end
        )
      and printPat = fn
        A.WildPat => {string = "_", safe = true}
      | A.VarPat path => {string = printPath path, safe = true}
      | A.IntPat (s,_) => {string = s, safe = true}
      | A.WordPat (s,_) => {string = s, safe = true}
      | A.StringPat s => {string = "\"" ^ String.toString s ^ "\"", safe = true}
      | A.CharPat s => {string = "#\"" ^ String.toString s ^ "\"", safe = true}
      | A.RecordPat {def=defs,flexibility=flexibility} => {
          string =
            case defs of
              nil => "()"
            | _   => ListFormat.fmt { init = "{", sep = ", ", final = if flexibility then ", ...}" else "}", fmt = fn (sym,pat) => Symbol.name sym ^ " = " ^ #string (printPat pat)} defs,
          safe = true
        }
      | A.ListPat pats => {string = listToString (#string o printPat) pats, safe = true}
      | A.TuplePat pats => {string = tupleToString (#string o printPat) pats, safe = true}
      | A.FlatAppPat pats => (
          case pats of
            nil   => raise Invalid "empty FlatAppPat"
          | [pat] => printPat (#item pat)
          | _     => {string = String.concatWith " " (List.map (printPat' o #item) pats), safe = false}
        )
      | A.AppPat {constr=constr,argument=argument} => {string = printPat' constr ^ " " ^ printPat' argument, safe = false}
      | A.ConstraintPat {pattern=pat,constraint=ty} => {string = printPat' pat ^ " : " ^ printTy ty, safe = false}
      | A.LayeredPat {varPat=varPat,expPat=expPat} => {string = printPat' varPat ^ " as " ^ printPat' expPat, safe = false}
      | A.VectorPat pats => raise Invalid "vectors not supported"
      | A.MarkPat (pat,_) => printPat pat
      | A.OrPat pats => (
          case pats of
            nil => raise Invalid "empty OrPat"
          | [pat] => printPat pat
          | _ => {string = ListFormat.fmt { init = "(", sep = " | ", final = ")", fmt = #string o printPat} pats, safe = true}
        )
      and printPat' = fn pat => wrapStr (printPat pat)
      and printStrexp = fn
        A.VarStr path => [printPath path]
      | A.BaseStr dec => (
          case indent (printDec dec) of
            nil   => ["struct end"]
          | lines => "struct" :: lines  @ ["end"]
        )
      | A.ConstrainedStr (strexp,sigconst) => (
          case printSigConst sigconst of
            [line] => putOnLast line (printStrexp strexp)
          | lines  => printStrexp strexp @ lines
        )
      | (A.AppStr (path,args) | A.AppStrI (path,args)) => (
          case args of
            [(strexp,_)] => (
              case printStrexp strexp of
                [line] => [printPath path ^ " (" ^ line ^ ")"]
              | lines  => printPath path ^ " (" :: indent lines @ [")"]
            )
          | _ => raise Invalid "higher-order modules not supported"
        )
      | A.LetStr (dec,strexp) => "let" :: indent (printDec dec) @ ["in"] @ indent (printStrexp strexp) @ ["end"]
      | A.MarkStr (strexp,_) => printStrexp strexp
      and printFctexp = fn _ => raise TODO
      and printWherespec = fn
        A.WhType (path,tyvars,ty) => "type " ^ printTys printTyvar tyvars ^ printPath path ^ " = " ^ printTy ty
      | A.WhStruct (src,dst) => printPath src ^ " = " ^ printPath dst
      and printSigexp = fn
        A.VarSig sym => [Symbol.name sym]
      | A.AugSig (sigexp,wherespecs) => (
          printSigexp sigexp
          @ (
            wherespecs
            |> concatMapAnd "where " (fn (kw,wherespec) => [kw ^ printWherespec wherespec])
          )
        )
      | A.BaseSig specs => (
          case separateWithNewlines printSpec specs of
            nil   => ["sig end"]
          | lines => "sig" :: indent lines @ ["end"]
        )
      | A.MarkSig (sigexp,_) => printSigexp sigexp
      and printFsigexp = fn _ => raise TODO
      and printSpec = fn
        A.StrSpec structures => (
          structures
          |> concatMapAnd "structure " (
              fn (kw,(name,sigexp,pathOpt)) =>
                case printSigexp sigexp of
                  [line] => [kw ^ Symbol.name name ^ " : " ^ line]
                | lines  => kw ^ Symbol.name name ^ " :" :: indent lines
            )
        )
      | A.TycSpec (types,eq) => (
          types
          |> concatMapAnd (if eq then "eqtype " else "type ") (
              fn (kw,(name,tyvars,tyOpt)) => [kw ^ printTys printTyvar tyvars ^ Symbol.name name
                ^ (case tyOpt of NONE => "" | SOME ty => " = " ^ printTy ty)]
            )
        )
      | A.FctSpec _ => raise Invalid "<fctsig> ignored"
      | A.ValSpec vals => (
          vals
          |> concatMapAnd "val " (fn (kw,(name,ty)) => [kw ^ Symbol.name name ^ " : " ^ printTy ty])
        )
      | A.DataSpec {datatycs=datatycs, withtycs=withtycs} => (
          case withtycs of
            nil => concatMapAnd "datatype " (fn (kw,db) => case printDb db of [line] => [kw ^ line] | lines => kw :: indent lines) datatycs
          | _ => raise Invalid "nonempty withtycs"
        )
      | A.DataReplSpec (name,path) => ["datatype " ^ Symbol.name name ^ " = datatype " ^ printPath path]
      | A.ExceSpec exns => (
        exns
        |> concatMapAnd "exception " (
            fn (kw,(name,tyOpt)) => [
              kw ^ Symbol.name name ^ (
                case tyOpt of
                  NONE    => ""
                | SOME ty => " of " ^ printTy ty
              )
            ]
          )
      )
      | A.ShareStrSpec paths => ["sharing " ^ String.concatWithMap " = " printPath paths]
      | A.ShareTycSpec paths => ["sharing type " ^ String.concatWithMap " = " printPath paths]
      | A.IncludeSpec sigexp => (
          case printSigexp sigexp of
            nil => nil
          | line :: lines => "include " ^ line :: lines
        )
      | A.MarkSpec (spec,_) => printSpec spec
      and printSigConst = fn
        A.NoSig          => nil
      | A.Transparent sg => (
          case printSigexp sg of
            [line] => [" : " ^ line]
          | lines  => ":" :: lines
        )
      | A.Opaque      sg => (
          case printSigexp sg of
            [line] => [" :> " ^ line]
          | lines  => ":>" :: lines
        )
      and printDec = fn
        A.ValDec (vbs,tyvars) => (
          vbs
          |> List.map printVb
          |> concatMapAnd ("val " ^ printTys printTyvar tyvars) (
              fn (kw,{pat=pat,exp=[line]}) => [kw ^ pat ^ " = " ^ line]
               | (kw,{pat=pat,exp=lines}) => kw ^ pat ^ " =" :: indent lines
            )
        )
      | A.ValrecDec (rbvs,tyvars) => (
          rbvs
          |> List.map printRvb
          |> concatMapAnd ("val rec " ^ printTys printTyvar tyvars) (
              fn (kw,{init=init,exp=[line]}) => [kw ^ init ^ " = " ^ line]
               | (kw,{init=init,exp=lines}) => kw ^ init ^ " =" :: indent lines
            )
        )
      | A.DoDec _ => raise Invalid "unsupported declaration: 'do'"
      | A.FunDec (fbs,tyvars) => (
          fbs
          |> List.map printFb
          |> concatMapAnd ("fun " ^ printTys printTyvar tyvars) (Fn.uncurry putOnFirst)
        )
      | A.TypeDec tbs => (
          tbs
          |> List.map printTb
          |> concatMapAnd "type " (fn (kw,str) => [kw ^ str])
        )
      | A.DatatypeDec {datatycs=datatycs,withtycs=withtycs} => (
          (
            concatMapAnd "datatype " (
              fn (kw,db) =>
                case printDb db of
                  [line] => [kw ^ line]
                | lines => kw :: indent lines
            ) datatycs
          ) @ concatMapAnd "withtype " (fn (kw,db) => [kw ^ printTb db]) withtycs
        )
      | A.ExceptionDec ebs => (
          ebs
          |> List.map printEb
          |> concatMapAnd "exception " (fn (kw,str) => [kw ^ str])
        )
      | A.StrDec strbs => (
          strbs
          |> List.map printStrb
          |> concatMapAnd "structure " (fn (kw,{name=name,def=def,constraint=constraint}) =>
            let
              val decl =
                putOnLast " =" (
                  case constraint of
                    nil => [kw ^ name]
                  | [l] => [kw ^ name ^ l]
                  | l::ls  => kw ^ name ^ l :: indent ls
                )
            in
              case def of
                nil => decl
              | [l] => putOnLast (" " ^ l) decl
              | _   => decl @ indent def
            end
          )
        )
      | A.SigDec sigbs => (
          sigbs
          |> List.map printSigb
          |> concatMapAnd "signature " (
              fn (kw,{name=name,def=[line]}) => [kw ^ name ^ " = " ^ line]
               | (kw,{name=name,def=def   }) => kw ^ name ^ " =" :: indent def
            )
        )
      | A.FsigDec _ => raise Invalid "funsig not supported"
      | A.LocalDec (dec1,dec2) => "local" :: indent (printDec dec1) @ ["in"] @ indent (printDec dec2) @ ["end"]
      | A.SeqDec decs => separateWithNewlines printDec decs
      | A.OpenDec paths => ["open " ^ String.concatWithMap " " printPath paths]
      | A.OvldDec _ => raise Invalid "not available in external language"
      | A.FixDec {fixity=fixity, ops=ops} => [Fixity.fixityToString fixity ^ String.concatWithMap " " Symbol.name ops]
      | A.MarkDec (dec,_) => printDec dec
      and printVb = fn
        A.Vb {pat=pat,exp=exp,lazyp=_} => { pat = #string (printPat pat), exp = #string (printExp exp) }
      | A.MarkVb (vb,_) => printVb vb
      and printRvb = fn
        A.Rvb {var=var,fixity=fixity,exp=exp,resultty=resulttyOpt,lazyp=_} => {
          init =
            (
              if Option.isNone fixity
                then "op "
                else ""
            ) ^
            Symbol.name var ^ (
              case resulttyOpt of
                NONE => ""
              | SOME ty => " : " ^ printTy ty
            ),
          exp = #string (printExp exp)
        }
      | A.MarkRvb (rvb,_) => printRvb rvb
      and printFb = fn
        A.Fb (clauses,_) => concatMapWith "  | " "" (fn (kw,clause) => (putOnFirst kw o printClause) clause) clauses
      | A.MarkFb (fb,_) => printFb fb
      and printClause = fn
        A.Clause {pats=pats,resultty=resulttyOpt,exp=exp} =>
        putOnFirst (
          String.concatWithMap " " (printPat' o #item) pats ^ (
            case resulttyOpt of
              NONE => ""
            | SOME ty => " : " ^ printTy ty
          ) ^ " = "
        ) (printExp' exp)
      and printTb = fn
        A.Tb {tyc=tyc,def=def,tyvars=tyvars} => printTys printTyvar tyvars ^ Symbol.name tyc ^ " = " ^ printTy def
      | A.MarkTb (tb,_) => printTb tb
      and printDb = fn
        A.Db {tyc=tyc, tyvars=tyvars, rhs=rhs, lazyp=_} => [
          printTys printTyvar tyvars ^ Symbol.name tyc ^ " = " ^
            String.concatWithMap " | " (fn (name,NONE) => Symbol.name name | (name,SOME ty) => Symbol.name name ^ " of " ^ printTy ty) rhs
        ]
      | A.MarkDb (db,_) => printDb db
      and printEb = fn
        A.EbGen {exn=exn,etype=etypeOpt} => Symbol.name exn ^ (
          case etypeOpt of
            NONE => ""
          | SOME ty => " of " ^ printTy ty
        )
      | A.EbDef {exn=exn,edef=edef} => Symbol.name exn ^ " = " ^ printPath edef
      | A.MarkEb (eb,_) => printEb eb
      and printStrb = fn
        A.Strb {name=name,def=def,constraint=constraint} => {name=Symbol.name name, def=printStrexp def, constraint=printSigConst constraint}
      | A.MarkStrb (strb,_) => printStrb strb
      and printFctb = fn _ => raise TODO
      and printSigb = fn
        A.Sigb {name=name,def=def} => {name=Symbol.name name,def=printSigexp def}
      | A.MarkSigb (sigb,_) => printSigb sigb
      and printTyvar = fn
        A.Tyv a => Symbol.name a
      | A.MarkTyv (tyvar,_) => printTyvar tyvar
      and printTy = fn
        A.VarTy tyvar => printTyvar tyvar
      | A.ConTy (path,tyvars) => printTys printTy tyvars ^ printPath path
      | A.TupleTy tys => String.concatWithMap " * " printTy tys
      | A.MarkTy (ty,_) => printTy ty
    in
      val toString = String.concat o List.map (fn s => s ^ "\n") o printDec
    end
  end
