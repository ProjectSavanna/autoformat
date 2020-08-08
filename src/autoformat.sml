structure AutoFormat :> AUTOFORMAT =
  struct
    structure A = Ast

    type t = A.dec

    local
      exception TODO

      val printDec = fn _ => raise TODO
    in
      val toString = printDec
    end
  end
