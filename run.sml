structure Run =
  struct
    local
      val read = fn f => fn filename =>
        let
          val stream = TextIO.openIn filename
        in
          f stream before TextIO.closeIn stream
        end
      val write = fn string => fn filename =>
        let
          val stream = TextIO.openOut filename
        in
          TextIO.output (stream,string) before TextIO.closeOut stream
        end
    in
      val run = fn
        (_, [src, dst]) =>
          let
            val dec =
              read
                (fn stream => SmlFile.parse (Source.newSource (src, stream, false, ErrorMsg.defaultConsumer ())))
                src
          in
            OS.Process.success before write (AutoFormat.toString dec) dst
          end
      | _ => OS.Process.failure before print "Invalid arguments.\n"
    end
  end
