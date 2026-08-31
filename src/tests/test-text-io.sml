(* Tests for TextIO.
 *
 * The input side is tested through TextIO.openString, which is part of the
 * required TEXT_IO signature and needs no file system, so these tests run
 * even on a hosted implementation with no storage.  Only the group that
 * actually opens files is gated on C.hasFileSystem.
 *)

functor TextIOTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val str = G.printableString
    val showS = Show.string

    (* Lines of printable text, joined with newlines -- the shape that the
     * line-oriented operations are actually about. *)
    val lines =
      G.bind (G.int (0, 5)) (fn n =>
        G.listN n (G.map String.implode (G.list G.printableChar)))

    fun readAllLines ins =
      case TextIO.inputLine ins of
          NONE => []
        | SOME l => l :: readAllLines ins

    val scratch = C.scratchDir
    fun scratchFile name = OS.Path.concat (scratch, name)

    (* Create the scratch directory on demand; leave it in place afterwards so
     * that a failing run can be inspected. *)
    fun ensureScratch () =
      if OS.FileSys.access (scratch, []) then ()
      else OS.FileSys.mkDir scratch

    fun withOutFile (name, f) =
      let
        val () = ensureScratch ()
        val path = scratchFile name
        val outs = TextIO.openOut path
      in
        (f outs; TextIO.closeOut outs; path)
        handle e => (TextIO.closeOut outs; raise e)
      end

    fun readWholeFile path =
      let
        val ins = TextIO.openIn path
      in
        TextIO.inputAll ins before TextIO.closeIn ins
        handle e => (TextIO.closeIn ins; raise e)
      end

    fun removeQuietly path =
      OS.FileSys.remove path handle _ => ()

    val suite = Group ("TextIO",
      [ Group ("reading from a string",
        [ Case ("input1 delivers one character at a time", fn () =>
            let
              val ins = TextIO.openString "ab"
            in
              A.eqCharOption "first" (SOME #"a", TextIO.input1 ins);
              A.eqCharOption "second" (SOME #"b", TextIO.input1 ins);
              A.eqCharOption "end of stream" (NONE, TextIO.input1 ins);
              TextIO.closeIn ins
            end),

          Case ("inputN takes at most what is asked for", fn () =>
            let
              val ins = TextIO.openString "abcde"
            in
              A.eqString "exact" ("ab", TextIO.inputN (ins, 2));
              A.eqString "more than remains" ("cde", TextIO.inputN (ins, 99));
              A.eqString "nothing left" ("", TextIO.inputN (ins, 1));
              TextIO.closeIn ins
            end),

          Case ("inputN of zero characters", fn () =>
            let
              val ins = TextIO.openString "abc"
            in
              A.eqString "empty" ("", TextIO.inputN (ins, 0));
              A.eqString "the stream did not advance" ("abc", TextIO.inputAll ins);
              TextIO.closeIn ins
            end),

          Case ("inputAll drains the stream", fn () =>
            let
              val ins = TextIO.openString "abc"
            in
              A.eqString "everything" ("abc", TextIO.inputAll ins);
              A.eqString "and then nothing" ("", TextIO.inputAll ins);
              TextIO.closeIn ins
            end),

          (* inputLine keeps the terminator, and supplies one for a final
           * unterminated line. *)
          Case ("inputLine keeps the newline", fn () =>
            let
              val ins = TextIO.openString "ab\ncd\n"
            in
              A.eqStringOption "first" (SOME "ab\n", TextIO.inputLine ins);
              A.eqStringOption "second" (SOME "cd\n", TextIO.inputLine ins);
              A.eqStringOption "end" (NONE, TextIO.inputLine ins);
              TextIO.closeIn ins
            end),

          Case ("a final unterminated line still gets a newline", fn () =>
            let
              val ins = TextIO.openString "ab\ncd"
            in
              A.eqStringOption "first" (SOME "ab\n", TextIO.inputLine ins);
              A.eqStringOption "last" (SOME "cd\n", TextIO.inputLine ins);
              A.eqStringOption "end" (NONE, TextIO.inputLine ins);
              TextIO.closeIn ins
            end),

          Case ("an empty stream has no lines", fn () =>
            let
              val ins = TextIO.openString ""
            in
              A.eqStringOption "none" (NONE, TextIO.inputLine ins);
              TextIO.closeIn ins
            end),

          Case ("an empty line is a lone newline", fn () =>
            let
              val ins = TextIO.openString "\n"
            in
              A.eqStringOption "just the terminator"
                (SOME "\n", TextIO.inputLine ins);
              A.eqStringOption "end" (NONE, TextIO.inputLine ins);
              TextIO.closeIn ins
            end),

          Case ("lookahead does not consume", fn () =>
            let
              val ins = TextIO.openString "ab"
            in
              A.eqCharOption "peek" (SOME #"a", TextIO.lookahead ins);
              A.eqCharOption "peek again" (SOME #"a", TextIO.lookahead ins);
              A.eqCharOption "then read" (SOME #"a", TextIO.input1 ins);
              A.eqCharOption "next" (SOME #"b", TextIO.lookahead ins);
              TextIO.closeIn ins
            end),

          Case ("endOfStream", fn () =>
            let
              val ins = TextIO.openString "a"
            in
              A.eqBool "not yet" (false, TextIO.endOfStream ins);
              ignore (TextIO.input1 ins);
              A.eqBool "now" (true, TextIO.endOfStream ins);
              TextIO.closeIn ins
            end),

          Case ("endOfStream of an empty stream", fn () =>
            let
              val ins = TextIO.openString ""
            in
              A.eqBool "immediately" (true, TextIO.endOfStream ins);
              TextIO.closeIn ins
            end),

          Case ("closing twice is harmless", fn () =>
            let
              val ins = TextIO.openString "a"
            in
              TextIO.closeIn ins;
              A.noRaise "second close" (fn () => TextIO.closeIn ins)
            end),

          Case ("reading past a close yields nothing", fn () =>
            let
              val ins = TextIO.openString "abc"
            in
              TextIO.closeIn ins;
              A.eqString "empty" ("", TextIO.inputAll ins)
            end),

          (* "Other operations on a closed stream will behave as if the stream
           * is at end-of-stream." *)
          Case ("every read on a closed stream sees the end of it", fn () =>
            let
              val ins = TextIO.openString "abc"
            in
              TextIO.closeIn ins;
              A.eqCharOption "input1" (NONE, TextIO.input1 ins);
              A.eqCharOption "lookahead" (NONE, TextIO.lookahead ins);
              A.eqStringOption "inputLine" (NONE, TextIO.inputLine ins);
              A.eqString "input" ("", TextIO.input ins);
              A.eqString "inputN" ("", TextIO.inputN (ins, 3));
              A.eqBool "endOfStream" (true, TextIO.endOfStream ins)
            end),

          (* "After a call to input1 returning NONE to indicate an
           * end-of-stream, the input stream should be positioned after the
           * end-of-stream." *)
          Case ("input1 at the end stays at the end", fn () =>
            let
              val ins = TextIO.openString "a"
            in
              A.eqCharOption "the one character" (SOME #"a", TextIO.input1 ins);
              A.eqCharOption "then nothing" (NONE, TextIO.input1 ins);
              A.eqCharOption "and nothing again" (NONE, TextIO.input1 ins);
              A.eqString "and inputN agrees" ("", TextIO.inputN (ins, 1));
              TextIO.closeIn ins
            end),

          (* "It returns SOME(k), where 0 <= k <= n, if a call to input would
           * return immediately with at least k characters.  Note that k = 0
           * corresponds to the stream being at end-of-stream." *)
          Case ("canInput reports what can be read without blocking", fn () =>
            let
              val ins = TextIO.openString "abc"
              val empty = TextIO.openString ""
              fun check (what, strm, n) =
                case TextIO.canInput (strm, n) of
                    NONE => ()   (* an answer of "would block" is allowed *)
                  | SOME k =>
                      A.that (what ^ ": 0 <= " ^ Int.toString k ^ " <= "
                              ^ Int.toString n)
                        (0 <= k andalso k <= n)
            in
              check ("three available, asking for two", ins, 2);
              check ("three available, asking for ten", ins, 10);
              (case TextIO.canInput (empty, 1) of
                   NONE => ()
                 | SOME k =>
                     A.eqInt "an exhausted stream reports zero" (0, k));
              TextIO.closeIn ins;
              TextIO.closeIn empty
            end
            handle IO.Io { cause = IO.NonblockingNotSupported, ... } => ()),

          (* "It raises the Size exception if n < 0", for canInput, and
           * "It raises Size if n < 0" for inputN. *)
          Case ("a negative count is rejected", fn () =>
            let
              val ins = TextIO.openString "abc"
            in
              A.raises "inputN" A.isSize
                (fn () => TextIO.inputN (ins, A.hide ~1));
              (A.raises "canInput" A.isSize
                 (fn () => TextIO.canInput (ins, A.hide ~1)))
              handle IO.Io { cause = IO.NonblockingNotSupported, ... } => ();
              TextIO.closeIn ins
            end),

          (* "input ... When elements are available, it returns a vector of at
           * least one element.  When strm is at end-of-stream or is closed,
           * it returns an empty vector." *)
          Case ("input returns something, then nothing", fn () =>
            let
              val ins = TextIO.openString "abc"
              val first = TextIO.input ins
            in
              A.that "at least one character" (String.size first >= 1);
              A.that "and it is a prefix of the string"
                (String.isPrefix first "abc");
              ignore (TextIO.inputAll ins);
              A.eqString "nothing at the end" ("", TextIO.input ins);
              TextIO.closeIn ins
            end),

          (* "converts a stream-based scan function into one that works on
           * Imperative I/O streams", advancing the stream past what was
           * scanned. *)
          Case ("scanStream scans and advances the stream", fn () =>
            let
              val ins = TextIO.openString "42 rest"
            in
              A.eqIntOption "the scanned value"
                (SOME 42, TextIO.scanStream (Int.scan StringCvt.DEC) ins);
              A.eqString "and the stream moved past it"
                (" rest", TextIO.inputAll ins);
              TextIO.closeIn ins
            end),

          Case ("scanStream leaves the stream alone when it fails", fn () =>
            let
              val ins = TextIO.openString "abc"
            in
              A.eqIntOption "nothing scanned"
                (NONE, TextIO.scanStream (Int.scan StringCvt.DEC) ins);
              A.eqString "and nothing consumed" ("abc", TextIO.inputAll ins);
              TextIO.closeIn ins
            end)
        ]),

        Group ("files",
          onlyIf (C.hasFileSystem, "no file system available")
          [ Case ("a written file reads back unchanged", fn () =>
              let
                val path = withOutFile ("roundtrip.txt",
                                        fn outs => TextIO.output (outs, "hello\n"))
              in
                A.eqString "contents" ("hello\n", readWholeFile path);
                removeQuietly path
              end),

            Case ("output1 and outputSubstr", fn () =>
              let
                val path =
                  withOutFile ("pieces.txt",
                               fn outs =>
                                 (TextIO.output1 (outs, #"a");
                                  TextIO.outputSubstr
                                    (outs, Substring.substring ("xbcy", 1, 2))))
              in
                A.eqString "contents" ("abc", readWholeFile path);
                removeQuietly path
              end),

            Case ("openAppend adds to the end", fn () =>
              let
                val path = withOutFile ("append.txt",
                                        fn outs => TextIO.output (outs, "one\n"))
                val outs = TextIO.openAppend path
              in
                TextIO.output (outs, "two\n");
                TextIO.closeOut outs;
                A.eqString "both" ("one\ntwo\n", readWholeFile path);
                removeQuietly path
              end),

            Case ("openOut truncates an existing file", fn () =>
              let
                val path = withOutFile ("truncate.txt",
                                        fn outs => TextIO.output (outs, "longer text"))
                val outs = TextIO.openOut path
              in
                TextIO.output (outs, "hi");
                TextIO.closeOut outs;
                A.eqString "replaced" ("hi", readWholeFile path);
                removeQuietly path
              end),

            Case ("reading a file line by line", fn () =>
              let
                val path = withOutFile ("lines.txt",
                                        fn outs => TextIO.output (outs, "a\nb\nc\n"))
                val ins = TextIO.openIn path
                val got = readAllLines ins
              in
                TextIO.closeIn ins;
                A.eqStringList "lines" (["a\n", "b\n", "c\n"], got);
                removeQuietly path
              end),

            (* The Basis wraps the underlying system error in IO.Io rather
             * than letting OS.SysErr escape. *)
            Case ("opening a file that does not exist", fn () =>
              A.raises "no such file" A.isIo
                (fn () => TextIO.openIn (scratchFile "definitely-absent-file"))),

            Case ("the file system agrees that the file is gone", fn () =>
              let
                val path = withOutFile ("transient.txt",
                                        fn outs => TextIO.output (outs, "x"))
              in
                A.eqBool "exists" (true, OS.FileSys.access (path, []));
                OS.FileSys.remove path;
                A.eqBool "removed" (false, OS.FileSys.access (path, []))
              end),

            (* "A write attempt on a closed outstream will cause the
             * exception Io{cause=ClosedStream,...} to be raised." *)
            Case ("writing to a closed stream reports a closed stream",
              fn () =>
                let
                  val () = ensureScratch ()
                  val path = scratchFile "closed-out.txt"
                  val outs = TextIO.openOut path
                  val () = TextIO.closeOut outs
                  fun isClosed (IO.Io { cause = IO.ClosedStream, ... }) = true
                    | isClosed _ = false
                in
                  A.raises "output" isClosed
                    (fn () => TextIO.output (outs, "x"));
                  A.raises "output1" isClosed
                    (fn () => TextIO.output1 (outs, #"x"));
                  A.noRaise "closing twice" (fn () => TextIO.closeOut outs);
                  removeQuietly path
                end),

            Case ("fileSize agrees with what was written", fn () =>
              let
                val path = withOutFile ("size.txt",
                                        fn outs => TextIO.output (outs, "12345"))
              in
                A.eqBy (op =, Position.toString) "five bytes"
                  (Position.fromInt 5, OS.FileSys.fileSize path);
                removeQuietly path
              end)
          ]),

        Group ("laws",
        [ P.forAll ("inputAll returns the whole string", str, showS,
                    fn s =>
                      let
                        val ins = TextIO.openString s
                        val got = TextIO.inputAll ins
                      in
                        TextIO.closeIn ins;
                        got = s
                      end),

          P.forAll ("reading one character at a time reconstructs the string",
                    str, showS,
                    fn s =>
                      let
                        val ins = TextIO.openString s
                        fun drain acc =
                          case TextIO.input1 ins of
                              NONE => List.rev acc
                            | SOME c => drain (c :: acc)
                        val got = String.implode (drain [])
                      in
                        TextIO.closeIn ins;
                        got = s
                      end),

          P.forAll ("inputN of one is input1", str, showS,
                    fn s =>
                      let
                        val ins = TextIO.openString s
                        val got = TextIO.inputN (ins, 1)
                      in
                        TextIO.closeIn ins;
                        got = (if s = "" then "" else String.substring (s, 0, 1))
                      end),

          P.forAll ("splitting at any point and rejoining is the identity",
                    G.pair (str, G.int (0, 20)), Show.pair (showS, Show.int),
                    fn (s, k) =>
                      let
                        val ins = TextIO.openString s
                        val a = TextIO.inputN (ins, k)
                        val b = TextIO.inputAll ins
                      in
                        TextIO.closeIn ins;
                        a ^ b = s
                      end),

          P.forAll ("concatenating the lines rebuilds the text",
                    lines, Show.list showS,
                    fn ls =>
                      let
                        (* Every line is newline-terminated, so the text has an
                         * unambiguous decomposition. *)
                        val text = String.concat (List.map (fn l => l ^ "\n") ls)
                        val ins = TextIO.openString text
                        val got = readAllLines ins
                      in
                        TextIO.closeIn ins;
                        String.concat got = text
                      end),

          P.forAll ("every line but the last ends with a newline",
                    lines, Show.list showS,
                    fn ls =>
                      let
                        val text = String.concat (List.map (fn l => l ^ "\n") ls)
                        val ins = TextIO.openString text
                        val got = readAllLines ins
                      in
                        TextIO.closeIn ins;
                        List.all (fn l => String.isSuffix "\n" l) got
                      end),

          P.forAll ("lookahead agrees with the next character read", str, showS,
                    fn s =>
                      let
                        val ins = TextIO.openString s
                        val peeked = TextIO.lookahead ins
                        val taken = TextIO.input1 ins
                      in
                        TextIO.closeIn ins;
                        peeked = taken
                      end),

          P.forAll ("endOfStream is true exactly when the string is exhausted",
                    str, showS,
                    fn s =>
                      let
                        val ins = TextIO.openString s
                        val atStart = TextIO.endOfStream ins
                        val _ = TextIO.inputAll ins
                        val atEnd = TextIO.endOfStream ins
                      in
                        TextIO.closeIn ins;
                        atStart = (s = "") andalso atEnd
                      end)
        ])
      ])
  end
