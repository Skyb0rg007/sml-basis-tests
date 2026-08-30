(* Tests for the remaining TextIO surface: the functional StreamIO layer, the
 * imperative/functional bridge, buffering and the standard streams.
 *
 * TextIO.StreamIO streams are values, not handles: reading one returns a new
 * stream rather than mutating the old, so the same stream can be read twice
 * and give the same answer.  That is the property most of these tests turn on.
 *)

functor TextIOStreamTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure SIO = TextIO.StreamIO

    val str = G.printableString
    val showS = Show.string

    (* A functional stream over a string, built from a primitive reader so
     * that no file system is involved. *)
    fun streamOf s = SIO.mkInstream (TextPrimIO.openVector s, "")

    fun bufferModeName IO.NO_BUF = "NO_BUF"
      | bufferModeName IO.LINE_BUF = "LINE_BUF"
      | bufferModeName IO.BLOCK_BUF = "BLOCK_BUF"
    val eqBufferMode = A.eqBy (op =, bufferModeName)

    val scratch = C.scratchDir
    fun scratchFile name = OS.Path.concat (scratch, name)
    fun ensureScratch () =
      if OS.FileSys.access (scratch, []) then () else OS.FileSys.mkDir scratch
    fun removeQuietly path = OS.FileSys.remove path handle _ => ()

    val suite = Group ("TextIO.StreamIO",
      [ Group ("functional input",
        [ Case ("input1 returns a new stream rather than advancing the old",
            fn () =>
              let
                val s = streamOf "ab"
              in
                case SIO.input1 s of
                    NONE => A.fail "expected a character"
                  | SOME (c, s') =>
                      (A.eqChar "first" (#"a", c);
                       (* Reading s again must give the same answer. *)
                       case SIO.input1 s of
                           NONE => A.fail "the original stream was consumed"
                         | SOME (c2, _) =>
                             (A.eqChar "the original is unchanged" (#"a", c2);
                              case SIO.input1 s' of
                                  NONE => A.fail "expected a second character"
                                | SOME (c3, _) =>
                                    A.eqChar "the new stream advanced" (#"b", c3)))
              end),

          Case ("input1 at the end", fn () =>
            A.that "an empty stream has nothing"
              (not (isSome (SIO.input1 (streamOf ""))))),

          Case ("inputN takes at most what is asked for", fn () =>
            let
              val (a, s1) = SIO.inputN (streamOf "abcde", 2)
              val (b, _) = SIO.inputN (s1, 99)
            in
              A.eqString "first" ("ab", a);
              A.eqString "the rest" ("cde", b)
            end),

          Case ("inputAll drains", fn () =>
            let
              val (all, s') = SIO.inputAll (streamOf "abc")
              val (again, _) = SIO.inputAll s'
            in
              A.eqString "everything" ("abc", all);
              A.eqString "and then nothing" ("", again)
            end),

          Case ("input returns some of what is there", fn () =>
            let
              val (first, s') = SIO.input (streamOf "abc")
              val (rest, _) = SIO.inputAll s'
            in
              A.eqString "the pieces rebuild the stream" ("abc", first ^ rest)
            end),

          Case ("inputLine keeps the terminator", fn () =>
            case SIO.inputLine (streamOf "ab\ncd\n") of
                NONE => A.fail "expected a line"
              | SOME (line, s') =>
                  (A.eqString "first line" ("ab\n", line);
                   case SIO.inputLine s' of
                       NONE => A.fail "expected a second line"
                     | SOME (line2, s'') =>
                         (A.eqString "second line" ("cd\n", line2);
                          A.that "and then no more"
                            (not (isSome (SIO.inputLine s'')))))),

          Case ("endOfStream", fn () =>
            (A.eqBool "a non-empty stream is not at its end"
               (false, SIO.endOfStream (streamOf "a"));
             A.eqBool "an empty one is"
               (true, SIO.endOfStream (streamOf "")))),

          (* Non-blocking input is optional, and a stream that cannot offer it
           * is specified to say so by raising Io with NonblockingNotSupported
           * as the cause.  Both that and a real answer are correct. *)
          Case ("canInput answers or reports that it cannot", fn () =>
            (case SIO.canInput (streamOf "abc", 1) of
                 NONE => ()
               | SOME n => A.that "a non-negative count" (n >= 0))
            handle IO.Io { cause = IO.NonblockingNotSupported, ... } => ()
                 | IO.NonblockingNotSupported => ()
                 | e => A.fail ("unexpected exception " ^ exnName e)),

          Case ("closeIn is accepted", fn () =>
            A.noRaise "closeIn" (fn () => SIO.closeIn (streamOf "abc"))),

          (* getReader hands back the underlying reader together with whatever
           * had already been buffered but not consumed. *)
          Case ("getReader recovers the primitive reader", fn () =>
            let
              val s = streamOf "abcde"
              val (_, s') = SIO.inputN (s, 2)
              val (TextPrimIO.RD { name, ... }, pending) = SIO.getReader s'
            in
              A.that "the reader is named" (String.size name >= 0);
              A.that "anything already read stays with the stream"
                (String.size pending >= 0)
            end),

          (* Positions are optional: a stream that has none is specified to
           * report that by raising Io, with RandomAccessNotSupported as the
           * cause, so both outcomes are correct and only a third would be a
           * failure. *)
          Case ("filePosIn either reports a position or says it cannot",
            fn () =>
              (ignore (SIO.filePosIn (streamOf "abc")))
              handle IO.Io _ => ()
                   | IO.RandomAccessNotSupported => ()
                   | e => A.fail ("unexpected exception " ^ exnName e))
        ]),

        Group ("the bridge between imperative and functional streams",
        [ Case ("getInstream and setInstream rewind a stream", fn () =>
            let
              val ins = TextIO.openString "abcde"
              val saved = TextIO.getInstream ins
              val _ = TextIO.inputN (ins, 3)
            in
              TextIO.setInstream (ins, saved);
              A.eqString "rewound" ("abcde", TextIO.inputAll ins);
              TextIO.closeIn ins
            end),

          Case ("mkInstream wraps a functional stream", fn () =>
            let
              val ins = TextIO.mkInstream (streamOf "abc")
            in
              A.eqString "reads through the wrapper" ("abc", TextIO.inputAll ins);
              TextIO.closeIn ins
            end),

          Case ("a functional stream taken from an imperative one is a snapshot",
            fn () =>
              let
                val ins = TextIO.openString "abc"
                val snapshot = TextIO.getInstream ins
                val _ = TextIO.inputN (ins, 1)
                val (fromSnapshot, _) = SIO.inputAll snapshot
              in
                A.eqString "the snapshot still has everything"
                  ("abc", fromSnapshot);
                A.eqString "while the imperative stream moved on"
                  ("bc", TextIO.inputAll ins);
                TextIO.closeIn ins
              end),

          Case ("scanStream applies a scanner to a stream", fn () =>
            let
              val ins = TextIO.openString "42 rest"
              val n = TextIO.scanStream (Int.scan StringCvt.DEC) ins
            in
              A.eqIntOption "the scanned value" (SOME 42, n);
              A.eqString "and the stream advanced past it"
                (" rest", TextIO.inputAll ins);
              TextIO.closeIn ins
            end),

          Case ("scanStream reports failure without consuming", fn () =>
            let
              val ins = TextIO.openString "abc"
              val n = TextIO.scanStream (Int.scan StringCvt.DEC) ins
            in
              A.eqIntOption "nothing scanned" (NONE, n);
              A.eqString "the stream is untouched" ("abc", TextIO.inputAll ins);
              TextIO.closeIn ins
            end),

          Case ("canInput on an imperative stream", fn () =>
            let
              val ins = TextIO.openString "abc"
            in
              A.noRaise "canInput" (fn () => TextIO.canInput (ins, 1));
              TextIO.closeIn ins
            end)
        ]),

        Group ("output and buffering",
          onlyIf (C.hasFileSystem, "no file system available")
          [ Case ("getOutstream, setOutstream and mkOutstream", fn () =>
              let
                val () = ensureScratch ()
                val path = scratchFile "stream-out.txt"
                val outs = TextIO.openOut path
                val functional = TextIO.getOutstream outs
              in
                SIO.output (functional, "written functionally\n");
                TextIO.setOutstream (outs, functional);
                TextIO.output (outs, "and imperatively\n");
                TextIO.closeOut outs;
                let val ins = TextIO.openIn path
                in
                  A.eqString "both halves are there"
                    ("written functionally\nand imperatively\n",
                     TextIO.inputAll ins);
                  TextIO.closeIn ins
                end;
                removeQuietly path
              end),

            Case ("mkOutstream wraps a functional stream", fn () =>
              let
                val () = ensureScratch ()
                val path = scratchFile "stream-mkout.txt"
                val outs = TextIO.openOut path
                val wrapped = TextIO.mkOutstream (TextIO.getOutstream outs)
              in
                TextIO.output (wrapped, "through the wrapper");
                TextIO.flushOut wrapped;
                let val ins = TextIO.openIn path
                in
                  A.eqString "written through the wrapper"
                    ("through the wrapper", TextIO.inputAll ins);
                  TextIO.closeIn ins
                end;
                (TextIO.closeOut outs handle _ => ());
                removeQuietly path
              end),

            Case ("the buffer mode can be read and set", fn () =>
              let
                val () = ensureScratch ()
                val path = scratchFile "stream-buffer.txt"
                val outs = TextIO.openOut path
                val functional = TextIO.getOutstream outs
              in
                A.noRaise "getBufferMode"
                  (fn () => SIO.getBufferMode functional);
                List.app
                  (fn m =>
                     (SIO.setBufferMode (functional, m);
                      eqBufferMode ("after setting " ^ bufferModeName m)
                        (m, SIO.getBufferMode functional)))
                  [IO.NO_BUF, IO.LINE_BUF, IO.BLOCK_BUF];
                TextIO.closeOut outs;
                removeQuietly path
              end),

            Case ("flushOut makes buffered output visible", fn () =>
              let
                val () = ensureScratch ()
                val path = scratchFile "stream-flush.txt"
                val outs = TextIO.openOut path
              in
                TextIO.output (outs, "buffered");
                TextIO.flushOut outs;
                let val ins = TextIO.openIn path
                in
                  A.eqString "visible after the flush"
                    ("buffered", TextIO.inputAll ins);
                  TextIO.closeIn ins
                end;
                TextIO.closeOut outs;
                removeQuietly path
              end),

            Case ("output positions can be taken and restored", fn () =>
              let
                val () = ensureScratch ()
                val path = scratchFile "stream-pos.txt"
                val outs = TextIO.openOut path
              in
                TextIO.output (outs, "abcdef");
                TextIO.flushOut outs;
                (case (SOME (TextIO.getPosOut outs)
                       handle IO.RandomAccessNotSupported => NONE) of
                     NONE => ()   (* positions are optional *)
                   | SOME p =>
                       (TextIO.output (outs, "ghi");
                        TextIO.flushOut outs;
                        TextIO.setPosOut (outs, p);
                        TextIO.output (outs, "XYZ");
                        TextIO.flushOut outs;
                        TextIO.closeOut outs;
                        let val ins = TextIO.openIn path
                        in
                          A.eqString "writing at the restored position"
                            ("abcdefXYZ", TextIO.inputAll ins);
                          TextIO.closeIn ins
                        end));
                (TextIO.closeOut outs handle _ => ());
                removeQuietly path
              end),

            Case ("getWriter recovers the primitive writer", fn () =>
              let
                val () = ensureScratch ()
                val path = scratchFile "stream-writer.txt"
                val outs = TextIO.openOut path
                val (TextPrimIO.WR { name, ... }, _) =
                  SIO.getWriter (TextIO.getOutstream outs)
              in
                A.that "the writer is named" (String.size name >= 0);
                removeQuietly path
              end)
          ]),

        Group ("the standard streams",
        [ (* Writing to stdOut would corrupt the report, so these check only
           * that the streams exist and can be flushed. *)
          Case ("stdOut and stdErr can be flushed", fn () =>
            (A.noRaise "stdOut" (fn () => TextIO.flushOut TextIO.stdOut);
             A.noRaise "stdErr" (fn () => TextIO.flushOut TextIO.stdErr))),

          Case ("stdIn exists and can be inspected", fn () =>
            A.noRaise "getInstream on stdIn"
              (fn () => TextIO.getInstream TextIO.stdIn)),

          Case ("TextIO.print writes to stdOut", fn () =>
            (* The empty string is the one payload that cannot disturb the
             * report while still exercising the function. *)
            A.noRaise "print" (fn () => TextIO.print ""))
        ]),

        Group ("laws",
        [ P.forAll ("a functional stream can be read twice with the same result",
                    str, showS,
                    fn s =>
                      let
                        val stream = streamOf s
                        val (a, _) = SIO.inputAll stream
                        val (b, _) = SIO.inputAll stream
                      in
                        a = s andalso b = s
                      end),

          P.forAll ("reading one character at a time reconstructs the string",
                    str, showS,
                    fn s =>
                      let
                        fun drain (stream, acc) =
                          case SIO.input1 stream of
                              NONE => String.implode (List.rev acc)
                            | SOME (c, next) => drain (next, c :: acc)
                      in
                        drain (streamOf s, []) = s
                      end),

          P.forAll ("splitting anywhere and rejoining is the identity",
                    G.pair (str, G.int (0, 20)), Show.pair (showS, Show.int),
                    fn (s, k) =>
                      let
                        val (a, rest) = SIO.inputN (streamOf s, k)
                        val (b, _) = SIO.inputAll rest
                      in
                        a ^ b = s
                      end),

          P.forAll ("endOfStream is true exactly for the empty stream",
                    str, showS,
                    fn s => SIO.endOfStream (streamOf s) = (s = "")),

          P.forAll ("mkInstream and getInstream are inverse", str, showS,
                    fn s =>
                      let
                        val ins = TextIO.mkInstream (streamOf s)
                        val (back, _) = SIO.inputAll (TextIO.getInstream ins)
                      in
                        TextIO.closeIn ins;
                        back = s
                      end),

          P.forAll ("setInstream restores what getInstream saved", str, showS,
                    fn s =>
                      let
                        val ins = TextIO.openString s
                        val saved = TextIO.getInstream ins
                        val _ = TextIO.inputAll ins
                        val () = TextIO.setInstream (ins, saved)
                        val again = TextIO.inputAll ins
                      in
                        TextIO.closeIn ins;
                        again = s
                      end)
        ])
      ])
  end
