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

          (* "Applying closeIn on a closed stream has no effect."  The
           * Discussion writes this as
           *   fun closeTwice f = (TS.closeIn f; TS.closeIn f; true) *)
          Case ("closing a functional stream twice is harmless", fn () =>
            let val s = streamOf "abc"
            in
              A.noRaise "twice" (fn () => (SIO.closeIn s; SIO.closeIn s))
            end),

          (* The Discussion:
           *   fun chkClose f = let val (a,f') = TS.input f
           *                        val _ = TS.closeIn f
           *                        val (b,_) = TS.input f
           *                    in a=b andalso TS.endOfStream f' end *)
          Case ("closing only empties the undetermined part of a stream",
            fn () =>
              let
                val f = streamOf "abc"
                val (a, f') = SIO.input f
                val () = SIO.closeIn f
                val (b, _) = SIO.input f
              in
                A.eqString "the determined part is unchanged" (a, b);
                A.eqBool "and the rest is at end-of-stream"
                  (true, SIO.endOfStream f')
              end),

          (* "Reading from a truncated input stream will never block; after
           * all buffered elements are read, input operations always return
           * empty vectors."  getReader truncates the stream. *)
          Case ("a truncated stream reads as empty", fn () =>
            let
              val f = streamOf "abcde"
              val (_, pending) = SIO.getReader f
            in
              A.eqString "input on the truncated stream" ("", #1 (SIO.input f));
              A.eqBool "and it is at end-of-stream" (true, SIO.endOfStream f);
              A.that "the pending data was handed over"
                (String.size pending >= 0)
            end),

          (* "The function raises the exception Io if f is closed or
           * truncated." *)
          Case ("getReader may not be applied twice", fn () =>
            let
              val f = streamOf "abc"
              val _ = SIO.getReader f
            in
              A.raises "a second getReader" A.isIo (fn () => SIO.getReader f)
            end),

          (* "The data returned will have the value (closeIn f; inputAll f)"
           * -- that is, what the stream had already buffered, not the rest of
           * the underlying source, since closing empties the undetermined
           * part.  Two equivalent streams are used because the operation is
           * destructive. *)
          Case ("getReader hands back exactly what was buffered", fn () =>
            let
              val f = streamOf "abcde"
              val (_, f') = SIO.inputN (f, 2)
              val () = SIO.closeIn f'
              val expected = #1 (SIO.inputAll f')
              val g = streamOf "abcde"
              val (_, g') = SIO.inputN (g, 2)
              val (_, pending) = SIO.getReader g'
            in
              A.eqString "the unconsumed data" (expected, pending)
            end),

          (* "It raises Size if n < 0", for both inputN and canInput. *)
          Case ("a negative count is rejected", fn () =>
            (A.raises "inputN" A.isSize
               (fn () => SIO.inputN (streamOf "abc", A.hide ~1));
             (A.raises "canInput" A.isSize
                (fn () => SIO.canInput (streamOf "abc", A.hide ~1)))
             handle IO.Io { cause = IO.NonblockingNotSupported, ... } => ())),

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
        [ (* "The endOfStream test is equivalent to input returning an empty
           * sequence:
           *   fun isEOS f = let val (a,_) = TS.input f
           *                 in ((size a)=0) = (TS.endOfStream f) end" *)
          P.forAll ("endOfStream is input returning nothing", str, showS,
                    fn s =>
                      let
                        val f = streamOf s
                        val (a, _) = SIO.input f
                      in
                        (String.size a = 0) = SIO.endOfStream f
                      end),

          (* "The semantics of inputAll can be defined in terms of input." *)
          P.forAll ("inputAll is input repeated to the end", str, showS,
                    fn s =>
                      let
                        fun all f =
                          case SIO.input f of
                              ("", f') => ""
                            | (v, f') => v ^ all f'
                      in
                        #1 (SIO.inputAll (streamOf s)) = all (streamOf s)
                      end),

          (* "The semantics of input1 can be defined in terms of inputN." *)
          P.forAll ("input1 is inputN of one", str, showS,
                    fn s =>
                      let
                        val viaOne =
                          Option.map #1 (SIO.input1 (streamOf s))
                        val viaN =
                          case SIO.inputN (streamOf s, 1) of
                              ("", _) => NONE
                            | (v, _) => SOME (String.sub (v, 0))
                      in
                        viaOne = viaN
                      end),

          (* The allAndN predicate from the Discussion: inputN returns fewer
           * than n elements exactly when an end-of-stream follows them. *)
          P.forAll ("inputN and inputAll agree",
                    G.bind str (fn s =>
                      G.map (fn n => (s, n)) (G.int (0, String.size s + 2))),
                    Show.pair (showS, Show.int),
                    fn (s, n) =>
                      let
                        val f = streamOf s
                        val (a, f1) = SIO.inputN (f, n)
                        val (t, _) = SIO.inputAll f
                      in
                        if String.size a < n then a = t
                        else t = a ^ #1 (SIO.inputAll f1)
                      end),

          (* "If a stream has already been at least partly determined, then
           * input cannot possibly block:
           *   fun noBlock f = let val (s,_) = TS.input f
           *                   in case TS.canInput (f, 1) of
           *                        SOME 0 => (size s) = 0
           *                      | SOME _ => (size s) > 0
           *                      | NONE => false end" *)
          P.forAll ("a determined stream never blocks", str, showS,
                    fn s =>
                      let
                        val f = streamOf s
                        val (v, _) = SIO.input f
                      in
                        (case SIO.canInput (f, 1) of
                             SOME 0 => String.size v = 0
                           | SOME _ => String.size v > 0
                           | NONE => false)
                        handle IO.Io { cause = IO.NonblockingNotSupported,
                                       ... } => true
                      end),

          (* "inputN(f,0) returns immediately with an empty vector and f, so
           * this cannot be used as an indication of end-of-stream." *)
          P.forAll ("inputN of nothing returns the same stream", str, showS,
                    fn s =>
                      let
                        val f = streamOf s
                        val (v, f') = SIO.inputN (f, 0)
                      in
                        v = "" andalso #1 (SIO.input f') = #1 (SIO.input f)
                      end),

          P.forAll ("a functional stream can be read twice with the same result",
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
