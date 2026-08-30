(* Tests for BinIO.
 *
 * BinIO has no openString, so the in-memory streams here are built from a
 * BinPrimIO reader over a vector.  That keeps the bulk of the tests
 * independent of the file system; only the group that opens real files is
 * gated on the configuration.
 *)

functor BinIOTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure W8V = Word8Vector

    val b = Word8.fromInt
    fun showB w = "0wx" ^ Word8.toString w
    fun toInts v = List.map Word8.toInt (W8V.foldr (op ::) [] v)
    fun ofInts ns = W8V.fromList (List.map b ns)
    val eqBytes = A.eqBy (op =, Show.intList)
    fun eqVec msg (e, a) = eqBytes msg (toInts e, toInts a)

    (* An in-memory BinIO input stream over the given bytes. *)
    fun openBytes v =
      BinIO.mkInstream
        (BinIO.StreamIO.mkInstream (BinPrimIO.openVector v, W8V.fromList []))

    val bytes = G.map ofInts (G.list (G.int (0, 255)))
    fun showBytes v = Show.intList (toInts v)

    val scratch = C.scratchDir
    fun scratchFile name = OS.Path.concat (scratch, name)
    fun ensureScratch () =
      if OS.FileSys.access (scratch, []) then () else OS.FileSys.mkDir scratch
    fun removeQuietly path = OS.FileSys.remove path handle _ => ()

    val suite = Group ("BinIO",
      [ Group ("reading from memory",
        [ Case ("input1 delivers one byte at a time", fn () =>
            let
              val ins = openBytes (ofInts [1, 2])
            in
              A.eqBy (op =, Show.option showB) "first"
                (SOME (b 1), BinIO.input1 ins);
              A.eqBy (op =, Show.option showB) "second"
                (SOME (b 2), BinIO.input1 ins);
              A.eqBy (op =, Show.option showB) "end"
                (NONE, BinIO.input1 ins);
              BinIO.closeIn ins
            end),

          Case ("inputN takes at most what is asked for", fn () =>
            let
              val ins = openBytes (ofInts [1, 2, 3, 4, 5])
            in
              eqVec "exact" (ofInts [1, 2], BinIO.inputN (ins, 2));
              eqVec "more than remains" (ofInts [3, 4, 5], BinIO.inputN (ins, 99));
              eqVec "nothing left" (ofInts [], BinIO.inputN (ins, 1));
              BinIO.closeIn ins
            end),

          Case ("inputN of zero does not advance the stream", fn () =>
            let
              val ins = openBytes (ofInts [1, 2, 3])
            in
              eqVec "empty" (ofInts [], BinIO.inputN (ins, 0));
              eqVec "still all there" (ofInts [1, 2, 3], BinIO.inputAll ins);
              BinIO.closeIn ins
            end),

          Case ("inputAll drains the stream", fn () =>
            let
              val ins = openBytes (ofInts [1, 2, 3])
            in
              eqVec "everything" (ofInts [1, 2, 3], BinIO.inputAll ins);
              eqVec "and then nothing" (ofInts [], BinIO.inputAll ins);
              BinIO.closeIn ins
            end),

          Case ("lookahead does not consume", fn () =>
            let
              val ins = openBytes (ofInts [7, 8])
            in
              A.eqBy (op =, Show.option showB) "peek"
                (SOME (b 7), BinIO.lookahead ins);
              A.eqBy (op =, Show.option showB) "peek again"
                (SOME (b 7), BinIO.lookahead ins);
              A.eqBy (op =, Show.option showB) "then read"
                (SOME (b 7), BinIO.input1 ins);
              A.eqBy (op =, Show.option showB) "next"
                (SOME (b 8), BinIO.lookahead ins);
              BinIO.closeIn ins
            end),

          Case ("endOfStream", fn () =>
            let
              val ins = openBytes (ofInts [1])
            in
              A.eqBool "not yet" (false, BinIO.endOfStream ins);
              ignore (BinIO.input1 ins);
              A.eqBool "now" (true, BinIO.endOfStream ins);
              BinIO.closeIn ins
            end),

          Case ("an empty stream is at its end immediately", fn () =>
            let
              val ins = openBytes (ofInts [])
            in
              A.eqBool "at the end" (true, BinIO.endOfStream ins);
              eqVec "nothing to read" (ofInts [], BinIO.inputAll ins);
              BinIO.closeIn ins
            end),

          Case ("input returns some of what is available", fn () =>
            let
              val ins = openBytes (ofInts [1, 2, 3])
              val first = BinIO.input ins
              val rest = BinIO.inputAll ins
            in
              eqVec "the two halves rebuild the stream"
                (ofInts [1, 2, 3], W8V.concat [first, rest]);
              BinIO.closeIn ins
            end),

          Case ("closing twice is harmless", fn () =>
            let
              val ins = openBytes (ofInts [1])
            in
              BinIO.closeIn ins;
              A.noRaise "second close" (fn () => BinIO.closeIn ins)
            end)
        ]),

        Group ("stream plumbing",
        [ Case ("getInstream and setInstream expose the functional stream",
            fn () =>
              let
                val ins = openBytes (ofInts [1, 2, 3])
                val saved = BinIO.getInstream ins
                val _ = BinIO.inputN (ins, 2)
              in
                (* Putting the saved stream back rewinds the imperative one. *)
                BinIO.setInstream (ins, saved);
                eqVec "rewound" (ofInts [1, 2, 3], BinIO.inputAll ins);
                BinIO.closeIn ins
              end),

          Case ("the functional stream reads without consuming the original",
            fn () =>
              let
                val ins = openBytes (ofInts [1, 2, 3])
                val s = BinIO.getInstream ins
              in
                case BinIO.StreamIO.input1 s of
                    NONE => A.fail "expected a byte"
                  | SOME (w, _) =>
                      (A.eqBy (op =, showB) "read through the functional stream"
                         (b 1, w);
                       (* The imperative stream has not moved. *)
                       eqVec "the imperative stream is untouched"
                         (ofInts [1, 2, 3], BinIO.inputAll ins));
                BinIO.closeIn ins
              end),

          (* As for text streams, non-blocking input is optional and the
           * specified way to decline is Io with NonblockingNotSupported. *)
          Case ("canInput answers or reports that it cannot", fn () =>
            let
              val ins = openBytes (ofInts [1, 2, 3])
            in
              (case BinIO.canInput (ins, 1) of
                   NONE => ()
                 | SOME n => A.that "a non-negative count" (n >= 0))
              handle IO.Io { cause = IO.NonblockingNotSupported, ... } => ()
                   | IO.NonblockingNotSupported => ()
                   | e => A.fail ("unexpected exception " ^ exnName e);
              BinIO.closeIn ins
            end)
        ]),

        Group ("files",
          onlyIf (C.hasFileSystem, "no file system available")
          [ Case ("bytes written to a file read back unchanged", fn () =>
              let
                val () = ensureScratch ()
                val path = scratchFile "bin-roundtrip.bin"
                val outs = BinIO.openOut path
                val payload = ofInts [0, 1, 127, 128, 255]
              in
                BinIO.output (outs, payload);
                BinIO.closeOut outs;
                let val ins = BinIO.openIn path
                in
                  eqVec "contents" (payload, BinIO.inputAll ins);
                  BinIO.closeIn ins
                end;
                removeQuietly path
              end),

            Case ("output1 writes single bytes", fn () =>
              let
                val () = ensureScratch ()
                val path = scratchFile "bin-single.bin"
                val outs = BinIO.openOut path
              in
                BinIO.output1 (outs, b 65);
                BinIO.output1 (outs, b 66);
                BinIO.closeOut outs;
                let val ins = BinIO.openIn path
                in
                  eqVec "contents" (ofInts [65, 66], BinIO.inputAll ins);
                  BinIO.closeIn ins
                end;
                removeQuietly path
              end),

            Case ("openAppend adds to the end", fn () =>
              let
                val () = ensureScratch ()
                val path = scratchFile "bin-append.bin"
                val outs = BinIO.openOut path
              in
                BinIO.output (outs, ofInts [1]);
                BinIO.closeOut outs;
                let val more = BinIO.openAppend path
                in BinIO.output (more, ofInts [2]); BinIO.closeOut more end;
                let val ins = BinIO.openIn path
                in
                  eqVec "both" (ofInts [1, 2], BinIO.inputAll ins);
                  BinIO.closeIn ins
                end;
                removeQuietly path
              end),

            Case ("flushOut does not raise", fn () =>
              let
                val () = ensureScratch ()
                val path = scratchFile "bin-flush.bin"
                val outs = BinIO.openOut path
              in
                BinIO.output (outs, ofInts [1, 2]);
                A.noRaise "flushOut" (fn () => BinIO.flushOut outs);
                BinIO.closeOut outs;
                removeQuietly path
              end),

            Case ("opening a file that does not exist", fn () =>
              A.raises "no such file" A.isIo
                (fn () => BinIO.openIn (scratchFile "absent-binary-file"))),

            (* Binary streams must not translate anything: every byte value
             * has to survive a round trip, newlines and NULs included. *)
            Case ("all 256 byte values survive a round trip", fn () =>
              let
                val () = ensureScratch ()
                val path = scratchFile "bin-all-bytes.bin"
                val payload = W8V.tabulate (256, fn i => b i)
                val outs = BinIO.openOut path
              in
                BinIO.output (outs, payload);
                BinIO.closeOut outs;
                let val ins = BinIO.openIn path
                in
                  eqVec "every byte" (payload, BinIO.inputAll ins);
                  BinIO.closeIn ins
                end;
                removeQuietly path
              end)
          ]),

        Group ("laws",
        [ P.forAll ("inputAll returns the whole vector", bytes, showBytes,
                    fn v =>
                      let
                        val ins = openBytes v
                        val got = BinIO.inputAll ins
                      in
                        BinIO.closeIn ins;
                        got = v
                      end),

          P.forAll ("reading a byte at a time reconstructs the vector",
                    bytes, showBytes,
                    fn v =>
                      let
                        val ins = openBytes v
                        fun drain acc =
                          case BinIO.input1 ins of
                              NONE => List.rev acc
                            | SOME w => drain (w :: acc)
                        val got = W8V.fromList (drain [])
                      in
                        BinIO.closeIn ins;
                        got = v
                      end),

          P.forAll ("splitting anywhere and rejoining is the identity",
                    G.pair (bytes, G.int (0, 20)),
                    Show.pair (showBytes, Show.int),
                    fn (v, k) =>
                      let
                        val ins = openBytes v
                        val a = BinIO.inputN (ins, k)
                        val c = BinIO.inputAll ins
                      in
                        BinIO.closeIn ins;
                        W8V.concat [a, c] = v
                      end),

          P.forAll ("lookahead agrees with the next byte read", bytes, showBytes,
                    fn v =>
                      let
                        val ins = openBytes v
                        val peeked = BinIO.lookahead ins
                        val taken = BinIO.input1 ins
                      in
                        BinIO.closeIn ins;
                        peeked = taken
                      end),

          P.forAll ("endOfStream is true exactly when nothing remains",
                    bytes, showBytes,
                    fn v =>
                      let
                        val ins = openBytes v
                        val atStart = BinIO.endOfStream ins
                        val _ = BinIO.inputAll ins
                        val atEnd = BinIO.endOfStream ins
                      in
                        BinIO.closeIn ins;
                        atStart = (W8V.length v = 0) andalso atEnd
                      end)
        ])
      ])
  end
