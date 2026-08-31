(* Tests for the IO structure and the two required PrimIO instances.
 *
 * IO itself is only exceptions and a datatype, but they are the vocabulary
 * every stream operation reports failure in, so their names and shapes matter.
 * TextPrimIO and BinPrimIO are the layer underneath the stream structures;
 * openVector makes them testable without touching a file system.
 *)

functor IOTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    fun bufferModeName IO.NO_BUF = "NO_BUF"
      | bufferModeName IO.LINE_BUF = "LINE_BUF"
      | bufferModeName IO.BLOCK_BUF = "BLOCK_BUF"

    val eqBufferMode = A.eqBy (op =, bufferModeName)

    (* Pull everything a reader will give, one chunk at a time. *)
    fun drainText rd =
      let
        val TextPrimIO.RD { readVec, ... } = rd
        val read = valOf readVec
        fun loop acc =
          let val chunk = read 3
          in if chunk = "" then String.concat (List.rev acc)
             else loop (chunk :: acc)
          end
      in
        loop []
      end

    val str = G.printableString
    val showS = Show.string

    val suite = Group ("IO",
      [ Group ("exceptions",
        [ Case ("Io carries a name, a function and a cause", fn () =>
            let
              val e = IO.Io { name = "thefile", function = "openIn",
                              cause = Fail "why" }
            in
              A.eqString "exnName" ("Io", exnName e);
              case e of
                  IO.Io { name, function, cause } =>
                    (A.eqString "name" ("thefile", name);
                     A.eqString "function" ("openIn", function);
                     A.eqString "cause" ("Fail", exnName cause))
                | _ => A.fail "Io did not match its own pattern"
            end),

          Case ("the stream exceptions exist and are distinct", fn () =>
            let
              val names = List.map exnName
                            [ IO.BlockingNotSupported,
                              IO.NonblockingNotSupported,
                              IO.RandomAccessNotSupported,
                              IO.ClosedStream ]
              fun distinct [] = true
                | distinct (x :: xs) =
                    not (List.exists (fn y => y = x) xs) andalso distinct xs
            in
              A.eqStringList "the specified names"
                (["BlockingNotSupported", "NonblockingNotSupported",
                  "RandomAccessNotSupported", "ClosedStream"], names);
              A.that "all four are distinct" (distinct names)
            end),

          Case ("a raised IO exception can be caught by its own pattern",
            fn () =>
              A.raises "ClosedStream"
                (fn IO.ClosedStream => true | _ => false)
                (fn () => raise IO.ClosedStream))
        ]),

        Group ("buffer modes",
        [ Case ("the three modes are distinct", fn () =>
            (A.that "NO_BUF is not LINE_BUF" (IO.NO_BUF <> IO.LINE_BUF);
             A.that "LINE_BUF is not BLOCK_BUF" (IO.LINE_BUF <> IO.BLOCK_BUF);
             A.that "NO_BUF is not BLOCK_BUF" (IO.NO_BUF <> IO.BLOCK_BUF))),

          Case ("a buffer mode can be matched", fn () =>
            eqBufferMode "round trip through a case"
              (IO.LINE_BUF,
               case IO.LINE_BUF of
                   IO.NO_BUF => IO.NO_BUF
                 | IO.LINE_BUF => IO.LINE_BUF
                 | IO.BLOCK_BUF => IO.BLOCK_BUF))
        ]),

        Group ("TextPrimIO",
        [ Case ("openVector produces a reader over the vector", fn () =>
            let
              val rd = TextPrimIO.openVector "abcde"
              val TextPrimIO.RD { name, chunkSize, readVec, ... } = rd
            in
              A.that "the reader is named" (String.size name >= 0);
              A.that "the chunk size is positive" (chunkSize > 0);
              A.that "readVec is provided" (isSome readVec)
            end),

          Case ("reading consumes the vector in order", fn () =>
            let
              val TextPrimIO.RD { readVec, ... } = TextPrimIO.openVector "abcde"
              val read = valOf readVec
            in
              A.eqString "first three" ("abc", read 3);
              A.eqString "the rest" ("de", read 3);
              A.eqString "then nothing" ("", read 3);
              A.eqString "and nothing again" ("", read 3)
            end),

          Case ("reading zero characters yields the empty vector", fn () =>
            let
              val TextPrimIO.RD { readVec, ... } = TextPrimIO.openVector "abc"
            in
              A.eqString "empty" ("", valOf readVec 0)
            end),

          Case ("a reader over the empty vector is immediately exhausted",
            fn () =>
              A.eqString "nothing to read"
                ("", drainText (TextPrimIO.openVector ""))),

          Case ("close does not raise", fn () =>
            let
              val TextPrimIO.RD { close, ... } = TextPrimIO.openVector "abc"
            in
              A.noRaise "close" close
            end),

          Case ("nullRd reads nothing at all", fn () =>
            let
              val TextPrimIO.RD { readVec, close, ... } = TextPrimIO.nullRd ()
            in
              A.eqString "empty" ("", valOf readVec 10);
              A.noRaise "close" close
            end),

          Case ("nullWr accepts and discards output", fn () =>
            let
              val TextPrimIO.WR { writeVec, close, ... } = TextPrimIO.nullWr ()
            in
              A.that "writeVec is provided" (isSome writeVec);
              A.noRaise "writing to it"
                (fn () => valOf writeVec (CharVectorSlice.full "abc"));
              A.noRaise "close" close
            end),

          (* augmentReader fills in the reading operations an underlying reader
           * did not supply, deriving them from the ones it did. *)
          Case ("augmentReader supplies the array-based operations", fn () =>
            let
              val TextPrimIO.RD { readArr, readVec, ... } =
                TextPrimIO.augmentReader (TextPrimIO.openVector "abcde")
            in
              A.that "readVec is still there" (isSome readVec);
              A.that "readArr is now available" (isSome readArr)
            end),

          Case ("an augmented reader still reads the same characters", fn () =>
            A.eqString "contents"
              ("abcde",
               drainText (TextPrimIO.augmentReader
                            (TextPrimIO.openVector "abcde")))),

          Case ("augmentWriter supplies the array-based operations", fn () =>
            let
              val TextPrimIO.WR { writeArr, writeVec, ... } =
                TextPrimIO.augmentWriter (TextPrimIO.nullWr ())
            in
              A.that "writeVec is still there" (isSome writeVec);
              A.that "writeArr is now available" (isSome writeArr)
            end),

          (* "close ... Further operations on the reader (besides close and
           * getPos) raise IO.ClosedStream."  The IO Discussion says the
           * opposite about the same call -- "the imperative, stream, and
           * primitive I/O modules will never raise a bare ... ClosedStream
           * exception; these exceptions are only used in the cause field of
           * the Io exception" -- so an Io carrying ClosedStream as its cause
           * is accepted as readily as the bare exception. *)
          Case ("a closed reader refuses to read", fn () =>
            let
              val rd as TextPrimIO.RD { readVec, close, ... } =
                TextPrimIO.openVector "abcde"
              fun isClosed IO.ClosedStream = true
                | isClosed (IO.Io { cause = IO.ClosedStream, ... }) = true
                | isClosed _ = false
            in
              close ();
              A.noRaise "closing twice" close;
              A.raises "readVec after closing" isClosed
                (fn () => valOf readVec 1)
            end),

          Case ("a closed writer refuses to write", fn () =>
            let
              val TextPrimIO.WR { writeVec, close, ... } = TextPrimIO.nullWr ()
              fun isClosed IO.ClosedStream = true
                | isClosed (IO.Io { cause = IO.ClosedStream, ... }) = true
                | isClosed _ = false
            in
              close ();
              A.noRaise "closing twice" close;
              A.raises "writeVec after closing" isClosed
                (fn () => valOf writeVec (CharVectorSlice.full "abc"))
            end),

          (* "readArr(slice) ... reads upto k elements into the array slice
           * slice, where k is the size of the slice.  This function returns
           * the number of elements actually read ... If no elements remain
           * before the end-of-stream, it returns 0 (this function also
           * returns 0 when slice is empty)." *)
          Case ("readArr fills an array slice and reports how much it read",
            fn () =>
              let
                val TextPrimIO.RD { readArr, ... } =
                  TextPrimIO.augmentReader (TextPrimIO.openVector "abcde")
                val read = valOf readArr
                val arr = CharArray.array (3, #"-")
                val n = read (CharArraySlice.full arr)
              in
                A.that "at least one element" (n >= 1 andalso n <= 3);
                A.eqString "and they are the first ones"
                  (String.substring ("abcde", 0, n),
                   CharArraySlice.vector
                     (CharArraySlice.slice (arr, 0, SOME n)));
                A.eqInt "an empty slice reads nothing"
                  (0, read (CharArraySlice.slice (arr, 0, SOME 0)));
                (* Drain, then confirm the end-of-stream answer. *)
                let
                  fun drain () =
                    if read (CharArraySlice.full arr) = 0 then ()
                    else drain ()
                in
                  drain ();
                  A.eqInt "nothing left" (0, read (CharArraySlice.full arr))
                end
              end),

          (* "avail() returns the number of bytes available on the "device",
           * or NONE if it cannot be determined." *)
          Case ("avail reports what is left, or that it cannot tell", fn () =>
            let
              val TextPrimIO.RD { avail, readVec, ... } =
                TextPrimIO.openVector "abcde"
              val before' = avail ()
              val _ = valOf readVec 2
              val after = avail ()
            in
              case (before', after) of
                  (NONE, _) => ()   (* undeterminable is allowed *)
                | (SOME a, NONE) =>
                    A.that "a count is not negative" (a >= 0)
                | (SOME a, SOME b) =>
                    (A.that "the count is not negative" (a >= 0);
                     A.that "and reading does not increase it" (b <= a))
            end),

          (* "writeVec(slice) ... writes the elements from the vector slice
           * slice to the output device and returns the number of elements
           * actually written." *)
          Case ("a write reports how many elements it took", fn () =>
            let
              val TextPrimIO.WR { writeVec, writeArr, ... } =
                TextPrimIO.augmentWriter (TextPrimIO.nullWr ())
              val n = valOf writeVec (CharVectorSlice.full "abc")
              val arr = CharArray.fromList [#"x", #"y"]
              val m = valOf writeArr (CharArraySlice.full arr)
            in
              A.that "no more than was offered" (n >= 0 andalso n <= 3);
              A.that "and the same for an array" (m >= 0 andalso m <= 2)
            end),

          (* "setPos(i) ... moves to position i in file", so re-reading from a
           * saved position gives the same elements again. *)
          Case ("a saved position can be returned to", fn () =>
            let
              val TextPrimIO.RD { getPos, setPos, readVec, endPos, ... } =
                TextPrimIO.openVector "abcde"
            in
              case (getPos, setPos) of
                  (SOME get, SOME set) =>
                    let
                      val start = get ()
                      val first = valOf readVec 3
                    in
                      set start;
                      A.eqString "the same elements come back"
                        (first, valOf readVec 3);
                      case endPos of
                          NONE => ()
                        | SOME atEnd =>
                            A.eqOrder "the end is not before the start"
                              (LESS, TextPrimIO.compare (start, atEnd ()))
                    end
                | _ => ()   (* random access is optional *)
            end),

          Case ("positions can be read and compared", fn () =>
            let
              val TextPrimIO.RD { getPos, readVec, ... } =
                TextPrimIO.openVector "abcde"
            in
              case getPos of
                  NONE => ()   (* a reader need not support positions *)
                | SOME get =>
                    let
                      val start = get ()
                      val _ = valOf readVec 2
                      val later = get ()
                    in
                      A.eqOrder "a position equals itself"
                        (EQUAL, TextPrimIO.compare (start, start));
                      A.eqOrder "reading moves the position forward"
                        (LESS, TextPrimIO.compare (start, later))
                    end
            end)
        ]),

        Group ("BinPrimIO",
        [ Case ("openVector produces a reader over the bytes", fn () =>
            let
              val v = Word8Vector.fromList
                        (List.map Word8.fromInt [1, 2, 3, 4, 5])
              val BinPrimIO.RD { readVec, chunkSize, ... } =
                BinPrimIO.openVector v
              val read = valOf readVec
              fun toInts w = List.map Word8.toInt (Word8Vector.foldr (op ::) [] w)
            in
              A.that "the chunk size is positive" (chunkSize > 0);
              A.eqIntList "first three" ([1, 2, 3], toInts (read 3));
              A.eqIntList "the rest" ([4, 5], toInts (read 3));
              A.eqIntList "then nothing" ([], toInts (read 3))
            end),

          Case ("augmentReader and augmentWriter supply the array operations",
            fn () =>
              let
                val v = Word8Vector.fromList
                          (List.map Word8.fromInt [1, 2, 3])
                val BinPrimIO.RD { readArr, readVec, ... } =
                  BinPrimIO.augmentReader (BinPrimIO.openVector v)
                val BinPrimIO.WR { writeArr, writeVec, ... } =
                  BinPrimIO.augmentWriter (BinPrimIO.nullWr ())
              in
                A.that "readVec survives" (isSome readVec);
                A.that "readArr is now available" (isSome readArr);
                A.that "writeVec survives" (isSome writeVec);
                A.that "writeArr is now available" (isSome writeArr)
              end),

          Case ("an augmented byte reader reads the same bytes", fn () =>
            let
              val v = Word8Vector.fromList (List.map Word8.fromInt [1, 2, 3])
              val BinPrimIO.RD { readVec, ... } =
                BinPrimIO.augmentReader (BinPrimIO.openVector v)
            in
              A.eqIntList "contents"
                ([1, 2, 3],
                 List.map Word8.toInt
                          (Word8Vector.foldr (op ::) [] (valOf readVec 10)))
            end),

          Case ("byte positions can be compared", fn () =>
            let
              val v = Word8Vector.fromList (List.map Word8.fromInt [1, 2, 3])
              val BinPrimIO.RD { getPos, readVec, ... } = BinPrimIO.openVector v
            in
              case getPos of
                  NONE => ()   (* positions are optional *)
                | SOME get =>
                    let
                      val start = get ()
                      val _ = valOf readVec 2
                      val later = get ()
                    in
                      A.eqOrder "a position equals itself"
                        (EQUAL, BinPrimIO.compare (start, start));
                      A.eqOrder "reading moves the position forward"
                        (LESS, BinPrimIO.compare (start, later))
                    end
            end),

          Case ("a closed byte reader refuses to read", fn () =>
            let
              val BinPrimIO.RD { readVec, close, ... } =
                BinPrimIO.openVector (Word8Vector.fromList
                                        [Word8.fromInt 1, Word8.fromInt 2])
              fun isClosed IO.ClosedStream = true
                | isClosed (IO.Io { cause = IO.ClosedStream, ... }) = true
                | isClosed _ = false
            in
              close ();
              A.noRaise "closing twice" close;
              A.raises "readVec after closing" isClosed
                (fn () => valOf readVec 1)
            end),

          Case ("nullRd and nullWr exist for bytes too", fn () =>
            let
              val BinPrimIO.RD { readVec, ... } = BinPrimIO.nullRd ()
              val BinPrimIO.WR { writeVec, close, ... } = BinPrimIO.nullWr ()
            in
              A.eqInt "nothing to read" (0, Word8Vector.length (valOf readVec 10));
              A.noRaise "writing"
                (fn () => valOf writeVec
                            (Word8VectorSlice.full
                               (Word8Vector.fromList [Word8.fromInt 1])));
              A.noRaise "close" close
            end)
        ]),

        Group ("laws",
        [ P.forAll ("a reader over a string yields that string back",
                    str, showS,
                    fn s => drainText (TextPrimIO.openVector s) = s),

          P.forAll ("augmenting a reader does not change what it reads",
                    str, showS,
                    fn s =>
                      drainText (TextPrimIO.augmentReader
                                   (TextPrimIO.openVector s)) = s),

          P.forAll ("a single read of the whole length returns everything",
                    str, showS,
                    fn s =>
                      let
                        val TextPrimIO.RD { readVec, ... } =
                          TextPrimIO.openVector s
                      in
                        valOf readVec (String.size s) = s
                      end),

          P.forAll ("nullRd is empty whatever is asked of it",
                    G.int (0, 50), Show.int,
                    fn n =>
                      let
                        val TextPrimIO.RD { readVec, ... } = TextPrimIO.nullRd ()
                      in
                        valOf readVec n = ""
                      end)
        ])
      ])
  end
