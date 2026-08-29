(* Tests for StringCvt.
 *
 * The reader-based functions are polymorphic in the stream type; here they are
 * exercised over Substring.getc, which is the reader every implementation must
 * provide and which makes the residual stream inspectable.
 *)

functor StringCvtTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val str = G.asciiString
    val showS = Show.string

    (* Apply a reader-consuming function to a whole string. *)
    fun onString f s = f Substring.getc (Substring.full s)
    fun restOf ss = Substring.string ss

    val suite = Group ("StringCvt",
      [ Group ("padding",
        [ Case ("padLeft", fn () =>
            (A.eqString "pads" ("..ab", StringCvt.padLeft #"." 4 "ab");
             A.eqString "exact width" ("ab", StringCvt.padLeft #"." 2 "ab");
             A.eqString "already too long"
               ("abcd", StringCvt.padLeft #"." 2 "abcd");
             A.eqString "zero width" ("ab", StringCvt.padLeft #"." 0 "ab");
             A.eqString "negative width" ("ab", StringCvt.padLeft #"." ~1 "ab");
             A.eqString "empty string" ("...", StringCvt.padLeft #"." 3 ""))),

          Case ("padRight", fn () =>
            (A.eqString "pads" ("ab..", StringCvt.padRight #"." 4 "ab");
             A.eqString "exact width" ("ab", StringCvt.padRight #"." 2 "ab");
             A.eqString "already too long"
               ("abcd", StringCvt.padRight #"." 2 "abcd")))
        ]),

        Group ("reader combinators",
        [ Case ("splitl", fn () =>
            let
              val (taken, rest) = onString (StringCvt.splitl Char.isAlpha) "ab1cd"
            in
              A.eqString "taken" ("ab", taken);
              A.eqString "rest" ("1cd", restOf rest)
            end),

          Case ("splitl taking everything", fn () =>
            let
              val (taken, rest) = onString (StringCvt.splitl Char.isAlpha) "abcd"
            in
              A.eqString "taken" ("abcd", taken);
              A.eqString "rest" ("", restOf rest)
            end),

          Case ("splitl taking nothing", fn () =>
            let
              val (taken, rest) = onString (StringCvt.splitl Char.isDigit) "abcd"
            in
              A.eqString "taken" ("", taken);
              A.eqString "rest" ("abcd", restOf rest)
            end),

          Case ("takel and dropl", fn () =>
            (A.eqString "takel" ("ab", onString (StringCvt.takel Char.isAlpha) "ab1");
             A.eqString "dropl"
               ("1", restOf (onString (StringCvt.dropl Char.isAlpha) "ab1")))),

          Case ("skipWS", fn () =>
            (A.eqString "leading whitespace"
               ("ab", restOf (onString StringCvt.skipWS "  \t\n ab"));
             A.eqString "no whitespace"
               ("ab", restOf (onString StringCvt.skipWS "ab"));
             A.eqString "all whitespace"
               ("", restOf (onString StringCvt.skipWS "   "))))
        ]),

        Group ("scanString",
        [ Case ("a successful scan", fn () =>
            A.eqIntOption "integer"
              (SOME 42, StringCvt.scanString (Int.scan StringCvt.DEC) "42")),

          Case ("a failing scan", fn () =>
            A.eqIntOption "letters"
              (NONE, StringCvt.scanString (Int.scan StringCvt.DEC) "abc")),

          (* scanString discards the residual stream, so trailing input is
           * silently accepted -- this is what distinguishes it from writing a
           * scanner that insists on reaching the end. *)
          Case ("trailing input is ignored", fn () =>
            A.eqIntOption "integer then junk"
              (SOME 42, StringCvt.scanString (Int.scan StringCvt.DEC) "42abc"))
        ]),

        Group ("radix and rounding modes are distinct values",
        [ Case ("the four radices differ", fn () =>
            let
              val all = [StringCvt.BIN, StringCvt.OCT, StringCvt.DEC, StringCvt.HEX]
              fun distinct [] = true
                | distinct (x :: xs) =
                    not (List.exists (fn y => y = x) xs) andalso distinct xs
            in
              A.that "all four are distinct" (distinct all)
            end),

          Case ("the real formats differ", fn () =>
            A.that "SCI, FIX, GEN and EXACT are distinct"
              (StringCvt.SCI NONE <> StringCvt.FIX NONE
               andalso StringCvt.GEN NONE <> StringCvt.EXACT
               andalso StringCvt.SCI (SOME 2) <> StringCvt.SCI (SOME 3)))
        ]),

        Group ("laws",
        [ P.forAll ("padLeft never shortens",
                    G.pair (str, G.int (0, 20)), Show.pair (showS, Show.int),
                    fn (s, n) =>
                      String.size (StringCvt.padLeft #"." n s)
                      = Int.max (n, String.size s)),

          P.forAll ("padLeft ends with the original",
                    G.pair (str, G.int (0, 20)), Show.pair (showS, Show.int),
                    fn (s, n) => String.isSuffix s (StringCvt.padLeft #"." n s)),

          P.forAll ("padRight starts with the original",
                    G.pair (str, G.int (0, 20)), Show.pair (showS, Show.int),
                    fn (s, n) => String.isPrefix s (StringCvt.padRight #"." n s)),

          P.forAll ("padding is the identity at or below the current size",
                    str, showS,
                    fn s =>
                      StringCvt.padLeft #"." (String.size s) s = s
                      andalso StringCvt.padRight #"." (String.size s) s = s),

          P.forAll ("splitl reassembles the input", str, showS,
                    fn s =>
                      let
                        val (taken, rest) = onString (StringCvt.splitl Char.isAlpha) s
                      in
                        taken ^ restOf rest = s
                      end),

          P.forAll ("takel and dropl are the halves of splitl", str, showS,
                    fn s =>
                      let
                        val (taken, rest) = onString (StringCvt.splitl Char.isAlpha) s
                      in
                        onString (StringCvt.takel Char.isAlpha) s = taken
                        andalso restOf (onString (StringCvt.dropl Char.isAlpha) s)
                                = restOf rest
                      end),

          P.forAll ("everything taken satisfies the predicate", str, showS,
                    fn s =>
                      List.all Char.isAlpha
                        (String.explode (onString (StringCvt.takel Char.isAlpha) s))),

          P.forAll ("skipWS leaves something that is not whitespace", str, showS,
                    fn s =>
                      let val rest = restOf (onString StringCvt.skipWS s)
                      in
                        rest = "" orelse not (Char.isSpace (String.sub (rest, 0)))
                      end),

          P.forAll ("skipWS only removes a prefix", str, showS,
                    fn s => String.isSuffix (restOf (onString StringCvt.skipWS s)) s)
        ])
      ])
  end
