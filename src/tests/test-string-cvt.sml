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
              (SOME 42, StringCvt.scanString (Int.scan StringCvt.DEC) "42abc")),

          (* "splitl can be used with scanning functions such as scanString by
           * composing it with SOME; e.g.,
           * scanString (fn rdr => SOME o (splitl f rdr))." *)
          Case ("the documented way to use splitl with scanString", fn () =>
            A.eqStringOption "the alphabetic prefix"
              (SOME "abc",
               StringCvt.scanString
                 (fn rdr => SOME o (StringCvt.splitl Char.isAlpha rdr))
                 "abc123")),

          (* "When the input source is a list of characters, scanning values
           * can be accomplished by applying the appropriate scan function to
           * the function List.getItem." *)
          Case ("a reader over a list of characters", fn () =>
            (case Int.scan StringCvt.DEC List.getItem (String.explode "42rest") of
                 NONE => A.fail "scanning an int from a char list returned NONE"
               | SOME (n, rest) =>
                   (A.eqInt "value" (42, n);
                    A.eqCharList "remainder" ([#"r", #"e", #"s", #"t"], rest));
             case Bool.scan List.getItem (String.explode "true!") of
                 NONE => A.fail "scanning a bool from a char list returned NONE"
               | SOME (b, rest) =>
                   (A.eqBool "value" (true, b);
                    A.eqCharList "remainder" ([#"!"], rest))))
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
                    fn s => String.isSuffix (restOf (onString StringCvt.skipWS s)) s),

          (* "It is equivalent to dropl Char.isSpace." *)
          P.forAll ("skipWS is dropl of Char.isSpace", str, showS,
                    fn s =>
                      restOf (onString StringCvt.skipWS s)
                      = restOf (onString (StringCvt.dropl Char.isSpace) s)),

          (* "These return s padded, on the left or right, respectively, with
           * i - |s| copies of the character c." *)
          P.forAll ("padding adds exactly the missing characters",
                    G.pair (str, G.int (~2, 20)), Show.pair (showS, Show.int),
                    fn (s, n) =>
                      let
                        val fill =
                          String.implode
                            (List.tabulate (Int.max (0, n - String.size s),
                                            fn _ => #"."))
                      in
                        StringCvt.padLeft #"." n s = fill ^ s
                        andalso StringCvt.padRight #"." n s = s ^ fill
                      end),

          P.forAll ("a reader over a character list agrees with one over a substring",
                    G.map Int.toString G.anyInt, showS,
                    fn s =>
                      let
                        val viaList =
                          Option.map (fn (n, rest) => (n, String.implode rest))
                            (Int.scan StringCvt.DEC List.getItem
                                      (String.explode s))
                        val viaSubstring =
                          Option.map (fn (n, rest) => (n, Substring.string rest))
                            (Int.scan StringCvt.DEC Substring.getc
                                      (Substring.full s))
                      in
                        viaList = viaSubstring
                      end)
        ])
      ])
  end
