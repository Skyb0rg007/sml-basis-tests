(* Tests for the Bool structure. *)

functor BoolTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val suite = Group ("Bool",
      [ Case ("not", fn () =>
          (A.eqBool "not true" (false, not true);
           A.eqBool "not false" (true, not false))),

        Case ("toString", fn () =>
          (A.eqString "true" ("true", Bool.toString true);
           A.eqString "false" ("false", Bool.toString false))),

        Case ("fromString on exact spellings", fn () =>
          (A.eqBy (op =, Show.option Show.bool) "true"
             (SOME true, Bool.fromString "true");
           A.eqBy (op =, Show.option Show.bool) "false"
             (SOME false, Bool.fromString "false"))),

        Case ("fromString skips leading whitespace", fn () =>
          A.eqBy (op =, Show.option Show.bool) "spaces then true"
            (SOME true, Bool.fromString "   true")),

        Case ("fromString ignores trailing characters", fn () =>
          A.eqBy (op =, Show.option Show.bool) "true then junk"
            (SOME true, Bool.fromString "truexyz")),

        Case ("fromString rejects non-booleans", fn () =>
          (A.eqBy (op =, Show.option Show.bool) "empty"
             (NONE, Bool.fromString "");
           A.eqBy (op =, Show.option Show.bool) "word"
             (NONE, Bool.fromString "yes"))),

        Case ("scan consumes only the boolean and no more", fn () =>
          case Bool.scan Substring.getc (Substring.full "false tail") of
              NONE => A.fail "scan returned NONE"
            | SOME (b, rest) =>
                (A.eqBool "value" (false, b);
                 A.eqString "remainder" (" tail", Substring.string rest))),

        (* "Ignoring case and initial whitespace, the sequences \"true\" and
         * \"false\" are converted to the corresponding boolean values." *)
        Case ("fromString ignores case", fn () =>
          (A.eqBy (op =, Show.option Show.bool) "TRUE"
             (SOME true, Bool.fromString "TRUE");
           A.eqBy (op =, Show.option Show.bool) "False"
             (SOME false, Bool.fromString "False");
           A.eqBy (op =, Show.option Show.bool) "tRuE"
             (SOME true, Bool.fromString "tRuE");
           A.eqBy (op =, Show.option Show.bool) "fALSE"
             (SOME false, Bool.fromString "fALSE"))),

        Case ("fromString rejects a proper prefix", fn () =>
          (A.eqBy (op =, Show.option Show.bool) "tru"
             (NONE, Bool.fromString "tru");
           A.eqBy (op =, Show.option Show.bool) "fals"
             (NONE, Bool.fromString "fals"))),

        Case ("scan skips leading whitespace and reports the rest", fn () =>
          case Bool.scan Substring.getc (Substring.full " \t\n true rest") of
              NONE => A.fail "scan returned NONE"
            | SOME (b, rest) =>
                (A.eqBool "value" (true, b);
                 A.eqString "remainder" (" rest", Substring.string rest))),

        Case ("scan declines a non-boolean", fn () =>
          (A.that "yes" (not (isSome (Bool.scan Substring.getc
                                        (Substring.full "yes"))));
           A.that "empty" (not (isSome (Bool.scan Substring.getc
                                          (Substring.full "")))))),

        P.forAll ("not is an involution", G.bool, Show.bool,
                  fn b => not (not b) = b),

        (* "The function fromString is equivalent to StringCvt.scanString
         * scan." *)
        P.forAll ("fromString is scanString scan",
                  G.oneOf [ G.printableString,
                            G.map (fn (b, s) => Bool.toString b ^ s)
                                  (G.pair (G.bool, G.printableString)) ],
                  Show.string,
                  fn s =>
                    Bool.fromString s = StringCvt.scanString Bool.scan s),

        P.forAll ("fromString inverts toString", G.bool, Show.bool,
                  fn b => Bool.fromString (Bool.toString b) = SOME b),

        P.forAll ("excluded middle", G.bool, Show.bool,
                  fn b => b orelse not b),

        P.forAll ("non-contradiction", G.bool, Show.bool,
                  fn b => not (b andalso not b)),

        P.forAll ("de Morgan", G.pair (G.bool, G.bool),
                  Show.pair (Show.bool, Show.bool),
                  fn (a, b) => not (a andalso b) = (not a orelse not b))
      ])
  end
