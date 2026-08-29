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

        P.forAll ("not is an involution", G.bool, Show.bool,
                  fn b => not (not b) = b),

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
