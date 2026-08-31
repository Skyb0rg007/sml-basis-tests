(* Tests for the Option structure and its top-level aliases. *)

functor OptionTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val optInt = G.option G.smallInt
    val showOptInt = Show.option Show.int

    val suite = Group ("Option",
      [ Case ("getOpt", fn () =>
          (A.eqInt "SOME" (1, getOpt (SOME 1, 0));
           A.eqInt "NONE" (0, getOpt (NONE, 0)))),

        Case ("isSome", fn () =>
          (A.eqBool "SOME" (true, isSome (SOME 1));
           A.eqBool "NONE" (false, isSome NONE))),

        Case ("valOf", fn () =>
          (A.eqInt "SOME" (1, valOf (SOME 1));
           A.raises "valOf NONE" A.isOption (fn () => valOf NONE))),

        Case ("Option.filter", fn () =>
          (A.eqIntOption "kept" (SOME 4, Option.filter (fn n => n > 3) 4);
           A.eqIntOption "dropped" (NONE, Option.filter (fn n => n > 3) 2))),

        Case ("Option.join", fn () =>
          (A.eqIntOption "nested SOME" (SOME 1, Option.join (SOME (SOME 1)));
           A.eqIntOption "inner NONE" (NONE, Option.join (SOME NONE));
           A.eqIntOption "outer NONE" (NONE, Option.join NONE))),

        Case ("Option.app", fn () =>
          let
            val cell = ref 0
          in
            Option.app (fn n => cell := n) (SOME 5);
            A.eqInt "applied" (5, !cell);
            Option.app (fn n => cell := n) NONE;
            A.eqInt "not applied" (5, !cell)
          end),

        Case ("Option.map", fn () =>
          (A.eqIntOption "SOME" (SOME 2, Option.map (fn n => n * 2) (SOME 1));
           A.eqIntOption "NONE" (NONE, Option.map (fn n => n * 2) NONE))),

        Case ("Option.mapPartial", fn () =>
          let
            val f = fn n => if n > 0 then SOME (n * 2) else NONE
          in
            A.eqIntOption "SOME to SOME" (SOME 2, Option.mapPartial f (SOME 1));
            A.eqIntOption "SOME to NONE" (NONE, Option.mapPartial f (SOME ~1));
            A.eqIntOption "NONE" (NONE, Option.mapPartial f NONE)
          end),

        Case ("Option.compose", fn () =>
          let
            val f = fn n => n + 1
            val g = fn n => if n > 0 then SOME n else NONE
            val h = Option.compose (f, g)
          in
            A.eqIntOption "hit" (SOME 4, h 3);
            A.eqIntOption "miss" (NONE, h ~3)
          end),

        Case ("Option.composePartial", fn () =>
          let
            val f = fn n => if n < 10 then SOME (n + 1) else NONE
            val g = fn n => if n > 0 then SOME n else NONE
            val h = Option.composePartial (f, g)
          in
            A.eqIntOption "both hit" (SOME 4, h 3);
            A.eqIntOption "second misses" (NONE, h ~3);
            A.eqIntOption "first misses" (NONE, h 20)
          end),

        P.forAll ("getOpt agrees with a hand-written case",
                  G.pair (optInt, G.smallInt),
                  Show.pair (showOptInt, Show.int),
                  fn (opt, d) =>
                    getOpt (opt, d) = (case opt of NONE => d | SOME v => v)),

        P.forAll ("isSome is the negation of being NONE",
                  optInt, showOptInt,
                  fn opt => isSome opt = (opt <> NONE)),

        P.forAll ("valOf inverts SOME",
                  G.smallInt, Show.int,
                  fn n => valOf (SOME n) = n),

        P.forAll ("map preserves definedness",
                  optInt, showOptInt,
                  fn opt => isSome (Option.map (fn n => n) opt) = isSome opt),

        P.forAll ("join o SOME is the identity",
                  optInt, showOptInt,
                  fn opt => Option.join (SOME opt) = opt),

        P.forAll ("mapPartial f = join o map f",
                  optInt, showOptInt,
                  fn opt =>
                    let val f = fn n => if n mod 2 = 0 then SOME n else NONE
                    in Option.mapPartial f opt = Option.join (Option.map f opt) end),

        (* "The expression compose (f, g) is equivalent to (map f) o g." *)
        P.forAll ("compose f g = map f o g",
                  G.smallInt, Show.int,
                  fn n =>
                    let
                      val f = fn m => m + 1
                      val g = fn m => if m mod 3 = 0 then NONE else SOME (m * 2)
                    in
                      Option.compose (f, g) n = (Option.map f o g) n
                    end),

        (* "The expression composePartial (f, g) is equivalent to
         * (mapPartial f) o g." *)
        P.forAll ("composePartial f g = mapPartial f o g",
                  G.smallInt, Show.int,
                  fn n =>
                    let
                      val f = fn m => if m mod 2 = 0 then SOME (m + 1) else NONE
                      val g = fn m => if m mod 3 = 0 then NONE else SOME (m * 2)
                    in
                      Option.composePartial (f, g) n
                      = (Option.mapPartial f o g) n
                    end),

        P.forAll ("app runs the function exactly when the option is SOME",
                  optInt, showOptInt,
                  fn opt =>
                    let
                      val cell = ref 0
                      val () = Option.app (fn n => cell := !cell + 1) opt
                    in
                      !cell = (if isSome opt then 1 else 0)
                    end),

        P.forAll ("map applies the function under SOME",
                  optInt, showOptInt,
                  fn opt =>
                    Option.map (fn n => n + 1) opt
                    = (case opt of NONE => NONE | SOME v => SOME (v + 1))),

        P.forAll ("filter keeps exactly what the predicate accepts",
                  G.smallInt, Show.int,
                  fn n =>
                    let val p = fn m => m > 0
                    in Option.filter p n = (if p n then SOME n else NONE) end)
      ])
  end
