(* gen.sml -- random value generators.
 *
 * A generator is a function of a size parameter and a random state.  The size
 * bounds the "bigness" of the result (list length, string length, integer
 * magnitude); the runner sweeps it across trials so that a property sees both
 * tiny and larger inputs.
 *
 * There is deliberately no shrinking: a falsifying input is reported exactly
 * as generated.
 *)

signature GEN =
  sig
    type 'a gen

    val run : 'a gen -> int -> Random.rand -> 'a * Random.rand

    (* combinators *)
    val return    : 'a -> 'a gen
    val map       : ('a -> 'b) -> 'a gen -> 'b gen
    val map2      : ('a * 'b -> 'c) -> 'a gen * 'b gen -> 'c gen
    val bind      : 'a gen -> ('a -> 'b gen) -> 'b gen
    val pair      : 'a gen * 'b gen -> ('a * 'b) gen
    val triple    : 'a gen * 'b gen * 'c gen -> ('a * 'b * 'c) gen
    val sized     : (int -> 'a gen) -> 'a gen
    val resize    : int -> 'a gen -> 'a gen
    val oneOf     : 'a gen list -> 'a gen
    val frequency : (int * 'a gen) list -> 'a gen
    val elem      : 'a list -> 'a gen
    val filter    : ('a -> bool) -> 'a gen -> 'a gen

    (* scalars *)
    val bool      : bool gen
    val order     : order gen
    val int       : int * int -> int gen
    val nat       : int gen          (* 0 .. size *)
    val smallInt  : int gen          (* ~size .. size *)
    val anyInt    : int gen          (* biased towards the representable edges *)
    val nonZeroInt: int gen
    val word      : word gen
    val unitReal  : real gen         (* [0, 1) *)
    val anyReal   : real gen         (* finite, mixed magnitudes and signs *)

    (* text *)
    val char           : char gen    (* 0 .. Char.maxOrd *)
    val asciiChar      : char gen    (* 0 .. 127 *)
    val printableChar  : char gen    (* 32 .. 126 *)
    val alphaNumChar   : char gen
    val string         : string gen
    val asciiString    : string gen
    val printableString: string gen

    (* containers *)
    val listN  : int -> 'a gen -> 'a list gen
    val list   : 'a gen -> 'a list gen
    val list1  : 'a gen -> 'a list gen   (* never empty *)
    val vector : 'a gen -> 'a vector gen
    val option : 'a gen -> 'a option gen

    (* an index into a container of the given length, plus the length *)
    val indexIn : int -> int gen
  end

structure Gen :> GEN =
  struct

    type 'a gen = int -> Random.rand -> 'a * Random.rand

    fun run g size r = g size r

    fun return x = fn _ => fn r => (x, r)

    fun map f g = fn sz => fn r =>
      let val (x, r') = g sz r in (f x, r') end

    fun bind g k = fn sz => fn r =>
      let val (x, r') = g sz r in k x sz r' end

    fun pair (g1, g2) = fn sz => fn r =>
      let
        val (a, r1) = g1 sz r
        val (b, r2) = g2 sz r1
      in ((a, b), r2) end

    fun map2 f (g1, g2) = map f (pair (g1, g2))

    fun triple (g1, g2, g3) = fn sz => fn r =>
      let
        val (a, r1) = g1 sz r
        val (b, r2) = g2 sz r1
        val (c, r3) = g3 sz r2
      in ((a, b, c), r3) end

    fun sized f = fn sz => fn r => f sz sz r

    fun resize n g = fn _ => fn r => g n r

    fun elem [] = raise Domain
      | elem xs =
          let val n = List.length xs
          in fn _ => fn r =>
               let val (i, r') = Random.int (0, n - 1) r
               in (List.nth (xs, i), r') end
          end

    fun oneOf [] = raise Domain
      | oneOf gs =
          let val n = List.length gs
          in fn sz => fn r =>
               let val (i, r') = Random.int (0, n - 1) r
               in List.nth (gs, i) sz r' end
          end

    fun frequency wgs =
      let
        val wgs = List.filter (fn (w, _) => w > 0) wgs
        val total = List.foldl (fn ((w, _), a) => a + w) 0 wgs
        fun pick (k, (w, g) :: rest) = if k < w then g else pick (k - w, rest)
          | pick (_, []) = raise Domain
      in
        if total <= 0 then raise Domain
        else fn sz => fn r =>
          let val (k, r') = Random.int (0, total - 1) r
          in pick (k, wgs) sz r' end
      end

    (* Bounded retry: a generator that cannot satisfy the predicate must not
     * hang the suite, so give up and return the last value drawn. *)
    fun filter p g = fn sz => fn r =>
      let
        fun go (0, x, r) = (x, r)
          | go (n, _, r) =
              let val (x, r') = g sz r
              in if p x then (x, r') else go (n - 1, x, r') end
        val (x0, r0) = g sz r
      in
        if p x0 then (x0, r0) else go (100, x0, r0)
      end

    val bool : bool gen = fn _ => Random.bool
    val order : order gen = elem [LESS, EQUAL, GREATER]

    fun int (lo, hi) = fn _ => fn r => Random.int (lo, hi) r

    val nat : int gen = fn sz => fn r => Random.nat sz r
    val smallInt : int gen = fn sz => fn r => Random.int (~sz, sz) r

    (* Values at the edge of the representable range are where conversions and
     * overflow checks go wrong, so draw them far more often than chance would. *)
    val edgeInts =
      case (Int.minInt, Int.maxInt) of
          (SOME lo, SOME hi) => [lo, lo + 1, hi, hi - 1, hi div 2, lo div 2]
        | _ => [1073741823, ~1073741824, 2147483647, ~2147483648]

    val anyInt : int gen =
      frequency [ (6, smallInt),
                  (2, elem [0, 1, ~1, 2, ~2, 10, ~10, 100, ~100]),
                  (2, elem edgeInts) ]

    val nonZeroInt : int gen = filter (fn n => n <> 0) anyInt

    (* Assembled 30 bits at a time so that it covers the full word whatever
     * Word.wordSize turns out to be. *)
    val word : word gen = fn _ => fn r =>
      let
        fun go (n, acc, r) =
          if n <= 0 then (acc, r)
          else
            let
              val k = if n < 30 then n else 30
              val (w, r') = Random.bits k r
            in
              go (n - k, Word.orb (Word.<< (acc, Word.fromInt k), w), r')
            end
      in
        go (Word.wordSize, 0w0, r)
      end

    val unitReal : real gen = fn _ => fn r => Random.real r

    val anyReal : real gen =
      let
        val scaled =
          fn sz => fn r =>
            let
              val (u, r1) = Random.real r
              val (e, r2) = Random.int (~12, 12) r1
              val (s, r3) = Random.bool r2
              val m = u * Real.fromInt (sz + 1)
              val v = m * Math.pow (10.0, Real.fromInt e)
            in
              ((if s then v else ~v), r3)
            end
      in
        frequency [ (6, scaled),
                    (2, elem [0.0, 1.0, ~1.0, 0.5, ~0.5, 2.0, ~2.0, 100.0]),
                    (1, map Real.fromInt smallInt) ]
      end

    fun charFrom (lo, hi) : char gen = map Char.chr (int (lo, hi))

    val char : char gen = charFrom (0, Char.maxOrd)
    val asciiChar : char gen = charFrom (0, 127)
    val printableChar : char gen = charFrom (32, 126)
    val alphaNumChar : char gen =
      oneOf [charFrom (48, 57), charFrom (65, 90), charFrom (97, 122)]

    fun listN n g : 'a list gen =
      let
        fun go (0, acc) = (fn sz => fn r => (List.rev acc, r))
          | go (k, acc) =
              (fn sz => fn r =>
                 let val (x, r') = g sz r
                 in go (k - 1, x :: acc) sz r' end)
      in
        if n <= 0 then return [] else go (n, [])
      end

    fun list g : 'a list gen = sized (fn n => bind (int (0, n)) (fn k => listN k g))
    fun list1 g : 'a list gen = sized (fn n => bind (int (1, Int.max (1, n))) (fn k => listN k g))

    fun vector g : 'a vector gen = map (fn xs => Vector.fromList xs) (list g)

    fun option g : 'a option gen = frequency [(1, return NONE), (3, map SOME g)]

    val string : string gen = map String.implode (list char)
    val asciiString : string gen = map String.implode (list asciiChar)
    val printableString : string gen = map String.implode (list printableChar)

    fun indexIn n : int gen = if n <= 0 then return 0 else int (0, n - 1)

  end
