(* random.sml -- a portable pseudo-random source.
 *
 * Design constraints, in order of importance:
 *
 *  1. It must run on *any* Standard ML implementation, so it uses nothing
 *     outside the required part of the Basis Library.
 *
 *  2. Word.wordSize is implementation-defined, so the generator may not
 *     assume 32- or 64-bit words.  The state here is 30 bits and the
 *     multiply is done with 15-bit limbs, which keeps every intermediate
 *     product below 2^30.  Word arithmetic wraps silently (it never raises
 *     Overflow), and wrapping at any modulus above 2^30 leaves the low 30
 *     bits intact, so the result is correct whenever wordSize >= 30.  Every
 *     SML system in existence is at least 31.
 *
 *  3. The state is threaded explicitly rather than kept in a ref.  The
 *     Definition leaves the evaluation order of most expression forms
 *     unspecified, so a ref-based generator would hand different values to
 *     different compilers and a failure would not reproduce.  Threading the
 *     state makes a run a pure function of its seed.
 *)

signature RANDOM =
  sig
    type rand

    (* fromSeed n -- a generator seeded by n.  Any int is accepted. *)
    val fromSeed : int -> rand

    (* bits n r -- n uniform bits, 0 <= n <= 30. *)
    val bits : int -> rand -> word * rand

    (* nat d r -- uniform in [0, d].  Raises Domain if d < 0. *)
    val nat : int -> rand -> int * rand

    (* int (lo, hi) r -- uniform in [lo, hi].  Raises Domain if lo > hi.
     * When hi - lo overflows the int range the two halves [lo, ~1] and
     * [0, hi] are chosen with equal probability, which is not uniform over
     * the whole range but is perfectly adequate for generating test data. *)
    val int : int * int -> rand -> int * rand

    val bool : rand -> bool * rand

    (* real r -- uniform in [0, 1) with 24 bits of resolution. *)
    val real : rand -> real * rand

    (* Independent stream derived from a string, so that each property gets
     * its own reproducible sequence regardless of how many ran before it. *)
    val fromSeedAndName : int * string -> rand
  end

structure Random :> RANDOM =
  struct

    val mask15 = 0wx7FFF
    val mask30 = 0wx3FFFFFFF

    (* s' = (a * s + c) mod 2^30, with a = 22695477 = 692 * 2^15 + 20021.
     * a = 5 (mod 8) and c is odd, so the period is the full 2^30. *)
    val aHi = 0w692
    val aLo = 0w20021
    val c   = 0w1013904223

    type rand = word

    fun step s =
      let
        val sLo = Word.andb (s, mask15)
        val sHi = Word.andb (Word.>> (s, 0w15), mask15)
        (* Only the low 15 bits of the cross terms survive the shift, so mask
         * them before adding and nothing can grow past 2^30. *)
        val mid = Word.andb (aLo * sHi + aHi * sLo, mask15)
      in
        Word.andb (aLo * sLo + Word.<< (mid, 0w15) + c, mask30)
      end

    (* The low bits of a power-of-two LCG are notoriously non-random, so take
     * the top 15 bits of each of two successive states. *)
    fun raw s =
      let
        val s1 = step s
        val s2 = step s1
      in
        (Word.andb (Word.<< (Word.>> (s1, 0w15), 0w15) + Word.>> (s2, 0w15),
                    mask30),
         s2)
      end

    fun bits n r =
      if n < 0 orelse n > 30 then raise Domain
      else
        let val (w, r') = raw r
        in (Word.>> (w, Word.fromInt (30 - n)), r') end

    fun bool r =
      let val (w, r') = bits 1 r in (w = 0w1, r') end

    fun mix (s, 0) = s
      | mix (s, n) = mix (step s, n - 1)

    fun fromSeed n = mix (Word.andb (Word.fromInt n, mask30), 8)

    fun fromSeedAndName (n, name) =
      let
        (* Word arithmetic wraps, so this cannot overflow whatever the seed. *)
        val h = List.foldl (fn (ch, h) => h * 0w131 + Word.fromInt (Char.ord ch))
                           (Word.andb (Word.fromInt n, mask30))
                           (String.explode name)
      in
        mix (Word.andb (h, mask30), 8)
      end

    fun pow2 n = Word.toInt (Word.<< (0w1, Word.fromInt n))

    (* Number of bits needed to represent d, computed by halving so that it
     * works even when the implementation's int is arbitrary precision. *)
    fun bitWidth (0, k) = k
      | bitWidth (d, k) = bitWidth (d div 2, k + 1)

    fun nat d r =
      if d < 0 then raise Domain
      else if d = 0 then (0, r)
      else
        let
          val k = bitWidth (d, 0)
          (* Build at most k bits.  The final value is < 2^k <= maxInt + 1, so
           * no intermediate can overflow. *)
          fun build (0, acc, r) = (acc, r)
            | build (i, acc, r) =
                let
                  val n = if i < 15 then i else 15
                  val (w, r') = bits n r
                in
                  build (i - n, acc * pow2 n + Word.toInt w, r')
                end
          fun attempt r =
            let val (v, r') = build (k, 0, r)
            in if v <= d then (v, r') else attempt r' end
        in
          attempt r
        end

    fun int (lo, hi) r =
      if lo > hi then raise Domain
      else if lo = hi then (lo, r)
      else
        case (SOME (hi - lo) handle Overflow => NONE) of
            (* lo + k <= lo + (hi - lo) = hi, so the addition cannot overflow. *)
            SOME d => let val (k, r') = nat d r in (lo + k, r') end
            (* Only reachable when lo < 0 <= hi, and then both ~1 - lo and
             * hi - 0 are representable. *)
          | NONE =>
              let val (b, r') = bool r
              in if b then int (lo, ~1) r' else int (0, hi) r' end

    fun real r =
      let val (v, r') = nat 16777215 r
      in (Real.fromInt v / 16777216.0, r') end

  end
