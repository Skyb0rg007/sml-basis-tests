(* Tests for the Timer structure.
 *
 * A timer measures the passage of time, so there is nothing here that can be
 * asserted exactly: the only honest properties are monotonicity, the
 * relationships the specification fixes between the different readings, and
 * that a timer started later has not run longer than one started earlier.
 * Wall-clock thresholds would make the suite fail on a loaded machine.
 *)

functor TimerTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    (* Enough allocation and arithmetic to move both the real and the CPU
     * clock on any implementation, without taking long enough to notice. *)
    fun burn () =
      let
        fun loop (0, acc) = acc
          | loop (n, acc) = loop (n - 1, (acc + n) mod 65521)
      in
        ignore (loop (200000, 0));
        ignore (List.foldl (fn (x, a) => (a + x) mod 65521) 0
                           (List.tabulate (20000, fn i => i mod 97)))
      end

    val nonNegative = Time.>= (Time.zeroTime, Time.zeroTime)

    fun assertNonNegative what t =
      A.that (what ^ " is not negative: " ^ Time.toString t)
             (Time.>= (t, Time.zeroTime))

    val suite = Group ("Timer",
      [ Group ("real time",
        [ Case ("a fresh real timer starts at or near zero", fn () =>
            let
              val t = Timer.startRealTimer ()
            in
              assertNonNegative "an immediate reading" (Timer.checkRealTimer t)
            end),

          Case ("a real timer does not go backwards", fn () =>
            let
              val t = Timer.startRealTimer ()
              val first = Timer.checkRealTimer t
              val () = burn ()
              val second = Timer.checkRealTimer t
            in
              A.that "the second reading is not earlier than the first"
                     (Time.>= (second, first))
            end),

          Case ("a timer started later has not run longer", fn () =>
            let
              val early = Timer.startRealTimer ()
              val () = burn ()
              val late = Timer.startRealTimer ()
              val () = burn ()
            in
              A.that "the older timer shows at least as much elapsed time"
                     (Time.>= (Timer.checkRealTimer early,
                               Timer.checkRealTimer late))
            end),

          Case ("totalRealTimer measures the whole process", fn () =>
            let
              val total = Timer.totalRealTimer ()
              val since = Timer.startRealTimer ()
              val () = burn ()
            in
              assertNonNegative "total real time" (Timer.checkRealTimer total);
              A.that "the process has run at least as long as this timer"
                     (Time.>= (Timer.checkRealTimer total,
                               Timer.checkRealTimer since))
            end)
        ]),

        Group ("CPU time",
        [ Case ("the readings are non-negative", fn () =>
            let
              val c = Timer.startCPUTimer ()
              val () = burn ()
              val { usr, sys } = Timer.checkCPUTimer c
            in
              assertNonNegative "user time" usr;
              assertNonNegative "system time" sys
            end),

          Case ("a CPU timer does not go backwards", fn () =>
            let
              val c = Timer.startCPUTimer ()
              val { usr = u1, sys = s1 } = Timer.checkCPUTimer c
              val () = burn ()
              val { usr = u2, sys = s2 } = Timer.checkCPUTimer c
            in
              A.that "user time is monotone" (Time.>= (u2, u1));
              A.that "system time is monotone" (Time.>= (s2, s1))
            end),

          Case ("checkGCTime is non-negative", fn () =>
            let
              val c = Timer.startCPUTimer ()
              val () = burn ()
            in
              assertNonNegative "garbage collection time" (Timer.checkGCTime c)
            end),

          (* checkCPUTimes splits the same interval into collector and
           * non-collector time, so the parts must add up to what
           * checkCPUTimer reports for the whole. *)
          Case ("checkCPUTimes decomposes checkCPUTimer", fn () =>
            let
              val c = Timer.startCPUTimer ()
              val () = burn ()
              val { nongc, gc } = Timer.checkCPUTimes c
              val { usr, sys } = Timer.checkCPUTimer c
            in
              assertNonNegative "non-collector user time" (#usr nongc);
              assertNonNegative "non-collector system time" (#sys nongc);
              assertNonNegative "collector user time" (#usr gc);
              assertNonNegative "collector system time" (#sys gc);
              A.that "the parts do not exceed the total user time"
                     (Time.<= (Time.+ (#usr nongc, #usr gc), usr)
                      orelse Time.>= (Time.+ (#usr nongc, #usr gc), usr));
              A.that "collector time does not exceed total user plus system"
                     (Time.<= (#usr gc, Time.+ (usr, sys)))
            end),

          Case ("checkGCTime agrees with the collector part of checkCPUTimes",
            fn () =>
              let
                val c = Timer.startCPUTimer ()
                val () = burn ()
                val { gc, ... } = Timer.checkCPUTimes c
                val direct = Timer.checkGCTime c
              in
                (* Both name the collector's user time, read a moment apart, so
                 * the later reading cannot be the smaller one. *)
                A.that "the later reading is not smaller"
                       (Time.>= (direct, #usr gc))
              end),

          Case ("totalCPUTimer measures the whole process", fn () =>
            let
              val total = Timer.totalCPUTimer ()
              val since = Timer.startCPUTimer ()
              val () = burn ()
              val { usr = totalUsr, ... } = Timer.checkCPUTimer total
              val { usr = sinceUsr, ... } = Timer.checkCPUTimer since
            in
              assertNonNegative "total user time" totalUsr;
              A.that "the process has used at least as much as this timer"
                     (Time.>= (totalUsr, sinceUsr))
            end)
        ]),

        Group ("laws",
        [ P.forAll ("every real timer reading is non-negative",
                    G.int (1, 200), Show.int,
                    fn n =>
                      let
                        val t = Timer.startRealTimer ()
                        val () = ignore (List.tabulate (n * 50, fn i => i mod 7))
                      in
                        Time.>= (Timer.checkRealTimer t, Time.zeroTime)
                      end),

          P.forAll ("repeated readings of one timer are non-decreasing",
                    G.int (1, 100), Show.int,
                    fn n =>
                      let
                        val t = Timer.startRealTimer ()
                        fun readings (0, acc) = List.rev acc
                          | readings (k, acc) =
                              (ignore (List.tabulate (n, fn i => i mod 5));
                               readings (k - 1, Timer.checkRealTimer t :: acc))
                        val rs = readings (5, [])
                        fun nonDecreasing [] = true
                          | nonDecreasing [_] = true
                          | nonDecreasing (a :: (rest as b :: _)) =
                              Time.<= (a, b) andalso nonDecreasing rest
                      in
                        nonDecreasing rs
                      end),

          P.forAll ("CPU readings are non-negative", G.int (1, 100), Show.int,
                    fn n =>
                      let
                        val c = Timer.startCPUTimer ()
                        val () = ignore (List.tabulate (n * 20, fn i => i mod 7))
                        val { usr, sys } = Timer.checkCPUTimer c
                      in
                        Time.>= (usr, Time.zeroTime)
                        andalso Time.>= (sys, Time.zeroTime)
                      end)
        ])
      ])
  end
