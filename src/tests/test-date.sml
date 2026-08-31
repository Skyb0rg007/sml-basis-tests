(* Tests for the Date structure.
 *
 * Date is the most environment-sensitive required structure in the Basis: the
 * local time zone, and whether daylight saving is in effect, are properties of
 * the host rather than of the implementation.  Every test here therefore
 * builds dates with an explicit UTC offset, so that the answers are fixed by
 * the calendar rather than by where the machine happens to be.  The handful of
 * genuinely local operations are checked only for internal consistency.
 *)

functor DateTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val utc = SOME Time.zeroTime

    fun mk (y, m, d, hh, mm, ss) =
      Date.date { year = y, month = m, day = d, hour = hh, minute = mm,
                  second = ss, offset = utc }

    fun monthName Date.Jan = "Jan" | monthName Date.Feb = "Feb"
      | monthName Date.Mar = "Mar" | monthName Date.Apr = "Apr"
      | monthName Date.May = "May" | monthName Date.Jun = "Jun"
      | monthName Date.Jul = "Jul" | monthName Date.Aug = "Aug"
      | monthName Date.Sep = "Sep" | monthName Date.Oct = "Oct"
      | monthName Date.Nov = "Nov" | monthName Date.Dec = "Dec"

    fun dayName Date.Mon = "Mon" | dayName Date.Tue = "Tue"
      | dayName Date.Wed = "Wed" | dayName Date.Thu = "Thu"
      | dayName Date.Fri = "Fri" | dayName Date.Sat = "Sat"
      | dayName Date.Sun = "Sun"

    val eqMonth = A.eqBy (op =, monthName)
    val eqDay = A.eqBy (op =, dayName)
    val showDate = Date.toString

    val months = [Date.Jan, Date.Feb, Date.Mar, Date.Apr, Date.May, Date.Jun,
                  Date.Jul, Date.Aug, Date.Sep, Date.Oct, Date.Nov, Date.Dec]
    val weekdays = [Date.Mon, Date.Tue, Date.Wed, Date.Thu, Date.Fri,
                    Date.Sat, Date.Sun]

    (* Arbitrary valid instants, kept inside a range every implementation can
     * represent.  Day-of-month stops at 28 so that no month needs special
     * handling and the generated date is always real. *)
    val genDate =
      G.map
        (fn (((y, mi), (d, hh)), (mm, ss)) =>
            mk (y, List.nth (months, mi), d, hh, mm, ss))
        (G.pair (G.pair (G.pair (G.int (1970, 2030), G.int (0, 11)),
                         G.pair (G.int (1, 28), G.int (0, 23))),
                 G.pair (G.int (0, 59), G.int (0, 59))))

    val suite = Group ("Date",
      [ Group ("construction and accessors",
        [ Case ("the accessors return what was supplied", fn () =>
            let
              val d = mk (2000, Date.Jan, 1, 12, 30, 45)
            in
              A.eqInt "year" (2000, Date.year d);
              eqMonth "month" (Date.Jan, Date.month d);
              A.eqInt "day" (1, Date.day d);
              A.eqInt "hour" (12, Date.hour d);
              A.eqInt "minute" (30, Date.minute d);
              A.eqInt "second" (45, Date.second d)
            end),

          Case ("offset reports the zone the date was built with", fn () =>
            (A.eqBy (op =, Show.option Show.time) "explicit UTC"
               (SOME Time.zeroTime, Date.offset (mk (2000, Date.Jan, 1, 0, 0, 0)));
             A.eqBy (op =, Show.option Show.time) "no offset means local time"
               (NONE,
                Date.offset (Date.date { year = 2000, month = Date.Jan, day = 1,
                                         hour = 0, minute = 0, second = 0,
                                         offset = NONE })))),

          (* The Basis leaves the answer unknown for a date carrying an
           * explicit offset, so all three answers are acceptable; what is not
           * acceptable is raising. *)
          Case ("isDst answers or admits it does not know", fn () =>
            A.noRaise "isDst" (fn () => Date.isDst (mk (2000, Date.Jul, 1, 0, 0, 0)))),

          Case ("weekDay of some known dates", fn () =>
            (eqDay "1 January 2000 was a Saturday"
               (Date.Sat, Date.weekDay (mk (2000, Date.Jan, 1, 0, 0, 0)));
             eqDay "1 January 1970 was a Thursday"
               (Date.Thu, Date.weekDay (mk (1970, Date.Jan, 1, 0, 0, 0)));
             eqDay "29 February 2000 was a Tuesday"
               (Date.Tue, Date.weekDay (mk (2000, Date.Feb, 29, 0, 0, 0)));
             eqDay "31 December 2025 was a Wednesday"
               (Date.Wed, Date.weekDay (mk (2025, Date.Dec, 31, 0, 0, 0))))),

          Case ("yearDay counts from zero", fn () =>
            (A.eqInt "1 January" (0, Date.yearDay (mk (2000, Date.Jan, 1, 0, 0, 0)));
             A.eqInt "2 January" (1, Date.yearDay (mk (2000, Date.Jan, 2, 0, 0, 0)));
             A.eqInt "31 December of a leap year"
               (365, Date.yearDay (mk (2000, Date.Dec, 31, 0, 0, 0)));
             A.eqInt "31 December of a common year"
               (364, Date.yearDay (mk (2001, Date.Dec, 31, 0, 0, 0))))),

          Case ("out of range fields are normalised", fn () =>
            let
              val d = mk (2000, Date.Jan, 32, 0, 0, 0)
            in
              eqMonth "day 32 of January rolls into February"
                (Date.Feb, Date.month d);
              A.eqInt "and becomes the first" (1, Date.day d)
            end),

          (* "Thus, minute = 10, second = ~140 becomes minute = 7,
           * second = 40." *)
          Case ("the normalisation example from the specification", fn () =>
            let
              val d = Date.date { year = 2000, month = Date.Jan, day = 1,
                                  hour = 0, minute = 10, second = ~140,
                                  offset = utc }
            in
              A.eqInt "minute" (7, Date.minute d);
              A.eqInt "second" (40, Date.second d)
            end),

          Case ("every field borrows from the next larger unit", fn () =>
            let
              fun at (hh, mm, ss) =
                Date.date { year = 2000, month = Date.Mar, day = 10,
                            hour = hh, minute = mm, second = ss, offset = utc }
              val a = at (0, 0, 3600)      (* an hour of seconds *)
              val b = at (0, ~1, 0)        (* a minute before midnight *)
              val c = at (25, 0, 0)        (* past the end of the day *)
            in
              A.eqInt "3600 seconds is an hour" (1, Date.hour a);
              A.eqInt "and no minutes" (0, Date.minute a);
              A.eqInt "a negative minute borrows a day" (9, Date.day b);
              A.eqInt "leaving the last hour" (23, Date.hour b);
              A.eqInt "and the last minute" (59, Date.minute b);
              A.eqInt "25 hours rolls into the next day" (11, Date.day c);
              A.eqInt "leaving one hour" (1, Date.hour c)
            end),

          (* "Offsets are taken modulo 24 hours.  That is, we express t, in
           * hours, as sgn(t)(24*d + r) ... The offset then becomes sgn(t)*r
           * and sgn(t)(24*d) is added to the hours." *)
          Case ("an offset beyond a day is reduced, and the rest moves to the hours",
            fn () =>
              let
                val hours = Time.fromSeconds o LargeInt.fromInt
                val d = Date.date { year = 2000, month = Date.Jan, day = 10,
                                    hour = 12, minute = 0, second = 0,
                                    offset = SOME (hours (25 * 3600)) }
              in
                A.eqBy (op =, Show.option Show.time) "the offset is reduced"
                  (SOME (hours 3600), Date.offset d);
                A.eqInt "and the day advances" (11, Date.day d);
                A.eqInt "with the hours unchanged" (12, Date.hour d)
              end),

          Case ("the leap year rule", fn () =>
            (A.eqInt "2000 is a leap year, so 29 February exists"
               (29, Date.day (mk (2000, Date.Feb, 29, 0, 0, 0)));
             A.eqInt "2024 is a leap year"
               (29, Date.day (mk (2024, Date.Feb, 29, 0, 0, 0)));
             eqMonth "1900 is not, so 29 February rolls over"
               (Date.Mar, Date.month (mk (1900, Date.Feb, 29, 0, 0, 0)));
             eqMonth "2001 is not either"
               (Date.Mar, Date.month (mk (2001, Date.Feb, 29, 0, 0, 0)))))
        ]),

        Group ("formatting",
        [ (* toString is specified as fmt "%a %b %d %H:%M:%S %Y". *)
          Case ("toString has the specified shape", fn () =>
            let
              val d = mk (2000, Date.Jan, 1, 12, 30, 45)
              val s = Date.toString d
            in
              A.eqInt "twenty-four characters" (24, String.size s);
              A.eqString "the whole string"
                ("Sat Jan 01 12:30:45 2000", s);
              A.eqString "and it agrees with the equivalent fmt"
                (Date.fmt "%a %b %d %H:%M:%S %Y" d, s)
            end),

          Case ("fmt understands the common specifiers", fn () =>
            let
              val d = mk (2000, Date.Jan, 2, 9, 5, 7)
            in
              A.eqString "%Y" ("2000", Date.fmt "%Y" d);
              A.eqString "%m is zero padded" ("01", Date.fmt "%m" d);
              A.eqString "%d is zero padded" ("02", Date.fmt "%d" d);
              A.eqString "%H is zero padded" ("09", Date.fmt "%H" d);
              A.eqString "%M is zero padded" ("05", Date.fmt "%M" d);
              A.eqString "%S is zero padded" ("07", Date.fmt "%S" d);
              A.eqString "%b" ("Jan", Date.fmt "%b" d);
              A.eqString "%a" ("Sun", Date.fmt "%a" d);
              A.eqString "%j is the day of the year, one based"
                ("002", Date.fmt "%j" d);
              A.eqString "a percent sign" ("%", Date.fmt "%%" d);
              A.eqString "literal text is copied through"
                ("x2000y", Date.fmt "x%Yy" d);
              A.eqString "an empty format" ("", Date.fmt "" d)
            end),

          Case ("fromString reads what toString wrote", fn () =>
            let
              val d = mk (2000, Date.Jan, 1, 12, 30, 45)
            in
              case Date.fromString (Date.toString d) of
                  NONE => A.fail "fromString returned NONE"
                | SOME d' =>
                    (A.eqInt "year" (2000, Date.year d');
                     eqMonth "month" (Date.Jan, Date.month d');
                     A.eqInt "day" (1, Date.day d');
                     A.eqInt "hour" (12, Date.hour d');
                     A.eqInt "minute" (30, Date.minute d');
                     A.eqInt "second" (45, Date.second d'))
            end),

          (* The specifiers whose meaning the specification fixes, as opposed
           * to the locale-dependent ones. *)
          Case ("fmt understands the numeric specifiers", fn () =>
            let
              val morning = mk (2001, Date.Feb, 3, 9, 5, 7)
              val afternoon = mk (2001, Date.Feb, 3, 15, 5, 7)
              val midnight = mk (2001, Date.Feb, 3, 0, 5, 7)
            in
              A.eqString "%y is the year of the century"
                ("01", Date.fmt "%y" morning);
              A.eqString "%I is the twelve-hour clock"
                ("09", Date.fmt "%I" morning);
              A.eqString "%I in the afternoon" ("03", Date.fmt "%I" afternoon);
              A.eqString "%I at midnight is twelve"
                ("12", Date.fmt "%I" midnight);
              A.eqString "%w numbers the days from Sunday"
                ("6", Date.fmt "%w" morning);
              A.that "%U is a two-digit week number"
                (String.size (Date.fmt "%U" morning) = 2
                 andalso List.all Char.isDigit
                                  (String.explode (Date.fmt "%U" morning)));
              A.that "%W is a two-digit week number"
                (String.size (Date.fmt "%W" morning) = 2
                 andalso List.all Char.isDigit
                                  (String.explode (Date.fmt "%W" morning)))
            end),

          (* "Note, however, that unlike strftime, the behavior of fmt is
           * defined for the directive %c for any character c": an unknown
           * directive stands for the character itself. *)
          Case ("an unknown directive is the character itself", fn () =>
            let
              val d = mk (2000, Date.Jan, 1, 0, 0, 0)
            in
              A.eqString "%q" ("q", Date.fmt "%q" d);
              A.eqString "%~" ("~", Date.fmt "%~" d);
              A.eqString "%5" ("5", Date.fmt "%5" d);
              A.eqString "surrounded by text" ("aqb", Date.fmt "a%qb" d)
            end),

          Case ("%A and %B name the weekday and the month", fn () =>
            let
              val d = mk (2000, Date.Jan, 1, 13, 0, 0)
            in
              A.that "%A produces a string" (String.size (Date.fmt "%A" d) > 0);
              A.that "%B produces a string" (String.size (Date.fmt "%B" d) > 0)
            end),

          Case ("%c, %x and %X are the locale's representations", fn () =>
            let
              val d = mk (2000, Date.Jan, 1, 13, 0, 0)
            in
              A.that "%c produces a string" (String.size (Date.fmt "%c" d) > 0);
              A.that "%x produces a string" (String.size (Date.fmt "%x" d) > 0);
              A.that "%X produces a string" (String.size (Date.fmt "%X" d) > 0)
            end),

          (* "%p: locale's equivalent of the AM/PM designation" -- which may
           * be empty in a locale that has none, so the requirement is only
           * that it is accepted. *)
          Case ("%p is accepted", fn () =>
            A.noRaise "%p"
              (fn () => Date.fmt "%p" (mk (2000, Date.Jan, 1, 13, 0, 0)))),

          (* "%Z: time zone name or abbreviation, or the empty string if no
           * time zone information exists" -- so an empty answer is correct
           * and the directive must still be accepted.  Behind a configuration
           * flag because on Poly/ML 5.7.1 this call corrupts the heap; see
           * dateFmtHandlesZone. *)
          (* "No check of the consistency of the date (weekday, date in the
           * month, ...) is performed." *)
          Case ("scanning does not check the weekday against the date", fn () =>
            case Date.fromString "Mon Jan 01 12:30:45 2000" of
                NONE => A.fail "an inconsistent weekday was rejected"
              | SOME d =>
                  (A.eqInt "the year is read" (2000, Date.year d);
                   A.eqInt "the day is read" (1, Date.day d))),

          Case ("scanning insists on the exact format", fn () =>
            (A.that "a missing weekday"
               (not (isSome (Date.fromString "Jan 01 12:30:45 2000")));
             A.that "a one-digit day"
               (not (isSome (Date.fromString "Sat Jan 1 12:30:45 2000")));
             A.that "a truncated string"
               (not (isSome (Date.fromString "Sat Jan 01 12:30:45"))))),

          (* "It is equivalent to StringCvt.scanString scan." *)
          Case ("fromString is scanString scan", fn () =>
            let
              fun agree s =
                A.that ("agree on " ^ s)
                  (Option.map Date.toString (Date.fromString s)
                   = Option.map Date.toString
                       (StringCvt.scanString Date.scan s))
            in
              List.app agree
                ["Sat Jan 01 12:30:45 2000", "  Sat Jan 01 12:30:45 2000",
                 "not a date", ""]
            end),

          Case ("fromString skips leading whitespace", fn () =>
            A.that "leading spaces"
              (isSome (Date.fromString "   Sat Jan 01 12:30:45 2000"))),

          Case ("fromString rejects what is not a date", fn () =>
            (A.that "empty" (not (isSome (Date.fromString "")));
             A.that "letters" (not (isSome (Date.fromString "not a date"))))),

          Case ("scan leaves the rest of the stream alone", fn () =>
            case Date.scan Substring.getc
                   (Substring.full "Sat Jan 01 12:30:45 2000 tail") of
                NONE => A.fail "scan returned NONE"
              | SOME (d, rest) =>
                  (A.eqInt "year" (2000, Date.year d);
                   A.eqString "remainder" (" tail", Substring.string rest)))
        ]),

        Group ("the time-zone directive",
          (* "%Z: time zone name or abbreviation, or the empty string if no
           * time zone information exists" -- so an empty answer is correct
           * and the directive must still be accepted.  Behind a flag because
           * on Poly/ML 5.7.1 this call corrupts the heap and the run dies
           * with a segmentation fault; see dateFmtHandlesZone. *)
          onlyIf (C.dateFmtHandlesZone,
                  "implementation not declared to handle the %Z directive")
          [ Case ("%Z is accepted", fn () =>
              A.noRaise "%Z"
                (fn () => Date.fmt "%Z" (mk (2000, Date.Jan, 1, 13, 0, 0))))
          ]),

        Group ("time and ordering",
        [ Case ("a UTC date survives conversion to a time and back", fn () =>
            let
              val d = mk (2000, Date.Jan, 1, 12, 30, 45)
              val d' = Date.fromTimeUniv (Date.toTime d)
            in
              A.eqInt "year" (2000, Date.year d');
              eqMonth "month" (Date.Jan, Date.month d');
              A.eqInt "day" (1, Date.day d');
              A.eqInt "hour" (12, Date.hour d');
              A.eqInt "minute" (30, Date.minute d');
              A.eqInt "second" (45, Date.second d')
            end),

          Case ("the epoch is where it should be", fn () =>
            let
              val d = Date.fromTimeUniv Time.zeroTime
            in
              A.eqInt "year" (1970, Date.year d);
              eqMonth "month" (Date.Jan, Date.month d);
              A.eqInt "day" (1, Date.day d);
              A.eqInt "hour" (0, Date.hour d);
              A.eqInt "minute" (0, Date.minute d);
              A.eqInt "second" (0, Date.second d)
            end),

          Case ("fromTimeLocal is self-consistent", fn () =>
            (* The local zone is unknown, so only the round trip can be
             * checked, not the fields. *)
            let
              val t = Time.fromSeconds (LargeInt.fromInt 946730445)
              val d = Date.fromTimeLocal t
            in
              A.eqTime "back to the same instant" (t, Date.toTime d)
            end),

          Case ("localOffset is a whole number of minutes", fn () =>
            let
              val off = Date.localOffset ()
              val secs = Time.toSeconds off
            in
              A.that "offset is a multiple of sixty seconds"
                (LargeInt.mod (secs, LargeInt.fromInt 60) = LargeInt.fromInt 0)
            end),

          Case ("compare", fn () =>
            let
              val a = mk (2000, Date.Jan, 1, 0, 0, 0)
              val b = mk (2000, Date.Jan, 2, 0, 0, 0)
            in
              A.eqOrder "equal" (EQUAL, Date.compare (a, a));
              A.eqOrder "earlier" (LESS, Date.compare (a, b));
              A.eqOrder "later" (GREATER, Date.compare (b, a))
            end),

          (* "It lexicographically compares the dates, using the year, month,
           * day, hour, minute, and second information, but ignoring the
           * offset and daylight savings time information." *)
          Case ("compare ignores the time zone", fn () =>
            let
              val hours = Time.fromSeconds o LargeInt.fromInt
              fun at off =
                Date.date { year = 2000, month = Date.Jan, day = 1,
                            hour = 12, minute = 0, second = 0, offset = off }
              val utcDate = at (SOME Time.zeroTime)
              val westDate = at (SOME (hours (5 * 3600)))
            in
              A.eqOrder "the same fields in different zones"
                (EQUAL, Date.compare (utcDate, westDate));
              A.that "even though the instants differ"
                (Time.compare (Date.toTime utcDate, Date.toTime westDate)
                 <> EQUAL)
            end),

          (* "fromTimeLocal ... The returned date will have offset=NONE.
           * fromTimeUniv ... The returned date will have offset=SOME(0)." *)
          Case ("the two conversions from a time report their zones", fn () =>
            let
              val t = Time.fromSeconds (LargeInt.fromInt 946730445)
            in
              A.eqBy (op =, Show.option Show.time) "fromTimeLocal has no offset"
                (NONE, Date.offset (Date.fromTimeLocal t));
              A.eqBy (op =, Show.option Show.time) "fromTimeUniv is UTC"
                (SOME Time.zeroTime, Date.offset (Date.fromTimeUniv t))
            end),

          (* "If these functions are applied to the same time value, the
           * resulting dates will differ by the offset of the local time zone
           * from UTC."  Daylight saving may shift the effective offset by an
           * hour from the one localOffset reports, so both are accepted. *)
          Case ("the local and universal dates differ by the local offset",
            fn () =>
              let
                val t = Time.fromSeconds (LargeInt.fromInt 946730445)
                fun asUtcInstant d =
                  Date.toTime (Date.date { year = Date.year d,
                                           month = Date.month d,
                                           day = Date.day d, hour = Date.hour d,
                                           minute = Date.minute d,
                                           second = Date.second d,
                                           offset = SOME Time.zeroTime })
                val diff = Time.- (asUtcInstant (Date.fromTimeUniv t),
                                   asUtcInstant (Date.fromTimeLocal t))
                val off = Date.localOffset ()
                val hour = Time.fromSeconds (LargeInt.fromInt 3600)
              in
                A.that "the difference is the local offset, up to daylight saving"
                  (diff = off
                   orelse diff = Time.- (off, hour)
                   orelse diff = Time.+ (off, hour))
              end),

          Case ("the Date exception exists", fn () =>
            A.eqString "name" ("Date", exnName Date.Date))
        ]),

        Group ("laws",
        [ P.forAll ("the accessors invert the constructor", genDate, showDate,
                    fn d =>
                      Date.year (mk (Date.year d, Date.month d, Date.day d,
                                     Date.hour d, Date.minute d, Date.second d))
                      = Date.year d),

          P.forAll ("fromString inverts toString on the printed fields",
                    genDate, showDate,
                    fn d =>
                      case Date.fromString (Date.toString d) of
                          NONE => false
                        | SOME d' => Date.toString d' = Date.toString d),

          P.forAll ("a UTC date round trips through Time", genDate, showDate,
                    fn d =>
                      Date.toString (Date.fromTimeUniv (Date.toTime d))
                      = Date.toString d),

          P.forAll ("yearDay stays inside the year", genDate, showDate,
                    fn d => Date.yearDay d >= 0 andalso Date.yearDay d <= 365),

          P.forAll ("the fields stay in their ranges", genDate, showDate,
                    fn d =>
                      Date.day d >= 1 andalso Date.day d <= 31
                      andalso Date.hour d >= 0 andalso Date.hour d <= 23
                      andalso Date.minute d >= 0 andalso Date.minute d <= 59
                      (* A leap second is permitted, so 60 is allowed. *)
                      andalso Date.second d >= 0 andalso Date.second d <= 60),

          P.forAll ("compare is reflexive", genDate, showDate,
                    fn d => Date.compare (d, d) = EQUAL),

          P.forAll ("compare is antisymmetric",
                    G.pair (genDate, genDate), Show.pair (showDate, showDate),
                    fn (a, b) =>
                      let
                        fun flip LESS = GREATER | flip GREATER = LESS
                          | flip EQUAL = EQUAL
                      in
                        Date.compare (a, b) = flip (Date.compare (b, a))
                      end),

          P.forAll ("ordering by date agrees with ordering by instant",
                    G.pair (genDate, genDate), Show.pair (showDate, showDate),
                    fn (a, b) =>
                      Date.compare (a, b)
                      = Time.compare (Date.toTime a, Date.toTime b)),

          P.forAll ("weekDay advances by one from one day to the next",
                    genDate, showDate,
                    fn d =>
                      let
                        fun index w =
                          case List.find (fn (_, x) => x = w)
                                 (ListPair.zip (List.tabulate (7, fn i => i),
                                                weekdays)) of
                              SOME (i, _) => i
                            | NONE => ~1
                        val next =
                          Date.fromTimeUniv
                            (Time.+ (Date.toTime d,
                                     Time.fromSeconds (LargeInt.fromInt 86400)))
                      in
                        index (Date.weekDay next) = (index (Date.weekDay d) + 1) mod 7
                      end),

          P.forAll ("the twelve-hour clock agrees with the twenty-four hour one",
                    genDate, showDate,
                    fn d =>
                      let
                        val h = Date.hour d
                        val twelve = if h mod 12 = 0 then 12 else h mod 12
                      in
                        Date.fmt "%I" d
                        = StringCvt.padLeft #"0" 2 (Int.toString twelve)
                        andalso Date.fmt "%y" d
                                = StringCvt.padLeft #"0" 2
                                    (Int.toString (Date.year d mod 100))
                      end),

          P.forAll ("%w numbers the weekdays from Sunday", genDate, showDate,
                    fn d =>
                      let
                        val order = [Date.Sun, Date.Mon, Date.Tue, Date.Wed,
                                     Date.Thu, Date.Fri, Date.Sat]
                        fun index (w, i, x :: rest) =
                              if x = w then i else index (w, i + 1, rest)
                          | index (_, _, []) = ~1
                      in
                        Date.fmt "%w" d
                        = Int.toString (index (Date.weekDay d, 0, order))
                      end),

          P.forAll ("%j is the day of the year, counting from one",
                    genDate, showDate,
                    fn d =>
                      Date.fmt "%j" d
                      = StringCvt.padLeft #"0" 3
                          (Int.toString (Date.yearDay d + 1))),

          P.forAll ("an unknown directive stands for its own character",
                    G.map Char.chr (G.int (33, 126)), Show.char,
                    fn c =>
                      let
                        val known = "aAbBcdHIjmMpSUwWxXyYZ%"
                        val d = mk (2000, Date.Jan, 1, 0, 0, 0)
                      in
                        P.implies (not (Char.contains known c),
                                   Date.fmt ("%" ^ String.str c) d
                                   = String.str c)
                      end),

          P.forAll ("compare is the lexicographic order on the fields",
                    G.pair (genDate, genDate), Show.pair (showDate, showDate),
                    fn (a, b) =>
                      let
                        fun monthIndex (m, i, x :: rest) =
                              if x = m then i else monthIndex (m, i + 1, rest)
                          | monthIndex (_, _, []) = ~1
                        fun key d =
                          [Date.year d, monthIndex (Date.month d, 0, months),
                           Date.day d, Date.hour d, Date.minute d, Date.second d]
                        fun collate ([], []) = EQUAL
                          | collate (x :: xs, y :: ys) =
                              (case Int.compare (x, y) of
                                   EQUAL => collate (xs, ys)
                                 | other => other)
                          | collate _ = EQUAL
                      in
                        Date.compare (a, b) = collate (key a, key b)
                      end),

          P.forAll ("fmt of the individual fields agrees with the accessors",
                    genDate, showDate,
                    fn d =>
                      Date.fmt "%Y" d = StringCvt.padLeft #"0" 4
                                          (Int.toString (Date.year d))
                      andalso Date.fmt "%d" d = StringCvt.padLeft #"0" 2
                                                  (Int.toString (Date.day d))
                      andalso Date.fmt "%H" d = StringCvt.padLeft #"0" 2
                                                  (Int.toString (Date.hour d))
                      andalso Date.fmt "%M" d = StringCvt.padLeft #"0" 2
                                                  (Int.toString (Date.minute d))
                      andalso Date.fmt "%S" d = StringCvt.padLeft #"0" 2
                                                  (Int.toString (Date.second d)))
        ])
      ])
  end
