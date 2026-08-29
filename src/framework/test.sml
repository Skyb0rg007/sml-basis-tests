(* test.sml -- the shape of a test tree.
 *
 * A Case is an ordinary unit test.  A Prop is a property: the function is one
 * trial, taking the size for that trial and threading the random state, and it
 * signals failure by raising Assert.TestFail.  Packaging a property as a
 * closure over its own generator is what lets properties of different element
 * types live in a single homogeneous tree.
 *)

structure Test =
  struct

    datatype test =
        Case  of string * (unit -> unit)
      | Prop  of string * (int -> Random.rand -> Random.rand)
      | Group of string * test list
        (* A test that does not apply to this configuration, carrying the
         * reason.  Dropping it silently would let a suite quietly shrink to
         * nothing on a system that declares everything unsupported, so a skip
         * is reported and counted like any other outcome. *)
      | Skip  of string * string

    fun nameOf (Case (n, _)) = n
      | nameOf (Prop (n, _)) = n
      | nameOf (Group (n, _)) = n
      | nameOf (Skip (n, _)) = n

    (* onlyIf (cond, reason) ts -- run ts only when cond holds. *)
    fun onlyIf (true, _) ts = ts
      | onlyIf (false, reason) ts =
          List.map (fn t => Skip (nameOf t, reason)) ts

  end

(* prop.sml -- building properties out of generators. *)
structure Prop =
  struct

    open Test

    fun describe (show, x) = " for input " ^ show x

    (* forAll (name, gen, show, pred) -- pred must hold for every generated
     * value.  An exception escaping pred is reported as a failure carrying the
     * input, since "the property raised Subscript on this input" is a finding,
     * not an infrastructure error. *)
    fun forAll (name, gen, show, pred) =
      Prop (name, fn size => fn r =>
        let
          val (x, r') = Gen.run gen size r
          val ok =
            pred x
            handle Assert.TestFail m =>
                     raise Assert.TestFail (m ^ describe (show, x))
                 | e =>
                     raise Assert.TestFail
                       ("raised " ^ exnName e ^ describe (show, x))
        in
          if ok then r'
          else raise Assert.TestFail ("falsified" ^ describe (show, x))
        end)

    (* Same, but the body asserts rather than returning a bool, so that the
     * report can say which of several conjuncts broke. *)
    fun forAllAssert (name, gen, show, check) =
      Prop (name, fn size => fn r =>
        let
          val (x, r') = Gen.run gen size r
        in
          (check x
           handle Assert.TestFail m =>
                    raise Assert.TestFail (m ^ describe (show, x))
                | e =>
                    raise Assert.TestFail
                      ("raised " ^ exnName e ^ describe (show, x)));
          r'
        end)

    (* Vacuous truth for conditional laws.  With no shrinking and no discard
     * accounting there is nothing to be gained from a separate "discarded"
     * outcome; a guarded law that is rarely triggered is a bad law. *)
    fun implies (premise, conclusion) = not premise orelse conclusion

    infix 4 ==>
    fun a ==> b = implies (a, b)

  end
