source "../../assert.sh/assert.sh"

OUTPUT=$(sal-smc --assertion='lift_controller_ltl{2}!must_stop_to_open')
assert_eq "$OUTPUT" "proved." "must_stop_to_open should be true. Don't forget to initialise r__4 to Some(Str(NO__1))!"

OUTPUT=$(sal-smc --assertion='lift_controller_ltl{2}!must_stop_to_open_false')
assert_contain "$OUTPUT" "Counterexample" "LTL_must_stop_lift_to_open_door should be true."

OUTPUT=$(sal-smc --assertion='lift_controller_ltl{2}!alw_must_stop_to_open')
assert_eq "$OUTPUT" "proved." "alw_must_stop_to_open should be true."

OUTPUT=$(sal-smc --assertion='lift_controller_ltl{2}!LTL_must_stop_lift_to_open_door')
assert_eq "$OUTPUT" "proved." "LTL_must_stop_lift_to_open_door should be true."

OUTPUT=$(sal-smc --assertion='lift_controller_ltl{2}!LTL_must_stop_lift_to_open_door_ev')
assert_eq "$OUTPUT" "proved." "LTL_must_stop_lift_to_open_door_ev should be true."
