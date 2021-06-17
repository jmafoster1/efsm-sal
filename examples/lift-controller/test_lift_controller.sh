source "../../assert.sh/assert.sh"

OUTPUT=$(sal-smc --assertion='lift_controller_ltl{4}!must_stop_to_open')
assert_eq "$OUTPUT" "proved." "must_stop_to_open should be true. Don't forget to initialise r__4 to Some(Num(1))!"

OUTPUT=$(sal-smc --assertion='lift_controller_ltl{4}!must_stop_to_open_false')
assert_contain "$OUTPUT" "Counterexample" "must_stop_to_open_false should be false. Don't forget to initialise r__4 to Some(Num(1))!"

OUTPUT=$(sal-smc --assertion='lift_controller_ltl{4}!alw_must_stop_to_open')
assert_eq "$OUTPUT" "proved." "alw_must_stop_to_open should be true."

OUTPUT=$(sal-smc --assertion='lift_controller_ltl{4}!LTL_must_stop_lift_to_open_door')
assert_eq "$OUTPUT" "proved." "LTL_must_stop_lift_to_open_door should be true."

OUTPUT=$(sal-smc --assertion='lift_controller_ltl{4}!LTL_must_stop_lift_to_open_door_ev')
assert_eq "$OUTPUT" "proved." "LTL_must_stop_lift_to_open_door_ev should be true."
