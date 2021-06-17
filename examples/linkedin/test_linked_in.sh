source "../../assert.sh/assert.sh"

OUTPUT=$(sal-smc --assertion='linked_in{2}!LTL_neverDetailed')
assert_contain "$OUTPUT" "Counterexample" "LTL_neverDetailed should be true."

OUTPUT=$(sal-smc --assertion='linked_in_fixed{2}!LTL_neverDetailed')
assert_eq "$OUTPUT" "proved." "alw_must_stop_to_open should be true."
