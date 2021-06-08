source "../assert.sh/assert.sh"

OUTPUT=$(sal-smc --assertion='drinks_machine_ltl{102}!LTL_r2_not_always_gt_100')
assert_eq "$OUTPUT" "proved." "LTL_r2_not_always_gt_100 should be true."

OUTPUT=$(sal-smc --assertion='drinks_machine_ltl{102}!LTL_nxt_2_means_vend')
assert_eq "$OUTPUT" "proved." "LTL_nxt_2_means_vend should be true."

OUTPUT=$(sal-smc --assertion='drinks_machine_ltl{102}!LTL_costsMoney')
assert_eq "$OUTPUT" "proved." "LTL_costsMoney should be true."

OUTPUT=$(sal-smc --assertion='drinks_machine_ltl{102}!LTL_costsMoney_aux')
assert_eq "$OUTPUT" "proved." "LTL_costsMoney_aux should be true."

OUTPUT=$(sal-smc --assertion='drinks_machine_ltl{102}!LTL_neverReachS2')
assert_eq "$OUTPUT" "proved." "LTL_neverReachS2 should be true."

OUTPUT=$(sal-smc --assertion='drinks_machine_ltl{102}!LTL_drinks_cost_money')
assert_eq "$OUTPUT" "proved." "LTL_drinks_machine_ltl_cost_money should be true."

OUTPUT=$(sal-smc --assertion='drinks_machine_ltl{102}!LTL_output_vend')
assert_eq "$OUTPUT" "proved." "LTL_output_vend should be true."
