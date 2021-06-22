source "../../assert.sh/assert.sh"

# Coin tea
OUTPUT=$(sal-smc --assertion='coin_tea{2}!LTL_label_vend_not_2')
assert_eq "$OUTPUT" "proved." "LTL_label_vend_not_2 should be true."

OUTPUT=$(sal-smc --assertion='coin_tea{2}!LTL_aux2')
assert_eq "$OUTPUT" "proved." "LTL_aux2 should be true."

OUTPUT=$(sal-smc --assertion='coin_tea{2}!LTL_init_makes_r_1_zero')
assert_eq "$OUTPUT" "proved." "LTL_init_makes_r_1_zero should be true."

OUTPUT=$(sal-smc --assertion='coin_tea{2}!LTL_vend_no_coin')
assert_eq "$OUTPUT" "proved." "LTL_init_makes_r_1_zero should be true."

OUTPUT=$(sal-smc --assertion='coin_tea{2}!LTL_invalid_gets_stuck_2')
assert_eq "$OUTPUT" "proved." "LTL_invalid_gets_stuck_2 should be true."

OUTPUT=$(sal-smc --assertion='coin_tea{2}!LTL_must_pay_correct')
assert_eq "$OUTPUT" "proved." "LTL_must_pay_correct should be true."

OUTPUT=$(sal-smc --assertion='coin_tea{2}!LTL_must_pay_correct_bracketed')
assert_eq "$OUTPUT" "proved." "LTL_init_makes_r_1_zero should be true."

# Coin tea broken
OUTPUT=$(sal-smc --assertion='coin_tea_broken{2}!LTL_label_vend_not_2')
assert_eq "$OUTPUT" "proved." "LTL_label_vend_not_2 should be true."

OUTPUT=$(sal-smc --assertion='coin_tea_broken{2}!LTL_init_makes_r_1_zero')
assert_eq "$OUTPUT" "proved." "LTL_init_makes_r_1_zero should be true."

OUTPUT=$(sal-smc --assertion='coin_tea_broken{2}!LTL_vend_no_coin')
assert_contain "$OUTPUT" "Counterexample" "LTL_vend_no_coin should be true."

OUTPUT=$(sal-smc --assertion='coin_tea_broken{2}!LTL_invalid_gets_stuck_2')
assert_eq "$OUTPUT" "proved." "LTL_invalid_gets_stuck_2 should be true."

OUTPUT=$(sal-smc --assertion='coin_tea_broken{2}!LTL_must_pay_correct')
assert_contain "$OUTPUT" "Counterexample" "LTL_must_pay_correct should have a counterexample."

OUTPUT=$(sal-smc --assertion='coin_tea_broken{2}!LTL_must_pay_correct_bracketed')
assert_contain "$OUTPUT" "Counterexample" "LTL_must_pay_correct_bracketed should have a counterexample."
