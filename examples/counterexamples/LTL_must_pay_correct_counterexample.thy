theory LTL_must_pay_correct_counterexample
  imports "../coin-tea/Coin_Tea_Broken"
begin

abbreviation "Num \<equiv> value.Int"

lemma LTL_must_pay_correct_counterexample :
  "¬ (ev (state_eq (Some 2)) impl 
    (not (label_eq ''vend'') suntil label_eq ''coin''))
(watch drinks (
      (STR ''init'', [])##
      (STR ''vend'', [])##
      (STR ''vend'', [Num 42, Num 85])##
      (STR ''vend'', [Str ''tea''])##
      (STR ''vend'', [Str ''tea''])##
   trace))"
  apply (simp add: make_full_observation_step)
  apply (simp add: possible_steps_init init_def apply_updates_def possible_steps_vend_sufficient possible_steps_2)
  by (simp add: ev_Stream implode_coin implode_vend suntil_Stream)


end