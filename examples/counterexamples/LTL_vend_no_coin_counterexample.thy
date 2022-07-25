theory LTL_vend_no_coin_counterexample
  imports "../coin-tea/Coin_Tea_Broken"
begin

abbreviation "Num \<equiv> value.Int"

lemma LTL_vend_no_coin_counterexample :
  "¬ (nxt (label_eq ''vend'' aand 
    input_eq []) impl not (ev (state_eq (Some 2))))
(watch drinks (
      (STR ''init'', [])##
      (STR ''vend'', [])##
      (STR ''vend'', [Str ''tea''])##
      (STR ''vend'', [Str ''tea'', Num 88])##
   trace))"
  apply (simp add: make_full_observation_step)
  apply (simp add: possible_steps_init init_def apply_updates_def possible_steps_vend_sufficient possible_steps_2)
  by (simp add: ev_Stream implode_coin implode_vend suntil_Stream)

end