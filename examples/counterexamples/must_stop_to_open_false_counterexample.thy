theory must_stop_to_open_false_counterexample
  imports "../lift-controller/Lift_Controller_LTL"
begin

abbreviation "Num \<equiv> value.Int"

lemma must_stop_to_open_false_counterexample :
  "¬ (∀n. (alw (not (label_eq ''opendoor'' aand 
    nxt (output_eq [Some (Str ''true''), Some (Num n)])) until 
    label_eq ''motorstop''))
(make_full_observation lift (Some 0) <4 $r:= Some (Num 1)> [] (
      (STR ''continit'', [])##
      (STR ''return'', [])##
      (STR ''motorstop'', [Str ''true'', Str ''true''])##
      (STR ''opendoor'', [Str ''true''])##
      (STR ''opendoor'', [Str ''true''])##
      (STR ''up'', [Str ''dummy__'', Num 1, Num 3, Str ''false''])##
   trace)))"
  apply (simp add: make_full_observation_step)
  apply (rule_tac x=1 in exI)
  apply (simp add: possible_steps_0 continit_def apply_updates_def return motorstop_1 One_nat_def[symmetric] opendoor_1 possible_steps_5_invalid apply_outputs_def)
  apply (simp add: not_alw_iff)
  apply (rule ev.step, simp, rule ev.step, simp, rule ev.step, simp)
  apply (rule ev.base)
  apply (rule not_until)
   apply (simp add: nxt.simps)
  by simp
end