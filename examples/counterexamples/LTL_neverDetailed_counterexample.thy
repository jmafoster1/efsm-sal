theory LTL_neverDetailed_counterexample
  imports "../linkedin/Linked_In"
begin

lemma LTL_neverDetailed_counterexample :
  "¬ ((label_eq ''login'' aand 
    input_eq [Str ''free'']) impl 
    nxt (alw ((label_eq ''pdf'' aand 
    check_exp ((Eq (V (Ip 0)) (L (Str ''otherID''))))) impl 
    not (nxt (output_eq [Some (
    Str ''detailed_pdf_of_otherID'')])))))
(watch linkedIn (
      (STR ''login'', [Str ''free''])##
      (STR ''view'', [Str ''otherID'', Str ''name'', Str ''4zoF''])##
      (STR ''pdf'', [Str ''otherID'', Str ''name'', Str ''4zoF''])##
      (STR ''view'', [Num 4])##
      (STR ''login'', [Num 7, Num 2])##
   trace))"
  apply (simp add: make_full_observation_step not_alw_iff)
  apply (simp add: login_free implode_login apply_updates_def login_def view_hack view2_def pdf_fuzz possible_steps_7)
  apply (rule ev.step, simp)
  by (rule ev.base, simp add: implode_pdf join_iro_def pdf2_def apply_outputs_def)

end