(* Generated by the SAL Theorem to Isabelle Translator *)
(* Version 1.2 released 21 June 2021 *)
theory lift_controller_ltlTheorems
imports "EFSM.EFSM_LTL" Lift_Controller_LTL Lift_Controller_LTL

begin

lemma must_stop_to_open :
  "(not (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some (Num n)])) until
      label_eq ''motorstop'')
(watch lift trace)"
using must_stop_to_open by blast

lemma must_stop_to_open_false :
  "(alw (not (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some (Num n)])) until
      label_eq ''motorstop''))
(watch lift trace)"
using must_stop_to_open_false by blast

lemma alw_must_stop_to_open :
  "(alw (ev (nxt (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some n]))) impl
      (not (nxt (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some n]))) until
      (label_eq ''motorstop'' or nxt (output_eq [Some (Str
      ''true''), Some n])))))
(watch lift trace)"
using alw_must_stop_to_open by blast

lemma LTL_must_stop_lift_to_open_door :
  "(alw (ev (nxt (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some n]))) impl
      (not (nxt (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some n]))) suntil
      (label_eq ''motorstop'' or nxt (output_eq [Some (Str
      ''true''), Some n])))))
(watch lift trace)"
using LTL_must_stop_lift_to_open_door by blast

lemma LTL_must_stop_lift_to_open_door_ev :
  "(ev (state_eq (Some 5)) impl
      ev (output_eq [Some (Num 0), Some (Num 1), Some (Str
      ''true'')]))
(watch lift trace)"
using LTL_must_stop_lift_to_open_door_ev by blast

end


