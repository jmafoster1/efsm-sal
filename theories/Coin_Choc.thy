theory Coin_Choc
  imports EFSM_LTL
begin

declare One_nat_def [simp del]
declare ValueLt_def [simp]

definition init :: transition where
"init \<equiv> \<lparr>
        Label = (STR ''init''),
        Arity = 0,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (L (Num 0)))]
      \<rparr>"

definition coin :: transition where
"coin \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 0,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (Plus (V (R 1)) (L (Num 1))))]
      \<rparr>"

definition vend :: transition where
"vend \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [gexp.Gt (V (R 1)) (L (Num 0))],
        Outputs = [],
        Updates = [(R 1, (Minus (V (R 1)) (L (Num 1))))]
      \<rparr>"

definition drinks :: "transition_matrix" where
"drinks \<equiv> {|
          ((0,1), init),
          ((1,1), coin),
          ((1,2), vend)
          |}"

lemma init_makes_r_1_zero: "((LabelEq ''init'' aand InputEq []) impl (nxt (checkInx rg 1 ValueEq (Some (Num 0)))) )(watch drinks t)"

(*  apply (case_tac "shd t = (STR ''init'', [])")
   apply (simp add: possible_steps_init updates_init ValueEq_def)
  apply clarify
  using not_init
  by simp  *)

lemma must_pay: "((not (LabelEq ''vend'' suntil LabelEq ''coin'')) suntil StateEq None) (watch drinks t)"
  oops


end
