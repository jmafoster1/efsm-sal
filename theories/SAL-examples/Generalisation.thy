subsection{*Generalisation*}
text{*This theory presents a simple EFSM definition and uses contexts to prove
transition subsumption. 
*}
theory Generalisation
imports "../efsm-isabelle/Contexts" "../efsm-isabelle/examples/Drinks_Machine_2"
begin

definition select :: "transition" where
"select \<equiv> \<lparr>
        Label = (STR ''select''),
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Str ''coke'')))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 50)))],
        Outputs = [],
        Updates = []
      \<rparr>"

lemma guard_coin50: "Guard coin50 = [(gexp.Eq (V (I 1)) (L (Num 50)))]"
  by (simp add: coin50_def)

definition coin_init :: "transition" where
"coin_init \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(1, (V (I 1)))]
      \<rparr>"

lemma guard_coin_init: "Guard coin_init = []"
  by (simp add: coin_init_def)

definition coin_inc :: "transition" where
"coin_inc \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(1, (Plus (V (R 1)) (V (I 1))))]
      \<rparr>"

definition vends :: "transition" where
"vends \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [],
        Outputs =  [L (Num 1)],
        Updates = []
      \<rparr>"

lemma outputs_vends [simp]: "Outputs vends = [L (Num 1)]"
  by (simp add: vends_def)

lemma guard_vends [simp]: "Guard vends = []"
  by (simp add: vends_def)

lemma updates_vends [simp]: "Updates vends = []"
  by (simp add: vends_def)

definition vends_g :: "transition" where
"vends_g \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [(Ge (V (R 1)) (L (Num 100)))],
        Outputs =  [L (Num 1)],
        Updates = []
      \<rparr>"

lemma outputs_vends_g [simp]: "Outputs vends_g = [L (Num 1)]"
  by (simp add: vends_g_def)

lemma guard_vends_g [simp]: "Guard vends_g = [(Ge (V (R 1)) (L (Num 100)))]"
  by (simp add: vends_g_def)

definition venderr :: "transition" where
"venderr \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [],
        Outputs =  [],
        Updates = []
      \<rparr>"

definition venderr_g :: "transition" where
"venderr_g \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [(GExp.Lt (V (R 1)) (L (Num 100)))],
        Outputs =  [L (Num 1)],
        Updates = []
      \<rparr>"

definition vend :: transition_matrix where
"vend \<equiv> {|
              ((0,1), select),
              ((1,2), coin50),
              ((2,2), venderr),
              ((2,3), coin50),
              ((3,4), vends)
         |}"

definition vend_g :: transition_matrix where
"vend_g \<equiv> {|
              ((0,1), select),
              ((1,2), coin_init),
              ((2,2), venderr_g),
              ((2,2), coin_inc),
              ((2,3), vends_g)
         |}"

lemmas transitions = select_def coin_init_def vends_g_def venderr_g_def coin_inc_def coin50_def vends_def

lemma "subsumes coin_init <> coin50"
  by (simp add: subsumes_def coin_init_def coin50_def can_take_transition_def can_take_def posterior_separate_def)

lemma "subsumes coin_inc <> coin50"
  by (simp add: subsumes_def coin_inc_def coin50_def can_take_transition_def can_take_def posterior_separate_def)


lemma  "\<not>subsumes vends_g <> vends"
  apply (rule bad_guards)
  by (simp add: vends_g_def vends_def can_take_def can_take_transition_def apply_guards_def connectives value_gt_def)

lemma "r $ 1 = Some (Num n) \<Longrightarrow> n \<ge> 100 \<Longrightarrow> subsumes vends_g r vends"
  by (simp add: subsumes_def vends_g_def vends_def can_take_transition_def can_take_def apply_guards_def connectives value_gt_def)

definition test1 :: transition where
"test1 \<equiv> \<lparr>
        Label = (STR ''foo''),
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 6)))],
        Outputs =  [(L (Num 6))],
        Updates = [(1, (L (Num 6)))]
      \<rparr>"

definition test2 :: transition where
"test2 \<equiv> \<lparr>
        Label = (STR ''foo''),
        Arity = 1,
        Guard = [(gexp.Gt (V (I 1)) (L (Num 0)))],
        Outputs =  [(V (I 1))],
        Updates = [(1, (V (I 1)))]
      \<rparr>"

lemma test2_subsumes_test1: "subsumes test2 <> test1"
  apply (simp add: subsumes_def test1_def test2_def can_take_transition_def can_take_def apply_guards_def posterior_separate_def value_gt_def  apply_outputs_def)
  by auto
end