theory Byzantine_Drinks_Machine
  imports "../Contexts"
begin

definition select :: "transition" where
"select \<equiv> \<lparr>
        Label = STR ''select'',
        Arity = 1,
        Guard = [], \<comment> \<open> No guards \<close>
        Outputs = [],
        Updates = [ \<comment> \<open> Two updates: \<close>
                    (1, (V (I 1))), \<comment> \<open>  Firstly set value of r1 to value of i1 \<close>
                    (2, (L (Num 0))) \<comment> \<open> Secondly set the value of r2 to literal zero \<close>
                  ]
      \<rparr>"

(*select:1[]/[][(R 1, (V (I 1))), (R 2, (L (Num 0)))]*)

lemma guard_select: "Guard select = []"
  by (simp add: select_def)

lemma outputs_select: "Outputs select = []"
  by (simp add: select_def)

definition coin :: "transition" where
"coin \<equiv> \<lparr>
        Label = STR ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [Plus (V (R 2)) (V (I 1))],
        Updates = [
                    (1, V (R 1)),
                    (2, Plus (V (R 2)) (V (I 1)))
                  ]
      \<rparr>"

lemma label_coin: "Label coin = STR ''coin''"
  by (simp add: coin_def)

lemma guard_coin: "Guard coin = []"
  by (simp add: coin_def)

definition vend :: "transition" where
"vend \<equiv> \<lparr>
        Label = STR ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))],
        Outputs =  [(V (R 1))],
        Updates = [(1, V (R 1)), (2, V (R 2))]
      \<rparr>"

lemma label_vend: "Label vend = STR ''vend''"
  by (simp add: vend_def)

definition vend_fail :: "transition" where
"vend_fail \<equiv> \<lparr>
        Label = STR ''vend'',
        Arity = 0,
        Guard = [(GExp.Lt (V (R 2)) (L (Num 100)))],
        Outputs =  [],
        Updates = [(1, V (R 1)), (2, V (R 2))]
      \<rparr>"

definition drinks :: "transition_matrix" where
"drinks \<equiv> {|
          ((0,1), select),
          ((1,1), coin),
          ((1,1), vend_fail),
          ((1,20), vend)
         |}"

end
