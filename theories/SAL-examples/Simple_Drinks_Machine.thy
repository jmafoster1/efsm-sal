theory Simple_Drinks_Machine
imports "../Contexts" "Drinks_Machine_2"
begin

definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = (STR ''select''),
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(1, (V (I 1))), (2, (L (Num 0)))]
      \<rparr>"

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 50)))],
        Outputs = [(Plus (V (R 2)) (V (I 1)))],
        Updates = [(1, (V (R 1))),
                   (2, Plus (V (R 2)) (L (Num 50)))]
      \<rparr>"

definition coin :: "transition" where
"coin \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 1,
        Guard = [],
        Outputs = [(Plus (V (R 2)) (V (I 1)))],
        Updates = [
                  (1, (V (R 1))),
                  (2, (Plus (V (R 2)) (V (I 1))))
                ]
      \<rparr>"

lemma guard_coin: "Guard coin = []"
  by (simp add: coin_def)

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))],
        Outputs =  [(V (R 1))],
        Updates = [(1, (V (R 1))), (2, (V (R 2)))]
      \<rparr>"

definition vend :: transition_matrix where
"vend \<equiv>  {|
              ((0,1), t1), \<comment> \<open> If we want to go from state 1 to state 2, t1 will do that \<close>
              ((1,1), coin50), \<comment> \<open> If we want to go from state 2 to state 2, coin50 will do that \<close>
              ((1,2), t3) \<comment> \<open> If we want to go from state 2 to state 3, t3 will do that \<close>
         |}"

definition vend_equiv :: transition_matrix where
"vend_equiv \<equiv> {|
                ((0,1), t1),    \<comment> \<open> If we want to go from state 1 to state 2, t1 will do that \<close>
                ((1,1), coin),  \<comment> \<open> If we want to go from state 2 to state 2, coin will do that \<close>
                ((1,2), t3)     \<comment> \<open> If we want to go from state 2 to state 3, t3 will do that \<close>
              |}"


definition drinks2 :: transition_matrix where
"drinks2 \<equiv> {|
              ((0,1), select),
              ((1,1), vend_nothing),
              ((1,2), coin50),
              ((2,2), coin),
              ((2,2), vend_fail),
              ((2,3), Drinks_Machine.vend)
         |}"

lemmas transitions = Drinks_Machine_2.transitions coin_def coin50_def

end
