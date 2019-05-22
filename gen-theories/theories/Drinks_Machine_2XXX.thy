theory Drinks_Machine_2XXX
imports "../Contexts"
begin

definition select :: "transition" where
"select \<equiv> \<lparr>
      Label = STR ''select'',
      Arity = 1,
      Guard = [],
      Outputs = [],
      Updates = [
            (R 1, (V (I 1))),
            (R 2, (L (Num 0)))
      ]
\<rparr>"

definition coin :: "transition" where
"coin \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 1,
      Guard = [],
      Outputs = [
            Plus (V (R 2)) (V (I 1))
      ],
      Updates = [
            (R 1, (V (R 1))),
            (R 2, Plus (V (R 2)) (V (I 1)))
      ]
\<rparr>"

definition coin1 :: "transition" where
"coin1 \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 1,
      Guard = [],
      Outputs = [
            Plus (V (R 2)) (V (I 1))
      ],
      Updates = [
            (R 1, (V (R 1))),
            (R 2, Plus (V (R 2)) (V (I 1)))
      ]
\<rparr>"

definition vend :: "transition" where
"vend \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [
            Ge (V (R 2)) (L (Num 100))
      ],
      Outputs = [
            (V (R 1))
      ],
      Updates = [
            (R 1, (V (R 1))),
            (R 2, (V (R 2)))
      ]
\<rparr>"

definition vend1 :: "transition" where
"vend1 \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [
            GExp.Lt (V (R 2)) (L (Num 100))
      ],
      Outputs = [],
      Updates = [
            (R 1, (V (R 1))),
            (R 2, (V (R 2)))
      ]
\<rparr>"

definition vend2 :: "transition" where
"vend2 \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (R 1, (V (R 1))),
            (R 2, (V (R 2)))
      ]
\<rparr>"

definition efsm :: "transition_matrix" where
"efsm \<equiv> {|
      ((0, 1), select),
      ((1, 2), coin),
      ((2, 2), coin1),
      ((2, 3), vend),
      ((2, 2), vend1),
      ((1, 1), vend2)
|}"

end