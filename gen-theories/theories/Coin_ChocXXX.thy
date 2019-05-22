theory Coin_ChocXXX
imports "../Contexts"
begin

definition init :: "transition" where
"init \<equiv> \<lparr>
      Label = STR ''init'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (R 1, (L (Num 0)))
      ]
\<rparr>"

definition coin :: "transition" where
"coin \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (R 1, Plus (V (R 1)) (L (Num 1)))
      ]
\<rparr>"

definition vend :: "transition" where
"vend \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [
            GExp.Gt (V (R 1)) (L (Num 0))
      ],
      Outputs = [],
      Updates = [
            (R 1, Minus (V (R 1)) (L (Num 1)))
      ]
\<rparr>"

definition efsm :: "transition_matrix" where
"efsm \<equiv> {|
      ((0, 1), init),
      ((1, 1), coin),
      ((1, 2), vend)
|}"

end
