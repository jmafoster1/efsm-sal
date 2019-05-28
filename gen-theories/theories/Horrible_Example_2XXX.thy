theory Horrible_Example_2XXX
imports "../Contexts"
begin

definition "f" :: "transition" where
"f \<equiv> \<lparr>
      Label = STR ''f'',
      Arity = 1,
      Guard = [],
      Outputs = [],
      Updates = [
            (R 1, (V (I 1)))
      ]
\<rparr>"

definition "g" :: "transition" where
"g \<equiv> \<lparr>
      Label = STR ''g'',
      Arity = 0,
      Guard = [
            GExp.Gt (V (R 1)) (L (Num 5))
      ],
      Outputs = [],
      Updates = [
            (R 1, Plus (V (R 1)) (L (Num 5)))
      ]
\<rparr>"

definition "h" :: "transition" where
"h \<equiv> \<lparr>
      Label = STR ''h'',
      Arity = 0,
      Guard = [],
      Outputs = [],
      Updates = [
            (R 1, (V (R 1)))
      ]
\<rparr>"

definition "efsm" :: "transition_matrix" where
"efsm \<equiv> {|
      ((0, 1), f),
      ((1, 1), g),
      ((1, 2), h)
|}"

end
