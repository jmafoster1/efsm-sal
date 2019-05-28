theory Inference_AnswerXXX
imports "../Contexts"
begin

definition "select" :: "transition" where
"select \<equiv> \<lparr>
      Label = STR ''select'',
      Arity = 1,
      Guard = [],
      Outputs = [],
      Updates = [
            (R 2, (L (Num 0))),
            (R 1, (V (I 1)))
      ]
\<rparr>"

definition "coin" :: "transition" where
"coin \<equiv> \<lparr>
      Label = STR ''coin'',
      Arity = 1,
      Guard = [],
      Outputs = [
            Plus (V (R 2)) (V (I 1))
      ],
      Updates = [
            (R 2, Plus (V (R 2)) (V (I 1))),
            (R 1, (V (R 1)))
      ]
\<rparr>"

definition "vend" :: "transition" where
"vend \<equiv> \<lparr>
      Label = STR ''vend'',
      Arity = 0,
      Guard = [],
      Outputs = [
            (V (R 1))
      ],
      Updates = [
            (R 1, (V (R 1))),
            (R 2, (V (R 2)))
      ]
\<rparr>"

definition "efsm" :: "transition_matrix" where
"efsm \<equiv> {|
      ((0, 1), select),
      ((1, 1), coin),
      ((1, 4), vend)
|}"

end
