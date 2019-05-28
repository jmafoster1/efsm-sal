theory LiftXXX
imports "../Contexts"
begin

definition "goUp" :: "transition" where
"goUp \<equiv> \<lparr>
      Label = STR ''goUp'',
      Arity = 1,
      Guard = [
            GExp.Gt (V (I 1)) (L (Num 0))
      ],
      Outputs = [
            (V (I 1))
      ],
      Updates = []
\<rparr>"

definition "goUp1" :: "transition" where
"goUp1 \<equiv> \<lparr>
      Label = STR ''goUp'',
      Arity = 1,
      Guard = [
            GExp.Gt (V (I 1)) (L (Num 0))
      ],
      Outputs = [
            Plus (V (I 1)) (L (Num (-1)))
      ],
      Updates = []
\<rparr>"

definition "goUp2" :: "transition" where
"goUp2 \<equiv> \<lparr>
      Label = STR ''goUp'',
      Arity = 1,
      Guard = [
            GExp.Eq (V (I 1)) (L (Num 0))
      ],
      Outputs = [
            (L (Num 0))
      ],
      Updates = []
\<rparr>"

definition "goDown" :: "transition" where
"goDown \<equiv> \<lparr>
      Label = STR ''goDown'',
      Arity = 1,
      Guard = [
            GExp.Gt (V (I 1)) (L (Num 0))
      ],
      Outputs = [
            (V (I 1))
      ],
      Updates = []
\<rparr>"

definition "goDown1" :: "transition" where
"goDown1 \<equiv> \<lparr>
      Label = STR ''goDown'',
      Arity = 1,
      Guard = [
            GExp.Gt (V (I 1)) (L (Num 0))
      ],
      Outputs = [
            Plus (V (I 1)) (L (Num (-1)))
      ],
      Updates = []
\<rparr>"

definition "goDown2" :: "transition" where
"goDown2 \<equiv> \<lparr>
      Label = STR ''goDown'',
      Arity = 1,
      Guard = [
            GExp.Eq (V (I 1)) (L (Num 0))
      ],
      Outputs = [
            (L (Num 0))
      ],
      Updates = []
\<rparr>"

definition "open" :: "transition" where
"open \<equiv> \<lparr>
      Label = STR ''open'',
      Arity = 0,
      Guard = [],
      Outputs = [
            (L (Num 1))
      ],
      Updates = []
\<rparr>"

definition "close" :: "transition" where
"close \<equiv> \<lparr>
      Label = STR ''close'',
      Arity = 0,
      Guard = [],
      Outputs = [
            (L (Num 0))
      ],
      Updates = []
\<rparr>"

definition "efsm" :: "transition_matrix" where
"efsm \<equiv> {|
      ((0, 1), goUp),
      ((1, 1), goUp1),
      ((1, 0), goUp2),
      ((0, 2), goDown),
      ((2, 2), goDown1),
      ((2, 0), goDown2),
      ((0, 3), open),
      ((3, 0), close)
|}"

end
