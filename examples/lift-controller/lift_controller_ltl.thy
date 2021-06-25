(* Generated by the SAL to Isabelle Translator *)
(* Version 1.5 released 25 June 2021 *)

theory lift_controller_ltl
imports "EFSM.EFSM_LTL" Lift_Controller_LTL
begin

declare One_nat_def [simp del]
declare ltl_step_alt [simp]

definition continit :: "transition" where
"continit \<equiv> \<lparr>
    Label = (STR ''continit''),
    Arity = 0,
    Guards = [],
    Outputs = [],
    Updates = [
      (1, (L (Str ''true'')))
    ]
\<rparr>"

definition motorstop4 :: "transition" where
"motorstop4 \<equiv> \<lparr>
    Label = (STR ''motorstop''),
    Arity = 2,
    Guards = [
      (Eq (V (R 1)) (L (Str ''true''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Num 0)),
      (L (Num 4)),
      (L (Str ''true''))
    ],
    Updates = []
\<rparr>"

definition motorstop3 :: "transition" where
"motorstop3 \<equiv> \<lparr>
    Label = (STR ''motorstop''),
    Arity = 2,
    Guards = [
      (Eq (V (R 1)) (L (Str ''true''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Num 0)),
      (L (Num 3)),
      (L (Str ''true''))
    ],
    Updates = []
\<rparr>"

definition motorstop2 :: "transition" where
"motorstop2 \<equiv> \<lparr>
    Label = (STR ''motorstop''),
    Arity = 2,
    Guards = [
      (Eq (V (R 1)) (L (Str ''true''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Num 0)),
      (L (Num 2)),
      (L (Str ''true''))
    ],
    Updates = []
\<rparr>"

definition motorstop1 :: "transition" where
"motorstop1 \<equiv> \<lparr>
    Label = (STR ''motorstop''),
    Arity = 2,
    Guards = [
      (Eq (V (R 1)) (L (Str ''true''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Num 0)),
      (L (Num 1)),
      (L (Str ''true''))
    ],
    Updates = []
\<rparr>"

definition startsearch :: "transition" where
"startsearch \<equiv> \<lparr>
    Label = (STR ''startsearch''),
    Arity = 2,
    Guards = [
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''false'')))
    ],
    Outputs = [],
    Updates = []
\<rparr>"

definition opendoor4 :: "transition" where
"opendoor4 \<equiv> \<lparr>
    Label = (STR ''opendoor''),
    Arity = 1,
    Guards = [
      (Eq (V (I 0)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Str ''true'')),
      (L (Num 4))
    ],
    Updates = []
\<rparr>"

definition opendoor3 :: "transition" where
"opendoor3 \<equiv> \<lparr>
    Label = (STR ''opendoor''),
    Arity = 1,
    Guards = [
      (Eq (V (I 0)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Str ''true'')),
      (L (Num 3))
    ],
    Updates = []
\<rparr>"

definition opendoor2 :: "transition" where
"opendoor2 \<equiv> \<lparr>
    Label = (STR ''opendoor''),
    Arity = 1,
    Guards = [
      (Eq (V (I 0)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Str ''true'')),
      (L (Num 2))
    ],
    Updates = []
\<rparr>"

definition opendoor1 :: "transition" where
"opendoor1 \<equiv> \<lparr>
    Label = (STR ''opendoor''),
    Arity = 1,
    Guards = [
      (Eq (V (I 0)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Str ''true'')),
      (L (Num 1))
    ],
    Updates = []
\<rparr>"

definition return4 :: "transition" where
"return4 \<equiv> \<lparr>
    Label = (STR ''return''),
    Arity = 0,
    Guards = [
      (Eq (V (R 4)) (L (Num 4)))
    ],
    Outputs = [],
    Updates = []
\<rparr>"

definition return3 :: "transition" where
"return3 \<equiv> \<lparr>
    Label = (STR ''return''),
    Arity = 0,
    Guards = [
      (Eq (V (R 4)) (L (Num 3)))
    ],
    Outputs = [],
    Updates = []
\<rparr>"

definition return2 :: "transition" where
"return2 \<equiv> \<lparr>
    Label = (STR ''return''),
    Arity = 0,
    Guards = [
      (Eq (V (R 4)) (L (Num 2)))
    ],
    Outputs = [],
    Updates = []
\<rparr>"

definition return1 :: "transition" where
"return1 \<equiv> \<lparr>
    Label = (STR ''return''),
    Arity = 0,
    Guards = [
      (Eq (V (R 4)) (L (Num 1)))
    ],
    Outputs = [],
    Updates = []
\<rparr>"

definition down43stop :: "transition" where
"down43stop \<equiv> \<lparr>
    Label = (STR ''down''),
    Arity = 3,
    Guards = [
      (Eq (V (R 2)) (L (Num 2))),
      (Eq (V (R 1)) (L (Str ''false''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true''))),
      (Eq (V (I 2)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Num 2)),
      (L (Str ''true''))
    ],
    Updates = [
      (4, (L (Num 3))),
      (1, (L (Str ''true'')))
    ]
\<rparr>"

definition down43 :: "transition" where
"down43 \<equiv> \<lparr>
    Label = (STR ''down''),
    Arity = 3,
    Guards = [
      (Eq (V (R 2)) (L (Num 2))),
      (Eq (V (R 1)) (L (Str ''false''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true''))),
      (Eq (V (I 2)) (L (Str ''false'')))
    ],
    Outputs = [
      (L (Num 2)),
      (L (Str ''false''))
    ],
    Updates = [
      (4, (L (Num 3))),
      (1, (L (Str ''false'')))
    ]
\<rparr>"

definition up34stop :: "transition" where
"up34stop \<equiv> \<lparr>
    Label = (STR ''up''),
    Arity = 2,
    Guards = [
      (Eq (V (R 2)) (L (Num 1))),
      (Eq (V (R 1)) (L (Str ''false''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Num 1)),
      (L (Str ''true''))
    ],
    Updates = [
      (4, (L (Num 4))),
      (1, (L (Str ''true'')))
    ]
\<rparr>"

definition down32stop :: "transition" where
"down32stop \<equiv> \<lparr>
    Label = (STR ''down''),
    Arity = 3,
    Guards = [
      (Eq (V (R 2)) (L (Num 2))),
      (Eq (V (R 1)) (L (Str ''false''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true''))),
      (Eq (V (I 2)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Num 2)),
      (L (Str ''true''))
    ],
    Updates = [
      (4, (L (Num 2))),
      (1, (L (Str ''true'')))
    ]
\<rparr>"

definition down32 :: "transition" where
"down32 \<equiv> \<lparr>
    Label = (STR ''down''),
    Arity = 3,
    Guards = [
      (Eq (V (R 2)) (L (Num 2))),
      (Eq (V (R 1)) (L (Str ''false''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true''))),
      (Eq (V (I 2)) (L (Str ''false'')))
    ],
    Outputs = [
      (L (Num 2)),
      (L (Str ''false''))
    ],
    Updates = [
      (4, (L (Num 2))),
      (1, (L (Str ''false'')))
    ]
\<rparr>"

definition up23stop :: "transition" where
"up23stop \<equiv> \<lparr>
    Label = (STR ''up''),
    Arity = 3,
    Guards = [
      (Eq (V (R 2)) (L (Num 1))),
      (Eq (V (R 1)) (L (Str ''false''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true''))),
      (Eq (V (I 2)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Num 1)),
      (L (Str ''true''))
    ],
    Updates = [
      (4, (L (Num 3))),
      (1, (L (Str ''true'')))
    ]
\<rparr>"

definition up23 :: "transition" where
"up23 \<equiv> \<lparr>
    Label = (STR ''up''),
    Arity = 3,
    Guards = [
      (Eq (V (R 2)) (L (Num 1))),
      (Eq (V (R 1)) (L (Str ''false''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true''))),
      (Eq (V (I 2)) (L (Str ''false'')))
    ],
    Outputs = [
      (L (Num 1)),
      (L (Str ''false''))
    ],
    Updates = [
      (4, (L (Num 3))),
      (1, (L (Str ''false'')))
    ]
\<rparr>"

definition down21stop :: "transition" where
"down21stop \<equiv> \<lparr>
    Label = (STR ''down''),
    Arity = 2,
    Guards = [
      (Eq (V (R 2)) (L (Num 2))),
      (Eq (V (R 1)) (L (Str ''false''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Num 2)),
      (L (Str ''true''))
    ],
    Updates = [
      (3, (L (Num 1))),
      (1, (L (Str ''true'')))
    ]
\<rparr>"

definition up12stop :: "transition" where
"up12stop \<equiv> \<lparr>
    Label = (STR ''up''),
    Arity = 3,
    Guards = [
      (Eq (V (R 2)) (L (Num 1))),
      (Eq (V (R 1)) (L (Str ''false''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true''))),
      (Eq (V (I 2)) (L (Str ''true'')))
    ],
    Outputs = [
      (L (Num 1)),
      (L (Str ''true''))
    ],
    Updates = [
      (1, (L (Str ''true''))),
      (4, (L (Num 2)))
    ]
\<rparr>"

definition up12 :: "transition" where
"up12 \<equiv> \<lparr>
    Label = (STR ''up''),
    Arity = 3,
    Guards = [
      (Eq (V (R 2)) (L (Num 1))),
      (Eq (V (R 1)) (L (Str ''false''))),
      (Eq (V (I 0)) (L (Str ''true''))),
      (Eq (V (I 1)) (L (Str ''true''))),
      (Eq (V (I 2)) (L (Str ''false'')))
    ],
    Outputs = [
      (L (Num 1)),
      (L (Str ''false''))
    ],
    Updates = [
      (4, (L (Num 2))),
      (1, (L (Str ''false'')))
    ]
\<rparr>"


definition lift :: "transition_matrix" where
"lift \<equiv> {|
    ((0, 9), continit),
    ((4, 8), motorstop4),
    ((3, 7), motorstop3),
    ((2, 6), motorstop2),
    ((1, 5), motorstop1),
    ((8, 9), startsearch),
    ((7, 9), startsearch),
    ((6, 9), startsearch),
    ((5, 9), startsearch),
    ((8, 8), opendoor4),
    ((7, 7), opendoor3),
    ((6, 6), opendoor2),
    ((5, 5), opendoor1),
    ((9, 4), return4),
    ((9, 3), return3),
    ((9, 2), return2),
    ((9, 1), return1),
    ((4, 3), down43stop),
    ((4, 3), down43),
    ((3, 4), up34stop),
    ((3, 2), down32stop),
    ((3, 2), down32),
    ((2, 3), up23stop),
    ((2, 3), up23),
    ((2, 1), down21stop),
    ((1, 2), up12stop),
    ((1, 2), up12)
  |}"
  
  
lemmas transitions =
  continit_def
  motorstop4_def
  motorstop3_def
  motorstop2_def
  motorstop1_def
  startsearch_def
  opendoor4_def
  opendoor3_def
  opendoor2_def
  opendoor1_def
  return4_def
  return3_def
  return2_def
  return1_def
  down43stop_def
  down43_def
  up34stop_def
  down32stop_def
  down32_def
  up23stop_def
  up23_def
  down21stop_def
  up12stop_def
  up12_def

lemma lift_equiv [simp]: "lift = Lift_Controller.lift"
  apply (simp add: lift_def Lift_Controller.lift_def transitions Lift_Controller.transitions)
  by auto
  
lemma must_stop_to_open :
  "(not (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some (Num n)])) until
      label_eq ''motorstop'')
(watch lift trace)"
  using must_stop_to_open by simp

lemma must_stop_to_open_false :
  "(alw (not (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some (Num n)])) until
      label_eq ''motorstop''))
(watch lift trace)"
  oops (* Not true *)

lemma alw_must_stop_to_open :
  "(alw (ev (nxt (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some n]))) impl
      (not (nxt (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some n]))) until
      (label_eq ''motorstop'' or nxt (output_eq [Some (Str
      ''true''), Some n])))))
(watch lift trace)"
  using alw_must_stop_to_open by simp

lemma LTL_must_stop_lift_to_open_door :
  "(alw (ev (nxt (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some n]))) impl
      (not (nxt (label_eq ''opendoor'' aand
      nxt (output_eq [Some (Str ''true''), Some n]))) suntil
      (label_eq ''motorstop'' or nxt (output_eq [Some (Str
      ''true''), Some n])))))
(watch lift trace)"
  using LTL_must_stop_lift_to_open_door by simp

lemma LTL_must_stop_lift_to_open_door_ev :
  "(ev (state_eq (Some 5)) impl
      ev (output_eq [Some (Num 0), Some (Num 1), Some (Str
      ''true'')]))
(watch lift trace)"
oops (* Not true *)

end
