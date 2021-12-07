theory Lift_Controller
imports "Extended_Finite_State_Machines.EFSM"
begin

definition "continit" :: "transition" where
"continit \<equiv> \<lparr>
      Label = STR ''continit'',
      Arity = 0,
      Guards = [],
      Outputs = [],
      Updates = [
            (1, (L (Str ''true'')))
      ]
\<rparr>"

definition "motorstop4" :: "transition" where
"motorstop4 \<equiv> \<lparr>
      Label = STR ''motorstop'',
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

definition "motorstop3" :: "transition" where
"motorstop3 \<equiv> \<lparr>
      Label = STR ''motorstop'',
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

definition "motorstop2" :: "transition" where
"motorstop2 \<equiv> \<lparr>
      Label = STR ''motorstop'',
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

definition "motorstop1" :: "transition" where
"motorstop1 \<equiv> \<lparr>
      Label = STR ''motorstop'',
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

abbreviation "startsearch" :: "transition" where
"startsearch \<equiv> \<lparr>
      Label = STR ''startsearch'',
      Arity = 2,
      Guards = [
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''false'')))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "opendoor4" :: "transition" where
"opendoor4 \<equiv> \<lparr>
      Label = STR ''opendoor'',
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

definition "opendoor3" :: "transition" where
"opendoor3 \<equiv> \<lparr>
      Label = STR ''opendoor'',
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

definition "opendoor2" :: "transition" where
"opendoor2 \<equiv> \<lparr>
      Label = STR ''opendoor'',
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

definition "opendoor1" :: "transition" where
"opendoor1 \<equiv> \<lparr>
      Label = STR ''opendoor'',
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

definition "return4" :: "transition" where
"return4 \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guards = [
            (Eq (V (R 4)) (L (Num 4)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return3" :: "transition" where
"return3 \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guards = [
            (Eq (V (R 4)) (L (Num 3)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return2" :: "transition" where
"return2 \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guards = [
            (Eq (V (R 4)) (L (Num 2)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "return1" :: "transition" where
"return1 \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guards = [
            (Eq (V (R 4)) (L (Num 1)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "down43stop" :: "transition" where
"down43stop \<equiv> \<lparr>
      Label = STR ''down'',
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

definition "down43" :: "transition" where
"down43 \<equiv> \<lparr>
      Label = STR ''down'',
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

definition "up34stop" :: "transition" where
"up34stop \<equiv> \<lparr>
      Label = STR ''up'',
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

definition "down32stop" :: "transition" where
"down32stop \<equiv> \<lparr>
      Label = STR ''down'',
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

definition "down32" :: "transition" where
"down32 \<equiv> \<lparr>
      Label = STR ''down'',
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

definition "up23stop" :: "transition" where
"up23stop \<equiv> \<lparr>
      Label = STR ''up'',
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

definition "up23" :: "transition" where
"up23 \<equiv> \<lparr>
      Label = STR ''up'',
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

definition "down21stop" :: "transition" where
"down21stop \<equiv> \<lparr>
      Label = STR ''down'',
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

definition "up12stop" :: "transition" where
"up12stop \<equiv> \<lparr>
      Label = STR ''up'',
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

definition "up12" :: "transition" where
"up12 \<equiv> \<lparr>
      Label = STR ''up'',
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

definition "init \<equiv> 0"
definition "search \<equiv> 9"

definition "o1 \<equiv> 5"
definition "o2 \<equiv> 6"
definition "o3 \<equiv> 7"
definition "o4 \<equiv> 8"

definition "f1 \<equiv> 1"
definition "f2 \<equiv> 2"
definition "f3 \<equiv> 3"
definition "f4 \<equiv> 4"

definition "o n = n + 4"

lemmas states[simp] = init_def search_def o1_def o2_def o3_def o4_def f1_def f2_def f3_def f4_def o_def

(*
definition lift :: transition_matrix where
  "lift = {|((0, 9), continit), ((9, 4), return4), ((9, 3), return3), ((9, 2), return2), ((9, 1), return1), ((8, 9), startsearch),
      ((8, 8), opendoor4), ((7, 9), startsearch), ((7, 7), opendoor3), ((6, 9), startsearch), ((6, 6), opendoor2),
      ((5, 9), startsearch), ((5, 5), opendoor1), ((4, 8), motorstop4), ((4, 3), down43stop), ((4, 3), down43),
      ((3, 7), motorstop3), ((3, 4), up34stop), ((3, 2), down32stop), ((3, 2), down32), ((2, 6), motorstop2),
      ((2, 3), up23stop), ((2, 3), up23), ((2, 1), down21stop), ((1, 5), motorstop1), ((1, 2), up12stop), ((1, 2), up12)|}"
*)

definition "lift" :: "transition_matrix" where
"lift \<equiv> {|
    ((init, search), continit),

    ((search, f4), return4),
    ((search, f3), return3),
    ((search, f2), return2),
    ((search, f1), return1),

    ((o4, search), startsearch),
    ((o4, o4), opendoor4),

    ((o3, search), startsearch),
    ((o3, o3), opendoor3),

    ((o2, search), startsearch),
    ((o2, o2), opendoor2),

    ((o1, search), startsearch),
    ((o1, o1), opendoor1),

    ((f4, o4), motorstop4),
    ((f4, f3), down43stop),
    ((f4, f3), down43),

    ((f3, o3), motorstop3),
    ((f3, f4), up34stop),
    ((f3, f2), down32stop),
    ((f3, f2), down32),

    ((f2, o2), motorstop2),
    ((f2, f3), up23stop),
    ((f2, f3), up23),
    ((f2, f1), down21stop),

    ((f1, o1), motorstop1),
    ((f1, f2), up12stop),
    ((f1, f2), up12)
  |}"

(*
lemma lift_lit: "lift_lit = lift"
  unfolding lift_def init_def search_def f1_def f2_def f3_def f4_def o1_def o2_def o3_def o4_def
  by (simp add: lift_def lift_lit_def)
*)


lemmas transitions =
  continit_def
  motorstop4_def
  motorstop3_def
  motorstop2_def
  motorstop1_def
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

abbreviation return :: "int \<Rightarrow> transition" where
"return n \<equiv> \<lparr>
      Label = STR ''return'',
      Arity = 0,
      Guards = [
            (Eq (V (R 4)) (L (Num n)))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

abbreviation motorstop :: "int \<Rightarrow> transition" where
"motorstop n \<equiv> \<lparr>
      Label = STR ''motorstop'',
      Arity = 2,
      Guards = [
            (Eq (V (R 1)) (L (Str ''true''))),
            (Eq (V (I 0)) (L (Str ''true''))),
            (Eq (V (I 1)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Num 0)),
            (L (Num n)),
            (L (Str ''true''))
      ],
      Updates = []
\<rparr>"

abbreviation opendoor :: "int \<Rightarrow> transition" where
"opendoor n \<equiv> \<lparr>
      Label = STR ''opendoor'',
      Arity = 1,
      Guards = [
            (Eq (V (I 0)) (L (Str ''true'')))
      ],
      Outputs = [
            (L (Str ''true'')),
            (L (Num n))
      ],
      Updates = []
\<rparr>"

declare size_fset_overloaded_simps [simp del]

lemmas can_take = can_take_def can_take_transition_def

lemma implode_true [simp]: "String.implode ''true'' = STR ''true''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_fslse [simp]: "String.implode ''false'' = STR ''false''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma outgoing_transitions_0:
  "outgoing_transitions lift 0 = {|((0, 9), continit)|}"
  by eval

lemma outgoing_transitions_1:
  "outgoing_transitions lift 1 = {|((1, f2), up12), ((1, f2), up12stop), ((1, o1), motorstop 1) |}"
  by eval

lemma outgoing_transitions_2:
  "outgoing_transitions lift 2 = {|((f2, o2), motorstop2),
    ((f2, f3), up23stop),
    ((f2, f3), up23),
    ((f2, f1), down21stop)|}"
  by eval

lemma outgoing_transitions_3:
  "outgoing_transitions lift 3 = {|
    ((f3, o3), motorstop3),
    ((f3, f4), up34stop),
    ((f3, f2), down32stop),
    ((f3, f2), down32)
|}"
  by eval

lemma outgoing_transitions_9:
  "outgoing_transitions lift 9 = {|
    ((search, f4), return4),
    ((search, f3), return3),
    ((search, f2), return2),
    ((search, f1), return1)
|}"
  by eval

lemma outgoing_transitions_4:
  "outgoing_transitions lift 4 = {|
    ((f4, o4), motorstop4),
    ((f4, f3), down43stop),
    ((f4, f3), down43)
|}"
  by eval

lemma outgoing_transitions_o:
  "s \<in> {5, 6, 7, 8} \<Longrightarrow>
outgoing_transitions lift s = {|
    ((s, search), startsearch),
    ((s, s), opendoor (int s - 4))
|}"

  apply (simp add: lift_def)

  apply (simp add: outgoing_transitions_def)
  apply (simp add: Abs_ffilter set_eq_iff)
  apply clarify
  apply (simp add: lift_def transitions)
  apply (case_tac "a=5")
   apply auto[1]
  apply (case_tac "a=6")
   apply auto[1]
  apply (case_tac "a=7")
   apply auto[1]
  apply (case_tac "a=8")
  by auto

lemma choice_return: "choice (return n) (return n') \<Longrightarrow> n = n'"
  apply (simp add: choice_def)
  using value_eq_true by auto

lemma deterministic_lift: "deterministic lift"
  apply (rule outgoing_transitions_fprod_deterministic)
  apply (case_tac "s=0")
   apply (simp add: outgoing_transitions_0)
  apply (case_tac "s=1")
   apply (simp add: outgoing_transitions_1)
   apply (case_tac "ba=up12")
    apply (case_tac "bc=motorstop 1")
     apply (simp add: transitions choice_def apply_guards_def Str_def)
    apply (case_tac "bc=up12stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
   apply (case_tac "ba=up12stop")
    apply (case_tac "bc=motorstop 1")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=up12")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
   apply (case_tac "ba=motorstop 1")
    apply (case_tac "bc=up12")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=up12stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply simp
  apply simp
  apply (case_tac "s=2")
  apply (simp add: outgoing_transitions_2)
   apply (case_tac "ba=motorstop2")
    apply (case_tac "bc=up23stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=up23")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=down21stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
   apply (case_tac "ba=up23stop")
    apply (case_tac "bc=motorstop2")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=up23")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=down21stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
   apply (case_tac "ba=up23")
    apply (case_tac "bc=motorstop2")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=up23stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=down21stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
  apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
   apply (case_tac "ba=down21stop")
    apply (case_tac "bc=motorstop2")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=up23stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=up23")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
  apply simp
  apply (case_tac "s=3")
  apply (simp add: outgoing_transitions_3)
 apply (case_tac "ba=motorstop3")
    apply (case_tac "bc=up34stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=down32")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=down32stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
 apply (case_tac "ba=up34stop")
    apply (case_tac "bc=motorstop3")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=down32")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=down32stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
  apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
 apply (case_tac "ba=down32")
    apply (case_tac "bc=motorstop3")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=up34stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=down32stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
  apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
 apply (case_tac "ba=down32stop")
    apply (case_tac "bc=motorstop3")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=up34stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=down32")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
  apply simp

  apply (case_tac "s=4")
  apply (simp add: outgoing_transitions_4)
 apply (case_tac "ba=motorstop4")
    apply (case_tac "bc=down43stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=down43")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
 apply (case_tac "ba=down43stop")
    apply (case_tac "bc=motorstop4")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=down43")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
  apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
 apply (case_tac "ba=down43")
    apply (case_tac "bc=down43stop")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (case_tac "bc=motorstop4")
     apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply (simp add: transitions choice_def apply_guards_def Str_def value_eq_true)
    apply simp

  apply (case_tac "s\<in>{5, 6, 7, 8}")
   apply (simp add: outgoing_transitions_o)
   apply (case_tac "bc=startsearch")
    apply auto[1]
   apply auto[1]

  apply (case_tac "s=9")
   apply (simp add: outgoing_transitions_9)
  apply (simp add: transitions)
  using choice_return apply fastforce (* ~5s *)
  by (simp add: lift_def outgoing_transitions_def)

end
