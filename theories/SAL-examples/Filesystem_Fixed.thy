theory Filesystem_Fixed
imports Filesystem "../EFSM_LTL"
begin

text_raw{*\snip{write}{1}{2}{%*}
definition "write" :: "transition" where
"write \<equiv> \<lparr>
        Label = (STR ''write''),
        Arity = 1,
        Guard = [gexp.Eq (V (R 1)) (V (R 3))], \<comment>\<open> No guards \<close>
        Outputs = [],
        Updates = [
                    (1, (V (R 1))), \<comment>\<open> Value of r1 remains unchanged \<close>
                    (2, (V (I 1))), \<comment>\<open> Write the input to r2 \<close>
                    (3, (V (R 1)))  \<comment>\<open> Store the writer in r3 \<close>
                  ]
      \<rparr>"
text_raw{*}%endsnip*}

\<comment>\<open> Create the file if it doesn't already exist \<close>
definition create :: "transition" where
"create \<equiv> \<lparr>
        Label = (STR ''create''),
        Arity = 0,
        Guard = [(Null (V (R 3)))],
        Outputs = [],
        Updates = [
                    (1, (V (R 1))),
                    (2, (V (R 2))),
                    (3, (V (R 1)))  \<comment>\<open> Initialise the current user as the file owner \<close>
                  ]
      \<rparr>"

definition "write_fail" :: "transition" where
"write_fail \<equiv> \<lparr>
        Label = (STR ''write''),
        Arity = 1,
        Guard = [(Ne (V (R 3)) (V (R 1)))],
        Outputs = [L (Str ''accessDenied'')],
        Updates = []
      \<rparr>"

lemma arity_write_fail: "Arity write_fail = 1"
  by (simp add: write_fail_def)

lemma guard_write_fail: "Guard write_fail = [(Ne (V (R 3)) (V (R 1)))]"
  by (simp add: write_fail_def)

text_raw{*\snip{filesystem}{1}{2}{%*}
definition filesystem :: "transition_matrix" where
"filesystem \<equiv> {|
              ((0,1), login),
              ((1,0), logout),
              ((1,1), write),
              ((1,1), read_success),
              ((1,1), read_fail),
              ((1,1), write_fail),
              ((1,1), create)
         |}"
text_raw{*}%endsnip*}

\<comment>\<open> export_code filesystem in "Scala" \<close>

declare One_nat_def [simp del]

lemmas transitions = login_def logout_def write_def read_success_def read_fail_def write_fail_def create_def

lemma possible_steps_0: "possible_steps Filesystem_Fixed.filesystem 0 r (STR ''login'') [u] = {|(1, login)|}"
  apply (simp add: possible_steps_def transitions filesystem_def)
  by force

lemma possible_steps_1_create: "r 3 = None \<Longrightarrow> possible_steps filesystem 1 r (STR ''create'') [] = {|(1, create)|}"
  apply (simp add: possible_steps_singleton filesystem_def)
  apply safe
  by (simp_all add: transitions apply_guards)

lemma possible_steps_1_write:  "r 1 = r 3 \<Longrightarrow> possible_steps Filesystem_Fixed.filesystem 1 r (STR ''write'') [Num 50] = {|(1, write)|}"
  apply (simp add: possible_steps_singleton filesystem_def)
  apply safe
  by (simp_all add: transitions apply_guards)

lemma possible_steps_1_read: "r 1 = r 3 \<Longrightarrow> r 2 \<noteq> None \<Longrightarrow> possible_steps Filesystem_Fixed.filesystem 1 r (STR ''read'') [] = {|(1, read_success)|}"
  apply (simp add: possible_steps_singleton filesystem_def)
  apply safe
  by (simp_all add: transitions apply_guards)

lemma "observe_trace filesystem 0 <> [((STR ''login''), [Str ''user'']), ((STR ''create''), []), ((STR ''write''), [Num 50]), ((STR ''read''), [])] = [[], [], [], [Some (Num 50)]]"
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_0)
    apply (simp add: login_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_1_create login_def)
    apply (simp add: create_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_1_write create_def)
    apply (simp add: write_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply simp
     apply (rule possible_steps_1_read)
      apply (simp add: write_def create_def login_def)
     apply (simp add: write_def create_def login_def datastate)
    apply (simp add: apply_outputs transitions)
   apply simp
  by simp


lemma possible_steps_1_read_fail: "r 3 = Some owner \<and> r 1 = Some user \<and> owner \<noteq> user \<Longrightarrow> possible_steps Filesystem_Fixed.filesystem 1 r (STR ''read'') [] = {|(1, read_fail)|}"
  apply (simp add: possible_steps_singleton filesystem_def)
  apply safe
  by (simp_all add: transitions apply_guards)

lemma read_2:  " r = <1:= user, 2:= content, 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem 1 r (STR ''read'') [] = Some (read_fail, 1, [Some (Str ''accessDenied'')], r)"
  apply (rule one_possible_step)
    defer
    apply (simp add: read_fail_def apply_outputs)
   apply (rule ext)
   apply (simp add: read_fail_def datastate)
  apply (simp add: possible_steps_singleton filesystem_def)
  apply safe
  by (simp_all add: transitions apply_guards)

lemma possible_steps_1_logout:  "possible_steps Filesystem_Fixed.filesystem 1 r (STR ''logout'') [] = {|(0, logout)|}"
  apply (simp add: possible_steps_def transitions filesystem_def)
  by force

lemma logout_2:  "step filesystem 1 r (STR ''logout'') [] = Some (logout, 0, [], r)"
  apply (rule one_possible_step)
    defer
    apply (simp add: apply_outputs logout_def)
   apply (rule ext)
   apply (simp add: datastate logout_def)
  apply (simp add: filesystem_def possible_steps_singleton)
  apply safe
  by (simp_all add: transitions apply_guards)

abbreviation label_not_logout :: "property" where
  "label_not_logout s \<equiv> (label (shd s) \<noteq> (STR ''logout''))"

abbreviation label_logout :: "property" where
  "label_logout s \<equiv> (label (shd s) = (STR ''logout''))"

abbreviation label_create :: "property" where
  "label_create s \<equiv> (label (shd s) = (STR ''create''))"

abbreviation read_0 :: "property" where
  "read_0 s \<equiv> (label (shd s)=(STR ''read'') \<longrightarrow> output (shd s)=[Some (Str ''accessDenied'')])"

abbreviation login_attacker :: "property" where
  "login_attacker s \<equiv> (event (shd s) = ((STR ''login''),  [Str ''attacker'']))"

abbreviation login_user :: "property" where
  "login_user s \<equiv> (event (shd s) = ((STR ''login''),  [Str ''user'']))"

lemma "login_user (watch filesystem i) \<Longrightarrow> shd i = ((STR ''login''), [Str ''user''])"
  by (simp add: watch_def)

lemma logout_label:  "t = logout \<Longrightarrow> Label t = (STR ''logout'')"
  by (simp add: logout_def)

lemma create_label:  "t = create \<Longrightarrow> Label t = (STR ''create'')"
  by (simp add: create_def)

lemma implode_login: "String.implode ''login'' = STR ''login''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

text_raw{*\snip{userdetails}{1}{2}{%*}
lemma LTL_user_details_stored_in_r1: "((label_eq ''login'' aand input_eq [u]) impl
                                      (nxt (check_inx rg 1 value_eq (Some u)))) (watch filesystem i)"
  by (simp add: event_components implode_login possible_steps_0 login_def watch_def value_eq_def datastate)  
text_raw{*}%endsnip*}

end