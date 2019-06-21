theory XXXlinkedin_ext
imports "../../EFSM_LTL"
begin

definition "login" :: "transition" where
"login \<equiv> \<lparr>
      Label = STR ''login'',
      Arity = 1,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''free''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "login1" :: "transition" where
"login1 \<equiv> \<lparr>
      Label = STR ''login'',
      Arity = 1,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''paid''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view" :: "transition" where
"view \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''friendID'')),
            GExp.Eq (V (I 2)) (L (Str ''name'')),
            GExp.Eq (V (I 3)) (L (Str ''HM8p''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view1" :: "transition" where
"view1 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''otherID'')),
            GExp.Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')),
            GExp.Eq (V (I 3)) (L (Str ''MNn5''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view2" :: "transition" where
"view2 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''otherID'')),
            GExp.Eq (V (I 2)) (L (Str ''name'')),
            GExp.Eq (V (I 3)) (L (Str ''4zoF''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "view3" :: "transition" where
"view3 \<equiv> \<lparr>
      Label = STR ''view'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''otherID'')),
            GExp.Eq (V (I 2)) (L (Str ''name'')),
            GExp.Eq (V (I 3)) (L (Str ''MNn5''))
      ],
      Outputs = [],
      Updates = []
\<rparr>"

definition "pdf" :: "transition" where
"pdf \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''friendID'')),
            GExp.Eq (V (I 2)) (L (Str ''name'')),
            GExp.Eq (V (I 3)) (L (Str ''HM8p''))
      ],
      Outputs = [
            (L (Str ''detailed_pdf_of_friendID''))
      ],
      Updates = []
\<rparr>"

definition "pdf1" :: "transition" where
"pdf1 \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''otherID'')),
            GExp.Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')),
            GExp.Eq (V (I 3)) (L (Str ''MNn5''))
      ],
      Outputs = [
            (L (Str ''summary_pdf_of_otherID''))
      ],
      Updates = []
\<rparr>"

definition "pdf2" :: "transition" where
"pdf2 \<equiv> \<lparr>
      Label = STR ''pdf'',
      Arity = 3,
      Guard = [
            GExp.Eq (V (I 1)) (L (Str ''otherID'')),
            GExp.Eq (V (I 2)) (L (Str ''name'')),
            GExp.Eq (V (I 3)) (L (Str ''4zoF''))
      ],
      Outputs = [
            (L (Str ''detailed_pdf_of_otherID''))
      ],
      Updates = []
\<rparr>"

definition "linkedIn" :: "transition_matrix" where
"linkedIn \<equiv> {|
      ((0, 1), login),
      ((0, 1), login1),
      ((1, 2), view),
      ((1, 4), view1),
      ((1, 6), view2),
      ((1, 6), view3),
      ((2, 3), pdf),
      ((4, 5), pdf1),
      ((6, 7), pdf2)
|}"

lemma implode_login: "String.implode ''login'' = STR ''login''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_pdf: "String.implode ''pdf'' = STR ''pdf''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma log_in: "length b = 1 \<Longrightarrow> possible_steps linkedIn 0 r STR ''login'' [Str ''free''] = {|(1, login)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
           apply (simp_all add: login_def apply_guards_def)
  sorry

lemma apply_updates_login: "apply_updates (Updates login) (join_ir [EFSM.Str ''free''] Map.empty) Map.empty = <1 := Str ''free''>"
  apply (rule ext)
  by (simp add: login_def apply_updates_def join_ir_def input2state_def)

lemma input_get_length: "b ! 0 = Str ''free'' \<Longrightarrow>
       length b = 1 \<Longrightarrow>
       hd b = Str ''free''"
proof(induction b)
  case Nil
  then show ?case by simp
next
  case (Cons a b)
  then show ?case
    by simp
qed

lemma not_view: "a \<noteq> STR ''view'' \<Longrightarrow> possible_steps linkedIn 1 <1 := EFSM.Str ''free''> a b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
  by (simp_all add: view_def view1_def view2_def view3_def)

lemma test: "snd (shd i) ! 0 = EFSM.Str ''otherID'' \<longrightarrow>
           fst (shd i) = STR ''pdf'' \<longrightarrow>
           \<not> OutputEq [Some (EFSM.Str ''detailed_pdf_of_otherID'')]
               (make_full_observation linkedIn (fst (ltl_step linkedIn (Some 1) <1 := EFSM.Str ''free''> (shd i)))
                 (snd (snd (ltl_step linkedIn (Some 1) <1 := EFSM.Str ''free''> (shd i)))) (stl i))"
  apply standard
  apply (case_tac "shd i")
  apply simp
  by (simp add: not_view OutputEq_def)

lemma not_login: "length b \<noteq> 1 \<Longrightarrow>
        possible_steps linkedIn 0 Map.empty STR ''login'' b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
  by (simp_all add: login_def)

lemma not_login_free: "b ! 0 = EFSM.Str ''free'' \<Longrightarrow>
       b \<noteq> [EFSM.Str ''free''] \<Longrightarrow>
       possible_steps linkedIn 0 Map.empty STR ''login'' b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
         apply (simp_all add: login_def)
  by (metis One_nat_def length_0_conv length_Suc_conv nth_Cons_0)

lemma state_1_pdf: "possible_steps linkedIn 1 <1 := EFSM.Str ''free''> STR ''pdf'' ba = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
  by (simp_all add: view_def view1_def view2_def view3_def)

lemma implode_friendID: "String.implode ''friendID'' = STR ''friendID''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_otherID: "String.implode ''otherID'' = STR ''otherID''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma viewFriend: "possible_steps linkedIn 1 <1 := EFSM.Str ''free''> STR ''view''
                                           [EFSM.Str ''friendID'', EFSM.Str ''name'', EFSM.Str ''HM8p''] = {|(2, view)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
  by (simp_all add: view1_def gval.simps ValueEq_def implode_friendID implode_otherID
                     view2_def view3_def view_def Str_def I_def apply_guards_def input2state_def)

lemma apply_updates_view: "apply_updates (Updates view) i r = r"
  apply (rule ext)
  by (simp add: view_def)

lemma pdfFriend: "possible_steps linkedIn 2 <1 := EFSM.Str ''free''> STR ''pdf'' [EFSM.Str ''friendID'', EFSM.Str ''name'', EFSM.Str ''HM8p''] = {|(3, pdf)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
  by (simp_all add: pdf_def gval.simps ValueEq_def I_def input2state_def apply_guards_def)

lemma apply_updates_pdf: "apply_updates (Updates pdf) i r = r"
  apply (rule ext)
  by (simp add: pdf_def)

lemma pdfOther_s2: "possible_steps linkedIn 2 <1 := EFSM.Str ''free''> STR ''pdf''
                                    [EFSM.Str ''otherID'', EFSM.Str ''name'', EFSM.Str ''HM8p''] = {||}"
  by (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def
                linkedIn_def pdf_def gval.simps ValueEq_def implode_friendID implode_otherID Str_def
                I_def apply_guards_def join_ir_def input2state_def)

lemma possible_steps_s3: "possible_steps linkedIn 3 r l i = {||}"
  by (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)

lemma none_never_detailed: "alw (\<lambda>xs. inputs (shd xs) ! 0 = EFSM.Str ''otherID'' \<longrightarrow>
                     label (shd xs) = STR ''pdf'' \<longrightarrow> output (shd (stl xs)) \<noteq> [Some (EFSM.Str ''detailed_pdf_of_otherID'')])
            (make_full_observation linkedIn None r i)"
proof -
  obtain ss :: "((String.literal \<times> value list) stream \<Rightarrow> state stream) \<Rightarrow> (String.literal \<times> value list) stream" where
    "\<forall>f p s. f (stl (ss f)) \<noteq> stl (f (ss f)) \<or> alw p (f s) = alw (\<lambda>s. p (f s)) s"
    by (metis (no_types) alw_inv)
  then show ?thesis
    by (simp add: all_imp_alw OutputEq_def)
qed

lemma aux1_aux1_aux1: "alw (\<lambda>xs. inputs (shd xs) ! 0 = EFSM.Str ''otherID'' \<longrightarrow>
                     label (shd xs) = STR ''pdf'' \<longrightarrow> output (shd (stl xs)) \<noteq> [Some (EFSM.Str ''detailed_pdf_of_otherID'')])
            (make_full_observation linkedIn (Some 3) <1 := EFSM.Str ''free''> i)"
proof(coinduction)
  case alw
  then show ?case
    apply (case_tac "shd i")
    by (simp add: possible_steps_s3 none_never_detailed)
qed

lemma implode_name: "String.implode ''name'' = STR ''name''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_HM8p: "String.implode ''HM8p'' = STR ''HM8p''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma not_pdfFriend: "ba \<noteq> [EFSM.Str ''friendID'', EFSM.Str ''name'', EFSM.Str ''HM8p''] \<Longrightarrow>
possible_steps linkedIn 2 <1 := EFSM.Str ''free''> STR ''pdf'' ba = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def 
         linkedIn_def pdf_def gval.simps ValueEq_def Str_def implode_friendID implode_otherID implode_name implode_HM8p)
  apply (case_tac ba)
   apply simp
  apply (case_tac list)
   apply simp
  apply (case_tac lista)
   apply simp
  apply clarify
  apply (simp add: apply_guards_def gval.simps join_ir_def ValueEq_def input2state_def)
  by auto

lemma not_pdfFriend_2: "aa \<noteq> STR ''pdf'' \<Longrightarrow> possible_steps linkedIn 2 <1 := EFSM.Str ''free''> aa ba = {||}"
  by (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def pdf_def)

lemma implode_MNn5: "String.implode ''MNn5'' = STR ''MNn5''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_4z0f: "String.implode ''4z0F'' = STR ''4z0F''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_OON: "String.implode ''OUT_OF_NETWORK'' = STR ''OUT_OF_NETWORK''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma view_other_OON: "possible_steps linkedIn 1 <1 := EFSM.Str ''free''> STR ''view''
                                           [EFSM.Str ''otherID'', EFSM.Str ''OUT_OF_NETWORK'', EFSM.Str ''MNn5''] = {|(4, view1)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
  by (simp_all add: view_def gval.simps ValueEq_def implode_otherID implode_friendID implode_MNn5 
                    implode_HM8p implode_name implode_OON Str_def view2_def view3_def view1_def
                    apply_guards_def input2state_def)

lemma apply_update_view1: "apply_updates (Updates view1) i r = r"
  apply (rule ext)
  by (simp add: view1_def)

lemma implode_free: "String.implode ''free'' = STR ''free''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_paid: "String.implode ''paid'' = STR ''paid''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma pdf_other_OON: "possible_steps linkedIn 4 <1 := EFSM.Str ''free''> STR ''pdf''
                                   [EFSM.Str ''otherID'', EFSM.Str ''OUT_OF_NETWORK'', EFSM.Str ''MNn5''] = {|(5, pdf1)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
  by (simp_all add: pdf_def pdf1_def gval.simps ValueEq_def implode_otherID implode_friendID
                    implode_MNn5 implode_HM8p implode_name implode_OON Str_def apply_guards_def input2state_def)

lemma apply_updates_pdf1: "apply_updates (Updates pdf1) i r = r"
  apply (rule ext)
  by (simp add: pdf1_def)

lemma possible_steps_5: "possible_steps linkedIn 5 r l i = {||}"
  by (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)

lemma aux1_aux1_aux2: "alw (\<lambda>xs. inputs (shd xs) ! 0 = EFSM.Str ''otherID'' \<longrightarrow>
                      label (shd xs) = STR ''pdf'' \<longrightarrow> output (shd (stl xs)) \<noteq> [Some (EFSM.Str ''detailed_pdf_of_otherID'')])
             (make_full_observation linkedIn (Some 5) <1 := EFSM.Str ''free''> i)"
proof(coinduction)
  case alw
  then show ?case
    apply (case_tac "shd i")
    apply simp
    apply (simp add: possible_steps_5)
    using none_never_detailed by blast
qed

lemma not_pdf_other: "ba \<noteq> [EFSM.Str ''otherID'', EFSM.Str ''OUT_OF_NETWORK'', EFSM.Str ''MNn5''] \<Longrightarrow>
        possible_steps linkedIn 4 <1 := EFSM.Str ''free''> STR ''pdf'' ba = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def 
         linkedIn_def pdf1_def gval.simps ValueEq_def Str_def implode_friendID implode_otherID implode_name implode_HM8p)
  apply (case_tac ba)
   apply simp
  apply (case_tac list)
   apply simp
  apply (case_tac lista)
   apply simp
  apply clarify
  apply (simp add: apply_guards_def gval.simps ValueEq_def join_ir_def input2state_def)
  by auto

lemma not_pdfOther_2: "aa \<noteq> STR ''pdf'' \<Longrightarrow> possible_steps linkedIn 4 <1 := EFSM.Str ''free''> aa ba = {||}"
  by (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def pdf1_def)

lemma viewOther_fuzz: "possible_steps linkedIn 1 <1 := EFSM.Str ''free''> STR ''view''
                                           [EFSM.Str ''otherID'', EFSM.Str ''name'', EFSM.Str ''4zoF''] = {|(4, view2)|}"
 apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
  by (simp_all add: view_def gval.simps ValueEq_def implode_free implode_paid implode_otherID
                    implode_friendID implode_MNn5 implode_HM8p implode_name implode_OON Str_def
                    view2_def view3_def view1_def apply_guards_def input2state_def)

lemma apply_updates_view2: "apply_updates (Updates view2) i r = r"
  apply (rule ext)
  by (simp add: view2_def)

lemma invalid: "b \<noteq> [EFSM.Str ''friendID'', EFSM.Str ''name'', EFSM.Str ''HM8p''] \<Longrightarrow>
        b \<noteq> [EFSM.Str ''otherID'', EFSM.Str ''OUT_OF_NETWORK'', EFSM.Str ''MNn5''] \<Longrightarrow>
        b \<noteq> [EFSM.Str ''otherID'', EFSM.Str ''name'', EFSM.Str ''4zoF''] \<Longrightarrow>
        possible_steps linkedIn 1 <1 := EFSM.Str ''free''> STR ''view'' b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def linkedIn_def)
  apply safe
     apply (simp_all add: view_def gval.simps ValueEq_def view1_def view2_def view3_def Str_def input2state_def apply_guards_def join_ir_def implode_free implode_paid implode_friendID implode_otherID implode_name implode_OON implode_MNn5 implode_HM8p implode_4z0f)
  apply (case_tac b)
   apply simp
  apply (case_tac list)
   apply simp
  apply (case_tac lista)
   apply simp
  apply clarify
     apply (simp add: )
     apply auto[1]
  apply (case_tac b)
   apply simp
  apply (case_tac list)
   apply simp
  apply (case_tac lista)
   apply simp
  apply clarify
   apply (simp add: input2state_def)
    apply auto[1]
  apply (case_tac b)
   apply simp
  apply (case_tac list)
   apply simp
  apply (case_tac lista)
   apply simp
  apply clarify
   apply (simp add: input2state_def)
  using trilean.distinct(1) by presburger

lemma aux1_aux1: "alw (\<lambda>xs. inputs (shd xs) ! 0 = EFSM.Str ''otherID'' \<longrightarrow>
                     label (shd xs) = STR ''pdf'' \<longrightarrow> output (shd (stl xs)) \<noteq> [Some (EFSM.Str ''detailed_pdf_of_otherID'')])
            (make_full_observation linkedIn (fst (ltl_step linkedIn (Some 1) <1 := EFSM.Str ''free''> (shd i)))
              (snd (snd (ltl_step linkedIn (Some 1) <1 := EFSM.Str ''free''> (shd i)))) (stl i))"
proof(coinduction)
  have OON_neq_name: "EFSM.Str ''OUT_OF_NETWORK'' \<noteq> EFSM.Str ''name''"
    by (simp add: Str_def implode_OON implode_name)
  case alw
  then show ?case
    apply simp
    apply (case_tac "shd i")
    apply simp
    apply (case_tac "a = STR ''view''")
     apply simp
     
     apply (case_tac "b = [Str ''friendID'', Str ''name'', Str ''HM8p'']")
      apply (simp add: viewFriend apply_updates_view)
      apply (case_tac "shd (stl i) = (STR ''pdf'', [Str ''friendID'', Str ''name'', Str ''HM8p''])")
       apply simp
       apply (simp add: pdfFriend apply_updates_pdf implode_friendID implode_otherID pdfOther_s2 aux1_aux1_aux1)
      apply (case_tac "shd (stl i)")
      apply simp
      apply (case_tac "aa = STR ''pdf''")
       apply (simp add: not_pdfFriend)
    using none_never_detailed apply blast
      apply (simp add: not_pdfFriend_2)
    using none_never_detailed apply blast

     apply (case_tac "b = [Str ''otherID'', Str ''OUT_OF_NETWORK'', Str ''MNn5'']")
      apply (simp add: view_other_OON apply_update_view1 OON_neq_name)
      apply (case_tac "shd (stl i) = (STR ''pdf'', [Str ''otherID'', Str ''OUT_OF_NETWORK'', Str ''MNn5''])")
       apply (simp add: pdf_other_OON apply_updates_pdf1 aux1_aux1_aux2)
       apply (case_tac "shd (stl (stl i))")
       apply (simp add: possible_steps_5)

      apply (case_tac "shd (stl i)")
      apply simp
      apply (case_tac "aa = STR ''pdf''")
       apply (simp add: not_pdf_other)
    using none_never_detailed apply blast
      apply (simp add: not_pdfOther_2)
    using none_never_detailed apply blast

     apply (case_tac "b = [Str ''otherID'', Str ''name'', Str ''4zoF'']")
      apply (simp add: viewOther_fuzz apply_updates_view2 OON_neq_name)
      apply (case_tac "shd (stl i) = (STR ''pdf'', [Str ''otherID'', Str ''OUT_OF_NETWORK'', Str ''MNn5''])")
       apply (simp add: pdf_other_OON apply_updates_pdf1 aux1_aux1_aux2)
       apply (case_tac "shd (stl (stl i))")
       apply (simp add: possible_steps_5)

      apply (case_tac "shd (stl i)")
      apply simp
      apply (case_tac "aa = STR ''pdf''")
       apply (simp add: not_pdf_other)
    using none_never_detailed apply blast
      apply (simp add: not_pdfOther_2)
    using none_never_detailed apply blast

     apply (simp add: invalid)
    using none_never_detailed apply blast

    apply (simp add: not_view)
    using none_never_detailed by blast
qed

lemma nxt_no_output_none: "(nxt (OutputEq [])) (make_full_observation e None r i)"
  by (simp add: OutputEq_def)

lemma aux1: "fst (shd i) = STR ''login'' \<Longrightarrow>
    snd (shd i) ! 0 = EFSM.Str ''free'' \<Longrightarrow>
    alw (\<lambda>xs. inputs (shd xs) ! 0 = EFSM.Str ''otherID'' \<longrightarrow>
              label (shd xs) = STR ''pdf'' \<longrightarrow> \<not> OutputEq [Some (EFSM.Str ''detailed_pdf_of_otherID'')] (stl xs))
     (make_full_observation linkedIn (fst (ltl_step linkedIn (Some 0) Map.empty (shd i)))
       (snd (snd (ltl_step linkedIn (Some 0) Map.empty (shd i)))) (stl i))"
proof(coinduction)
  case alw
  then show ?case
    apply simp
     apply (case_tac "shd i")
    apply simp
    apply (case_tac "b = [Str ''free'']")
     apply (simp add: log_in apply_updates_login)
     apply (simp add: OutputEq_def)
     apply standard
      apply (case_tac "shd (stl i)")
      apply (simp add: state_1_pdf)
     apply (simp add: aux1_aux1)
    by (simp add: not_login_free OutputEq_def none_never_detailed)
qed

(* SAL thinks this is true so we should be able to prove it *)
lemma LTL_neverDetailed:
    "(((LabelEq ''login'' aand checkInx ip 1 ValueEq (Some (Str ''free''))) impl
     (nxt (alw ((LabelEq ''pdf'' aand
     checkInx ip 1 ValueEq (Some (Str ''otherID''))) impl 
     (nxt (not (OutputEq [Some (Str ''detailed_pdf_of_otherID'')]))))))))
     (watch linkedIn i)"
  apply standard
  apply simp
  apply (simp add: LabelEq_def implode_login)
  apply (simp add: ValueEq_def implode_pdf)
  apply (case_tac "Inputs 0 (watch linkedIn i) = EFSM.Str ''free''")
   defer
   apply simp
  by (simp add: Inputs_def watch_def aux1)
end


end
