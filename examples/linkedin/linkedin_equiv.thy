theory linkedin_equiv
imports XXDOTXXLinked_In Linked_In linked_in
begin

lemma "XXDOTXXLinked_In.linked_in = Linked_In.linkedIn"
  apply (simp add: XXDOTXXLinked_In.linked_in_def Linked_In.linkedIn_def XXDOTXXLinked_In.transitions)
  by (simp add: Linked_In.login1_def Linked_In.login_def Linked_In.pdf1_def Linked_In.pdf2_def Linked_In.pdf_def Linked_In.view1_def Linked_In.view2_def Linked_In.view3_def Linked_In.view_def)

lemma "linked_in.linkedIn = Linked_In.linkedIn"
  apply (simp add: linked_in.linkedIn_def Linked_In.linkedIn_def linked_in.transitions)
  by (simp add: Linked_In.login1_def Linked_In.login_def Linked_In.pdf1_def Linked_In.pdf2_def Linked_In.pdf_def Linked_In.view1_def Linked_In.view2_def Linked_In.view3_def Linked_In.view_def)
end
