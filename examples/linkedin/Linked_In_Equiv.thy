theory Linked_In_Equiv
imports XXDOTXXLinked_In Linked_In XXSALXXLinked_In
begin

lemma "XXDOTXXLinked_In.linked_in = Linked_In.linkedIn"
  apply (simp add: XXDOTXXLinked_In.linked_in_def Linked_In.linkedIn_def XXDOTXXLinked_In.transitions)
  by (simp add: Linked_In.login1_def Linked_In.login_def Linked_In.pdf1_def Linked_In.pdf2_def Linked_In.pdf_def Linked_In.view1_def Linked_In.view2_def Linked_In.view3_def Linked_In.view_def)

lemma "XXSALXXLinked_In.linkedIn = Linked_In.linkedIn"
  apply (simp add: Linked_In.linkedIn_def XXSALXXLinked_In.linkedIn_def XXSALXXLinked_In.transitions)
  by (simp add: Linked_In.login1_def Linked_In.login_def Linked_In.pdf1_def Linked_In.pdf2_def Linked_In.pdf_def Linked_In.view1_def Linked_In.view2_def Linked_In.view3_def Linked_In.view_def)
end
