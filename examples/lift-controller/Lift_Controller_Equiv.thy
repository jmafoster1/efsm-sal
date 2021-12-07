theory Lift_Controller_Equiv
imports XXDOTXXLift_Controller Lift_Controller_LTL XXSALXXLift_Controller_LTL
begin

lemma "XXDOTXXLift_Controller.lift_controller = Lift_Controller.lift"
  apply (simp add: XXDOTXXLift_Controller.lift_controller_def Lift_Controller.lift_def XXDOTXXLift_Controller.transitions Lift_Controller.transitions)
  by auto

lemma "XXSALXXLift_Controller_LTL.lift = Lift_Controller.lift"
  apply (simp add: XXSALXXLift_Controller_LTL.lift_def Lift_Controller.lift_def XXSALXXLift_Controller_LTL.transitions Lift_Controller.transitions)
  by auto
end
