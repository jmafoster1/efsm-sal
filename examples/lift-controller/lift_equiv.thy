theory lift_equiv
imports XXDOTXXLift_Controller Lift_Controller_LTL lift_controller_ltl
begin

lemma "XXDOTXXLift_Controller.lift_controller = Lift_Controller.lift"
  apply (simp add: XXDOTXXLift_Controller.lift_controller_def Lift_Controller.lift_def XXDOTXXLift_Controller.transitions Lift_Controller.transitions)
  by auto

lemma "lift_controller_ltl.lift = Lift_Controller.lift"
  by (simp add: lift_controller_ltl.lift_def Lift_Controller.lift_def lift_controller_ltl.transitions Lift_Controller.transitions)
end
