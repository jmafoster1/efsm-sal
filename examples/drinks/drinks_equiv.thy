theory drinks_equiv
imports XXDOTXXDrinks_Machine Drinks_Machine_LTL drinks_machine_ltl
begin

lemma "XXDOTXXDrinks_Machine.drinks_machine = Drinks_Machine.drinks"
  apply (simp add: XXDOTXXDrinks_Machine.drinks_machine_def Drinks_Machine.drinks_def XXDOTXXDrinks_Machine.transitions Drinks_Machine.transitions)
  by auto

lemma "drinks_machine_ltl.drinks = Drinks_Machine.drinks"
  apply (simp add: drinks_machine_ltl.drinks_def Drinks_Machine.drinks_def drinks_machine_ltl.transitions Drinks_Machine.transitions)
  by auto
end
