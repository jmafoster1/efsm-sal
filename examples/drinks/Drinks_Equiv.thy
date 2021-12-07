theory Drinks_Equiv
imports XXDOTXXDrinks_Machine Drinks_Machine_LTL XXSALXXDrinks_Machine_LTL
begin

lemma "XXDOTXXDrinks_Machine.drinks_machine = Drinks_Machine.drinks"
  apply (simp add: XXDOTXXDrinks_Machine.drinks_machine_def Drinks_Machine.drinks_def XXDOTXXDrinks_Machine.transitions Drinks_Machine.transitions)
  by auto

lemma "XXSALXXDrinks_Machine_LTL.drinks = Drinks_Machine.drinks"
  apply (simp add: XXSALXXDrinks_Machine_LTL.drinks_def Drinks_Machine.drinks_def XXSALXXDrinks_Machine_LTL.transitions Drinks_Machine.transitions)
  by auto
end
