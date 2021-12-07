theory Coin_Tea_Equiv
imports XXDOTXXCoin_Tea Coin_Tea XXSALXXCoin_Tea
begin

lemma "XXDOTXXCoin_Tea.coin_tea = Coin_Tea.drinks"
  by (simp add: XXDOTXXCoin_Tea.coin_tea_def Coin_Tea.drinks_def XXDOTXXCoin_Tea.transitions Coin_Tea.transitions)

lemma "XXSALXXCoin_Tea.drinks = Coin_Tea.drinks"
  by (simp add: XXSALXXCoin_Tea.drinks_def Coin_Tea.drinks_def XXSALXXCoin_Tea.transitions Coin_Tea.transitions)

end
