theory drinks_equiv
imports XXDOTXXCoin_Tea Coin_Tea coin_tea
begin

lemma "XXDOTXXCoin_Tea.coin_tea = Coin_Tea.drinks"
  by (simp add: XXDOTXXCoin_Tea.coin_tea_def Coin_Tea.drinks_def XXDOTXXCoin_Tea.transitions Coin_Tea.transitions)

lemma "coin_tea.drinks = Coin_Tea.drinks"
  by (simp add: coin_tea.drinks_def Coin_Tea.drinks_def coin_tea.transitions Coin_Tea.transitions)

end
