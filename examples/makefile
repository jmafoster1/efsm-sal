clean:
	find . -name '*.sal' -o  -name '*.dot' -o  -name '*.png' -o  -name '*.thy~' -o  -name '*Theorems.thy' -o  -name 'Error_*.thy' | xargs rm

testwf:
	find . -name '*.sal' | xargs -n 1 sal-wfc

testsal:
	cd coin-tea;\
	bash test_coin_tea.sh;\
	cd ../drinks;\
	bash test_drinks_machine.sh;\
	cd ../lift-controller;\
	sed -i 's/r__4 = None/r__4 = Some(Num(1))/' lift_controller.sal;\
	sed -i 's/r__4 = None/r__4 = Some(Num(1))/' lift_controller_ltl.sal;\
	bash test_lift_controller.sh;\
	cd ../linkedin;\
	bash test_linked_in.sh

dot:
	find . -name '*.dot' | xargs -n 1 dot -Tpng -O
