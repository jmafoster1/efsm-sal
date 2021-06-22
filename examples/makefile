clean:
	find . -name '*.sal' -o  -name '*.dot' -o  -name '*.png' -o  -name '*.thy~' -o  -name '*Theorems.thy' -o  -name 'Error_*.thy' -o  -name 'XXX*.thy'| xargs rm

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

testsaltheorems:
	cd coin-tea;\
	bash test_coin_tea_theorems.sh;\
	cd ../drinks;\
	bash test_drinks_machine_theorems.sh;\
	cd ../lift-controller;\
	sed -i 's/r__4 = None/r__4 = Some(Num(1))/' lift_controller_ltltheorems.sal;\
	bash test_lift_controller_theorems.sh;\
	cd ../linkedin;\
	bash test_linked_in_theorems.sh

dot:
	find . -name '*.dot' | xargs -n 1 dot -Tpng -O
