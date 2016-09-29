module brindes

one sig Dono {}

sig Registro {
	id: one Id
}
some sig Funcionario {
	registros: set Registro
}
some sig Vendedor extends Funcionario {}
sig Operador extends Funcionario {}
some sig Promotor extends Funcionario {}

sig Brinde {}

sig Item {}
sig Id {}
sig Cliente {
		id: one Id,
		itens: set Item
}

pred show[]{}
run show for 2
