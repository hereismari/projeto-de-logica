module brindes

one sig dono {}

sig registro {
	id: one id
}
some sig funcionario {
	registros: set registro
}
some sig vendedor extends funcionario {}
sig operador extends funcionario {}
some sig promotor extends funcionario {}

sig brinde {}

sig Item {}
sig id {}
sig cliente {
		id: one id,
		itens: set Item
}

pred show[]{}
run show for 2
