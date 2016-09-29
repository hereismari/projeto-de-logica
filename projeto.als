module projeto

// -------------------------------- Helpers -------------------------------------

abstract sig Bool {}
one sig True, False extends Bool {}

// ------------------------------- Signatures ---------------------------------

one sig Dono {}
sig Id {}
sig Cliente {id: one Id }

abstract sig Brinde {}
one sig Bone, Adesivo, Chaveiros extends Brinde {}

abstract sig Item { compra : Compra }
sig Roupa, Calcado extends Item {}

abstract sig Funcionario { brinde : Brinde }
sig Vendedor, Caixa, Promotor extends Funcionario {}

sig Cartao {
	cliente : Cliente,
	dependente : Bool,
	promotor : Promotor
}

sig Compra {
	cliente : Cliente,
	vendedor : Vendedor,
	caixa : Caixa
}

// -------------------------------- Facts -------------------------------

// toda compra tem algum item associado
fact {
	all c:Compra | some compra.c
}

// todo cliente tem um unico id
fact {
	all c1: Cliente, c2: Cliente | c1 != c2 implies c1.id != c2.id
}

// Sabe-se que a loja tem 3 a 4 operadores de caixa, 2 promotores de cartão e 3 a 5 vendedores.
// se escopo < 8 nao eh achada uma instancia valida (investigar isso!!!), se esse fato for retirado deve dar certo
fact {
	#Vendedor >= 3 and #Vendedor <= 5
	#Promotor = 2
	#Caixa >= 3 and	 #Caixa <= 4
}

/*
fact {
	all v:Vendedor | v.brinde = True <=> some c:vendedor.v | c in Roupa.compra and c in Calcado.compra
	all p:Promotor | p.brinde = True <=> #promotor.p >= 2 and True in promotor.p.dependente
}*/

// --------------------------------- Run -------------------------------

pred show [] {}
run show for 8
