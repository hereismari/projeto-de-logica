module projeto

// -------------------------------- Helpers -------------------------------------

abstract sig Bool {}
one sig True, False extends Bool {}

// ------------------------------- Signatures ---------------------------------

one sig Dono {}
sig Id {}
sig Cliente {id: one Id }

abstract sig Brinde {}
sig Bone, Adesivo, Chaveiros extends Brinde {}

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

/*
fact {
	3 <= #Vendedor and #Vendedor <= 5
	3 <= #Caixa and #Caixa <= 4
	#Promotor = 2
}
*/
/*
fact {
	all v:Vendedor | v.brinde = True <=> some c:vendedor.v | c in Roupa.compra and c in Calcado.compra
	all p:Promotor | p.brinde = True <=> #promotor.p >= 2 and True in promotor.p.dependente
}*/

// --------------------------------- Run -------------------------------

pred show [] {}
run show for 3
