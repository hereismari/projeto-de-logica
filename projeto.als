module projeto
open util/ordering[Tempo]

// -------------------------------- Helpers -------------------------------------

abstract sig Bool {}
one sig True, False extends Bool {}

// ------------------------------- Signatures ---------------------------------

sig Tempo {}

sig Cliente {
	cartoes: set Jonas -> Cartao -> Tempo,
	compras: set Compra -> Tempo
}

abstract sig Item { compra: Compra }
sig Roupa, Calcado extends Item {}

abstract sig Funcionario { brinde: Bool}
sig Vendedor, Caixa extends Funcionario {}
sig Promotor extends Funcionario {
	cartoes: set Cartao -> Tempo
}

abstract sig Pagamento {}
one sig Vista, Dividido, Prazo extends Pagamento {}

sig Cartao {}

sig Compra {
	vendedor: Vendedor,
	pagamento: Pagamento,
	caixa: Caixa
}

// TEMPORAAAAAARIO ==>> TIRAR MESMO!
abstract sig Jonas {}

one sig Dependente, Titular extends Jonas {}
// -------------------------------- Facts -------------------------------

// Toda compra tem algum item associado
fact {
	all c:Compra | some compra.c
}

// Esse fato garante que todo cartão tem exatamente um titular
// Nao pode ser dependente e titular ao mesmo tempo
fact {
	all c:Cartao | one cartoes.Tempo.c.Titular
	all cl:Cliente | no cl.cartoes[Titular] & cl.cartoes[Dependente]
}

fact {
	all c:Cartao | one (cartoes).Tempo.c
}

// Sabe-se que a loja tem 3 a 4 operadores de caixa, 2 promotores de cartão e 3 a 5 vendedores.
//fact {
	//#Vendedor >= 3 and #Vendedor <= 5
	//#Promotor = 2
	//#Caixa >= 3 and	 #Caixa <= 4
//}

// Restrições em cima de quem ganha brinde
/*fact {
	all v:Vendedor | v.brinde = True <=> some c:vendedor.v | c in Roupa.compra and c in Calcado.compra
	all p:Promotor | p.brinde = True <=> #promotor.p >= 2 and True in promotor.p.dependente
	all c:Caixa | c.brinde = True <=> Dividido + Prazo in caixa.c.pagamento
}*/

// --------------------------------- Run -------------------------------

pred show [] {}
run show for 4 //but 11 Funcionario
