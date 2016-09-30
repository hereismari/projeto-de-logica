module projeto
open util/ordering[Tempo]

// -------------------------------- Helpers -------------------------------------

abstract sig Bool {}
one sig True, False extends Bool {}

// ------------------------------- Signatures ---------------------------------

sig Tempo {}

sig Cliente {
	cartoes: set Jonas -> Cartao -> Tempo,
	vendas: set Venda -> Tempo
}

abstract sig Item {}
sig Roupa, Calcado extends Item {}

abstract sig Funcionario { brinde: Bool -> Tempo }

sig Vendedor, Caixa extends Funcionario {
	vendas: set Venda -> Tempo 
}

sig Promotor extends Funcionario {
	cartoes: set Cartao -> Tempo
}

abstract sig Pagamento {}
one sig Vista, Dividido, Prazo extends Pagamento {}

sig Cartao {}

sig Venda {
	pagamento: Pagamento -> Tempo,
	itens: Item -> Tempo
}

// TEMPORAAAAAARIO ==>> TIRAR MESMO!
abstract sig Jonas {}

one sig Dependente, Titular extends Jonas {}
// -------------------------------- Facts -------------------------------

fact {
	no Cliente.cartoes.first
	no Cliente.vendas.first
	no Vendedor.vendas.first
	no Caixa.vendas.first
	no Promotor.cartoes.first
	no Venda.itens.first
	no Venda.pagamento.first
	Funcionario.brinde.first = False
}

fact {
	all f:Funcionario, t:Tempo | one f.brinde.t
	all f:Funcionario, t:Tempo-last | f.brinde.t = True implies next[t][f.brinde] = True
}

// Esse fato garante que todo cartão tem exatamente um titular
// Cada cartão só pode ter um promotor ao longo do tempo
// Nao pode ser dependente e titular ao mesmo tempo
// Em um certo tempo um cartão não pode ter promotor e não ter clientes, e vice versa
fact {
	all c:Cartao | lone cartoes.Tempo.c.Titular
	all c:Cartao | lone (Promotor<:cartoes).Tempo.c
	all cl:Cliente | no cl.cartoes[Titular] & cl.cartoes[Dependente]
	all c:Cartao, t:Tempo | some cartoes.t.c.Dependente implies some cartoes.t.c.Titular
	all c:Cartao, t:Tempo | some cartoes.t.c.Jonas implies some (Promotor<:cartoes).t.c
	all c:Cartao, t:Tempo-last | some t[Promotor<:cartoes].c implies some next[t][Promotor<:cartoes].c
	all c:Cartao, t0:Tempo | no prev[t0][Promotor<:cartoes].c and some t0[Promotor<:cartoes].c implies some t0[Cliente<:cartoes].c.Titular
}

// Cada item só pode ser vendido uma vez
fact {
	all i:Item | one (Venda<:itens).Tempo.i
}

fact {
	all v:Venda | lone (Cliente<:vendas).Tempo.v
	all v:Venda | lone (Caixa<:vendas).Tempo.v
	all v:Venda | lone (Vendedor<:vendas).Tempo.v

	all v:Venda | some v.itens.Tempo
	all v:Venda, t:Tempo | no v.itens.t or v.itens.t = v.itens.Tempo
	all v:Venda, t:Tempo-last | some t[Vendedor<:vendas].v implies some next[t][Vendedor<:vendas].v

	all v:Venda, t:Tempo |
		some (Cliente<:vendas).t.v and some (Caixa<:vendas).t.v and some (Vendedor<:vendas).t.v and some v.itens.t  or
		no (Cliente<:vendas).t.v and no (Caixa<:vendas).t.v and no (Vendedor<:vendas).t.v and no v.itens.t 
}

// Sabe-se que a loja tem 3 a 4 operadores de caixa, 2 promotores de cartão e 3 a 5 vendedores.
//fact {
	//#Vendedor >= 3 and #Vendedor <= 5
	//#Promotor = 2
	//#Caixa >= 3 and	 #Caixa <= 4
//}

// Restrições em cima de quem ganha brinde
fact {
	all v:Vendedor, t:Tempo | v.brinde.t = True implies some c:v.vendas.t | some c.itens.t & Roupa and some c.itens.t & Calcado 
	all p:Promotor, t:Tempo | p.brinde.t = True implies #p.cartoes.t >= 2 and some c:p.cartoes.t, t0:Tempo | some t0[cartoes].c.Dependente and no prev[t0][cartoes].c.Titular
	all c:Caixa, t:Tempo | c.brinde.t = True implies Dividido + Prazo in c.vendas.t.pagamento
	some c:Caixa, t:Tempo | c.brinde.t = True
}

// --------------------------------- Run -------------------------------

pred show [] {}
run show for 4 //but 11 Funcionario
