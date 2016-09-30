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

abstract sig Funcionario { brinde: set Bool -> Tempo }

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
	pagamento: set Pagamento -> Tempo,
	itens: set Item -> Tempo
}

// TEMPORAAAAAARIO ==>> TIRAR MESMO!
abstract sig Jonas {}

one sig Dependente, Titular extends Jonas {}
// -------------------------------- Facts -------------------------------

fact {
	all f:Funcionario, t:Tempo | one f.brinde.t
	all f:Funcionario, t:Tempo-last | f.brinde.t = True implies next[t][f.brinde] = True
}

// Esse fato garante que todo cartão tem exatamente um titular
// Cada cartão só pode ter um promotor ao longo do tempo
// Nao pode ser dependente e titular ao mesmo tempo
// Em um certo tempo um cartão não pode ter promotor e não ter clientes, e vice versa
fact {
	all c:Cartao | one cartoes.Tempo.c.Titular
	all c:Cartao | one (Promotor<:cartoes).Tempo.c
	all c:Cliente | no c.cartoes[Titular] & c.cartoes[Dependente]
	all c:Cartao, t:Tempo | some cartoes.t.c.Dependente implies some cartoes.t.c.Titular
	all c:Cartao, t:Tempo | some t[Cliente<:cartoes].c implies some t[Promotor<:cartoes].c
	all c:Cartao, t:Tempo-last | some t[Promotor<:cartoes].c implies some next[t][Promotor<:cartoes].c
	all c:Cartao, t:Tempo | no prev[t][Promotor<:cartoes].c and some t[Promotor<:cartoes].c implies some t[Cliente<:cartoes].c.Titular
	all c:Cartao, t:Tempo-last | some t[Cliente<:cartoes].c.Titular and no next[t][Cliente<:cartoes].c.Titular implies no ^next[t][Cliente<:cartoes].c.Titular
}

// Cada item só pode ser vendido uma vez
fact {
	all i:Item | one Tempo[Venda<:itens].i
}

fact {
	all v:Venda | one Tempo[Cliente<:vendas].v
	all v:Venda | one Tempo[Caixa<:vendas].v
	all v:Venda | one Tempo[Vendedor<:vendas].v
	all v:Venda | one v.pagamento.Tempo

	all v:Venda, t:Tempo-last | some t[v.pagamento] implies some next[t][v.pagamento]
	all v:Venda, t:Tempo | no v.itens.t or v.itens.t = v.itens.Tempo

	all v:Venda, t:Tempo |
		some (Cliente<:vendas).t.v and some (Caixa<:vendas).t.v and some (Vendedor<:vendas).t.v and some v.itens.t and some v.pagamento.t  or
		no (Cliente<:vendas).t.v and no (Caixa<:vendas).t.v and no (Vendedor<:vendas).t.v and no v.itens.t  and no v.pagamento.t
}

// Sabe-se que a loja tem 3 a 4 operadores de caixa, 2 promotores de cartão e 3 a 5 vendedores.
fact {
	#Vendedor >= 3 and #Vendedor <= 5
	#Promotor = 2
	#Caixa >= 3 and	 #Caixa <= 4
}

// Restrições em cima de quem ganha brinde
fact {
	all v:Vendedor, t:Tempo | v.brinde.t = True implies some ve:v.vendas.t | some ve.itens.t & Roupa and some ve.itens.t & Calcado 
	all p:Promotor, t:Tempo | p.brinde.t = True implies #p.cartoes.t >= 2 and some c:p.cartoes.t, tc:Tempo | some tc[cartoes].c.Dependente and no prev[tc][cartoes].c.Titular
	all c:Caixa, t:Tempo | c.brinde.t = True implies Dividido + Prazo in c.vendas.t.pagamento.t
}



//----------------------------- Predicados ---------------------------

pred init[t:Tempo] {
	no Cliente.cartoes.t
	no Cliente.vendas.t
	no Vendedor.vendas.t
	no Caixa.vendas.t
	no Promotor.cartoes.t
	no Venda.itens.t
	Funcionario.brinde.t = False
}

pred realizarVenda[cl:Cliente, ca:Caixa, v:Vendedor, i:Item, p:Pagamento, t1, t2:Tempo] {
	some ve:Venda |
		t1[ve.itens] = none and t2[ve.itens] = i and
		t1[ve.pagamento] = none and t2[ve.pagamento] = p and
		ve not in t1[cl.vendas] and ve in t2[cl.vendas] and
		ve not in t1[ca.vendas] and ve in t2[ca.vendas] and
		ve not in t1[v.vendas] and ve in t2[v.vendas] and
}

pred fazerCartao[c:Cliente, d:Cliente, p:Promotor, t1, t2:Tempo] {}

pred registrarDependente[c:Cartao, d:Cliente, t1, t2:Tempo] {
	d not in t1[Cliente<:cartoes].c.Jonas and d in t1[Cliente<:cartoes].c.Dependente
}

pred darBrinde[f:Funcionario, t1, t2:Tempo] {
	f.brinde.t1 = False and f.brinde.t2 = True
}

pred removerCartao[c:Cartao, t1, t2:Tempo] {
	some t1[Cliente<:cartoes].c.Titular and no t2[Cliente<:cartoes].c
}

fact traces {
	init[first]
	all t1: Tempo - last | let t2 = t1.next |
		(some cl:Cliente, ca:Caixa, v:Vendedor, p:Pagamento, i:Item | realizarVenda[cl, ca, v, i, p, t1, t2]) or
		(some c:Cliente, d:Cliente, p:Promotor | fazerCartao[c, d, p, t1, t2]) or
		(some c:Cartao, d:Cliente, t1, t2:Tempo | registrarDependente[c, d, t1, t2]) or
		(some f:Funcionario | darBrinde[f, t1, t2]) or
		(some c:Cartao | removerCartao[c, t1, t2])
}

// --------------------------------- Run -------------------------------

pred show [] {}
run show for 4 but 11 Funcionario
