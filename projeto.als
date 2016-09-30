module projeto
open util/ordering[Tempo]

// -------------------------------- Helpers -------------------------------------

abstract sig Bool {}
one sig True, False extends Bool {}

// ------------------------------- Signatures ---------------------------------

sig Tempo {}

sig Cliente {
	cartoes: set TipoCartao -> Cartao -> Tempo,
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

abstract sig TipoCartao {}
one sig Dependente, Titular extends TipoCartao {}

// -------------------------------- Facts -------------------------------

// Em um certo tempo, um funcionário não pode ter e não ter um brinde.
// Se um funcionário tem um brinde, ele não pode perdê-lo.
fact {
	all f:Funcionario, t:Tempo | one f.brinde.t
	all f:Funcionario, t:Tempo-last | f.brinde.t = True implies next[t][f.brinde] = True
}

// Todo cartão tem exatamente um titular ao longo de sua vida.
// Todo cartão tem exatamente um promotor ao longo de sua vida.
// Um cartão só pode ter dependentes se tiver um titular.
// Um cartão só pode ter clientes se tiver um promotor.
// A partir do momento que um cartão tem um promotor ele não pode perdê-lo.
// No momento em que o cartão passa a ter um promotor ele também deve ganhar um titular.
// Um cartão não pode deixar de ter titular e depois ganhar o titular de volta.
fact {
	all c:Cartao | one titulares[c, Tempo]
	all c:Cartao | one (Promotor<:cartoes).Tempo.c
	all c:Cartao, t:Tempo | some dependentes[c, t] implies some titulares[c, t]
	all c:Cartao, t:Tempo | some t[Cliente<:cartoes].c implies some t[Promotor<:cartoes].c
	all c:Cartao, t:Tempo-last | some t[Promotor<:cartoes].c implies some next[t][Promotor<:cartoes].c
	all c:Cartao, t:Tempo | no prev[t][Promotor<:cartoes].c and some t[Promotor<:cartoes].c implies some t[Cliente<:cartoes].c.Titular
	all c:Cartao, t:Tempo-last | some titulares[c, t] and no titulares[c, t.next] implies no titulares[c, t.^next]
}

// Nenhum cliente pode ser dependente e titular de um mesmo cartão ao mesmo tempo.
// Um cliente sem cartão da loja não pode fazer compras no cartão.
fact {
	all c:Cliente | no c.cartoes[Titular] & c.cartoes[Dependente]
	all c:Cliente, t:Tempo | no c.cartoes.t implies no c.vendas.t.pagamento.Tempo & (Prazo + Dividido)
}

// Cada item é vendido exatamente uma vez.
fact {
	all i:Item | one Tempo[Venda<:itens].i
}

// Cada venda tem exatamente um cliente.
// Cada venda tem exatamente um caixa.
// Cada venda tem exatamente um vendedor.
// Cada venda tem exatamente uma forma de pagamento
//
// A partir do momento em que uma venda foi paga, ela não pode ser "despaga".
// Para um venda em um certo momento, ou nenhum de seus produtos foi vendido, ou todos eles foram.
//
// Em qualquer momento, uma venda não pode estar parcialmente cadastrada.
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

// Há 3 a 4 operadores de caixa.
// Há 2 promotores de cartão.
// Há 3 a 5 vendedores.
/*fact {
	#Vendedor >= 3 and #Vendedor <= 5
	#Promotor = 2
	#Caixa >= 3 and	 #Caixa <= 4
}*/


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
		ve not in t1[v.vendas] and ve in t2[v.vendas]
}

pred fazerCartao[titular:Cliente, deps: Cliente, p:Promotor, t1, t2:Tempo] {
	some c:Cartao |
		titulares[c, t1] = none and titulares[c, t2] = titular and
		dependentes[c, t1] = none and dependentes[c, t2] = deps and
		t1[Promotor<:cartoes].c = none and t2[Promotor<:cartoes].c = p
}

pred registrarDependente[c:Cartao, d:Cliente, t1, t2:Tempo] {
	d not in t1[Cliente<:cartoes].c.TipoCartao and d in t2[Cliente<:cartoes].c.Dependente
}

pred darBrinde[f:Funcionario, t1, t2:Tempo] {
	t1[f.brinde] = False and t2[f.brinde] = True
}

pred removerCartao[c:Cartao, t1, t2:Tempo] {
	some t1[Cliente<:cartoes].c.Titular and no t2[Cliente<:cartoes].c
}

fact traces {
	init[first]

	// De um tempo pro próximo, pelo menos uma operação deve ser realizada
	all t1:Tempo-last | let t2 = t1.next |
		(some cl:Cliente, ca:Caixa, v:Vendedor, p:Pagamento, i:Item | realizarVenda[cl, ca, v, i, p, t1, t2]) or
		(some titular:Cliente, deps: Cliente, p:Promotor | fazerCartao[titular, deps, p, t1, t2]) or
		(some c:Cartao, d:Cliente, t1, t2:Tempo | registrarDependente[c, d, t1, t2]) or
		(some c:Cartao | removerCartao[c, t1, t2])

	// Os brindes são distribuidos sempre e apenas no último tempo
	let t1 = last.prev, t2 = last |
		(all v:Vendedor | some ve:v.vendas.t2 | some roupas[ve, t2] and some calcados[ve, t2] implies darBrinde[v, t1, t2]) and
		(all c:Caixa |  c.brinde.t2 = True implies Dividido + Prazo in c.vendas.t2.pagamento.Tempo implies darBrinde[c, t1, t2]) and
		(all p:Promotor | #p.cartoes.t2 >= 2 and some c:p.cartoes.t2, tc:Tempo | some dependentes[c, tc] and no titulares[c, tc.prev] implies darBrinde[p, t1, t2])
}

//------------------------------- Funções -----------------------------

fun dependentes[c:Cartao, t:Tempo] : set Cliente {
	t[cartoes].c.Dependente
}

fun titulares[c:Cartao, t:Tempo] : set Cliente {
	t[cartoes].c.Titular
}

fun calcados[v:Venda, t:Tempo] : set Calcado {
	v.itens.t & Calcado
}

fun roupas[v:Venda, t:Tempo] : set Roupa {
	v.itens.t & Roupa
}

//-------------------------------- Asserts -----------------------------

assert a1 {
	
}

// --------------------------------- Run -------------------------------

pred show [] {}
run show for 5//4 but 11 Funcionario

//check a1 for 5 but 8 Tempo
