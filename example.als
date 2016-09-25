module banco
open util/ordering[Time]

sig Time {}

sig Banco{
	contas: Conta -> Time
}

fact {
	all b: Banco,t:Time-first | some (b.contas).t
}

abstract sig Conta {}

sig ContaCorrente extends Conta{}
sig ContaPoupanca extends Conta{}

fact {
--	all b:Banco | #(b.contas) = 2
--	all c:Conta | one c.~contas

}

pred addConta[b:Banco,c:Conta,t,t':Time]{
	c !in (b.contas).t
	(b.contas).t'=(b.contas).t + c
}

pred delConta[b:Banco,c:Conta,t,t':Time]{
	c in (b.contas).t
	(b.contas).t'=(b.contas).t - c
}

pred init[t:Time]{
	no (Banco.contas).t
}

fact traces{
	init[first]
	all pre: Time - last | let pos = pre.next |
		some b:Banco,c:Conta |
			addConta[b,c,pre,pos] or
			delConta[b,c,pre,pos]
}


assert bancoVazio {
	all b:Banco | some b.contas
}


pred show(){
--	#Banco =4
}

run show for 3 but 8 Time
check bancoVazio for 3
