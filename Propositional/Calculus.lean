
-- Defining propositional formulae

def Variable := String

inductive Proposition
| atom : Variable -> Proposition
| neg  : Proposition -> Proposition
| conj : Proposition -> Proposition -> Proposition
| disj : Proposition -> Proposition -> Proposition
| imp  : Proposition -> Proposition -> Proposition
