Propositional logic --  Answers
==========
Pierre Bréchet 03672392
-----------

## 4.1 Question

To determine if a |= b, a pen-and-pencil approach requires to check whether
M(a) is included in M(b) or not, with M(a) being the set of all models where
the formula a is true.

* 4.1.1 False |= True iff M(False) = ø is in  M(a), which is always true.
* 4.1.2 True |= False iff M(a) is in ø, which is always false.
* 4.1.3 (A /\ B) |= (A <=> B) iff M(A /\ B) is in M(A <=> B).
The models for which  A /\ B is true is only the model A -> True, B -> True.
The models for which A <=> B is true are {(A -> True, B -> True), (A -> False, B -> False)
Therefore, M(A /\ B) is in M(A <=> B) and (A /\ B) |= (A <=> B) is true.
* 4.1.4 A <=> B is true for (A -> False, B -> False) whether (A \/ B) is not.
Therefore, (A <=> B) |= (A \/ B) is false
* 4.1.5 ~A \/ B is true for all models for which A <=> B is true.
Therefore, (A <=> B) |= (~A \/ B) is true.

The results are identical with the ones computed by the entails function.
Nethertheless, when computing by hand, we only check the valuations (models)
where a is true and check if under those models b is also true. The algorithm
is more exhaustive since it checks if a => b is a tautology, checking the
evaluation of a => b under every different valuations. The two approaches are
identical, since a valuation giving a true has to give b true (M(a) is in M(b)
for a => b being a tautology and reciprocally.

## 4.2

The pen-and-paper derivation gives the same results.

Smoke ==> Smoke is obviously a tautology, hence satisfiable

(Smoke ==> Fire) ==> (~Smoke ==> ~Fire) is true iff ~ (~ (Smoke) \/ Fire) \/ (Smoke \/ ~Fire) is true
iff (Smoke /\ ~Fire) \/ (Smoke \/ ~Fire)
Under the valuation {Smoke -> True , Fire -> False} the expression is true (satisfiable), 
but under {Smoke —> False, Fire -> True} the expression is false (not a tautology

Smoke | Fire | ~Fire is clearly a tautology

(Fire ==> Smoke) & Fire & ~Smoke is true iff (~Fire \/ Smoke) /\ Fire /\ ~Smoke
is true, which is clearly unsatisfiable.

By the pen-and-paper approach, we reason by equivalence (the proposition is
true iff ...) thanks to the laws of simplification. The result is the same.

## 4.3 The algorithms gives that B is a knave and C is a knight which
corresponds to the pen-and-paper solution. Nonetheless, we can't decide what
A is (we have to be careful, the algorithm says 'False' to both hypothesis
meaning we don't know and not both are false, A is either a knight or a knave).
The algorithm is trustworthy only when the result is 'True', otherwise we can't
say. It's not true the if KB |=/= a then KB |= ~a, since we could have not
enough information to decide whether KB |= a or not (it's the case with the
character A).


