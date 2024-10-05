Require Export Preduce.
Section Preduceplus.
Load hCoefStructure.
Load hOrderStructure.
Load hReduce.
Inductive reduceplus (Q : list (poly A0 eqA ltM)) : list (Term A n) -> list (Term A n) -> Prop := | Rstar_0 : forall x y : list (Term A n), eqP A eqA n x y -> reduceplus Q x y | Rstar_n : forall x y z : list (Term A n), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q x y -> reduceplus Q y z -> reduceplus Q x z.
Hint Resolve Rstar_0 : core.
Hint Resolve reduceplus_skip : core.
Hint Resolve reduce_imp_reduceplus : core.
End Preduceplus.

Theorem canonical_reduceplus : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduceplus Q p q -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q.
intros Q p q H'; elim H'; auto.
intros x y H H0.
apply eqp_imp_canonical with (1 := cs) (p := x); auto.
intros x y z H'0 H'1 H'2 H'3.
apply H'2; auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
