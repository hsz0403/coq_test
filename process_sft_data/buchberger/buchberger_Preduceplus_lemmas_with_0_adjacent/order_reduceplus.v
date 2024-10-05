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

Theorem order_reduceplus : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduceplus Q p q -> canonical A0 eqA ltM p -> ltP (A:=A) (n:=n) ltM q p \/ eqP A eqA n p q.
intros Q p q H'; elim H'; auto.
intros x y z H'0 H'1 H'2 H'3; left; try assumption.
elim H'2; [ intros H'5; try exact H'5; clear H'2 | intros H'5; clear H'2 | clear H'2 ].
apply ltP_trans with (y := y); auto.
apply ltP_reduce with (1 := cs) (3 := H'0); auto.
apply (ltp_eqp_comp A A0 eqA) with (p := y) (q := x); auto.
apply ltP_reduce with (1 := cs) (3 := H'0); auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
