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

Theorem reduceplus_eqp_com : forall (Q : list (poly A0 eqA ltM)) (p q r s : list (Term A n)), reduceplus Q p q -> canonical A0 eqA ltM p -> eqP A eqA n p r -> eqP A eqA n q s -> reduceplus Q r s.
intros Q p q r s H'; generalize r s; clear r s; elim H'; auto.
intros x y H'0 r s H'1 H'2 H'3.
apply Rstar_0; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := y); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := x); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x y z H'0 H'1 H'2 r s H'3 H'4 H'5.
apply Rstar_n with (y := y); auto.
apply reduce_eqp_com with (1 := cs) (p := x) (q := y); auto.
apply H'2; auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
