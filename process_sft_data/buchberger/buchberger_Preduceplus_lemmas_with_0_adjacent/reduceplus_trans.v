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

Theorem reduceplus_trans : forall (Q : list (poly A0 eqA ltM)) (x y z : list (Term A n)), reduceplus Q x y -> canonical A0 eqA ltM x -> reduceplus Q y z -> reduceplus Q x z.
intros Q x y z H'; elim H'; auto.
intros x0 y0 H'0 H'1 H'2.
apply reduceplus_eqp_com with (p := y0) (q := z); auto.
apply eqp_imp_canonical with (1 := cs) (p := x0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x0 y0 z0 H'0 H'1 H'2 H'3 H'4.
apply Rstar_n with (y := y0); auto.
apply H'2; auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
