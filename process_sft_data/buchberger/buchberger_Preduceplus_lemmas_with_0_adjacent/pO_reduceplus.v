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

Lemma pO_reduceplus : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduceplus Q (pO A n) p -> p = pO A n.
intros Q p q H'; inversion H'; auto.
inversion H; auto.
case (pO_reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q y); auto.
