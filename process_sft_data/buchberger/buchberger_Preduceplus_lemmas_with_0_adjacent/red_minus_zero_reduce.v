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

Theorem red_minus_zero_reduce : forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> reduceplus Q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) (pO A n) -> exists r1 : list (Term A n), reduceplus Q p r1 /\ reduceplus Q q r1.
intros Q p q H' H'0 H'1.
elim (red_plus_zero_reduce Q p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)); [ intros r1 E; elim E; intros H'8 H'9; clear E | idtac | idtac | idtac ]; auto.
exists r1; split; auto.
apply reduceplus_eqp_com with (p := q) (q := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r1)); auto.
apply reduceplus_mults_invr; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) r1); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply reduceplus_eqp_com with (p := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) (q := pO A n); auto.
