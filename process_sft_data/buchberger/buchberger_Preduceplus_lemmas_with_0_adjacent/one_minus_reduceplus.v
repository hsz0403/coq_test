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

Theorem one_minus_reduceplus : forall (Q : list (poly A0 eqA ltM)) (p1 p2 : list (Term A n)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p1 p2 -> forall r : list (Term A n), canonical A0 eqA ltM p1 -> canonical A0 eqA ltM r -> exists s : list (Term A n), reduceplus Q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p1 r) s /\ reduceplus Q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p2 r) s.
intros Q p1 p2 H' r H'0 H'1.
lapply (one_plus_reduceplus Q p1 p2); [ intros H'5; elim (H'5 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)); [ intros s E; elim E; intros H'9 H'10; clear E | idtac | idtac ] | idtac ]; auto.
exists s; split; auto.
apply reduceplus_eqp_com with (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)) (q := s); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
cut (canonical A0 eqA ltM p2); [ intros C0 | idtac ].
apply reduceplus_eqp_com with (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p2 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)) (q := s); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply canonical_reduce with (1 := cs) (3 := H'); auto.
