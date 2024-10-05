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

Theorem rep_minus_reduce : forall (Q : list (poly A0 eqA ltM)) (p q s : list (Term A n)), reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) s -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> exists p1 : list (Term A n), (exists q1 : list (Term A n), reduceplus Q p p1 /\ reduceplus Q q q1 /\ eqP A eqA n s (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p1 q1)).
intros Q p q s H' H'0 H'1.
elim (rep_plus_reduce Q p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) s); [ intros p1 E; elim E; intros q1 E0; elim E0; intros H'9 H'10; elim H'10; intros H'11 H'12; clear H'10 E0 E | idtac | idtac | idtac ]; auto.
exists p1; exists (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q1); split; [ idtac | split ]; auto.
apply reduceplus_mults_invr; auto.
cut (canonical A0 eqA ltM p1); [ intros Cp1 | idtac ].
cut (canonical A0 eqA ltM q1); [ intros Cq1 | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 q1); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q1))); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) q1)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 (mults (A:=A) multA (n:=n) (T1 A1 n) q1)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply canonical_reduceplus with (Q := Q) (p := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q); auto.
apply canonical_reduceplus with (Q := Q) (p := p); auto.
apply reduce_eqp_com with (1 := cs) (p := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q) (q := s); auto.
