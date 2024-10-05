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

Theorem rep_plus_zero_reduce : forall (Q : list (poly A0 eqA ltM)) (s t : list (Term A n)), reduceplus Q s t -> canonical A0 eqA ltM s -> forall p q : list (Term A n), eqP A eqA n s (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> eqP A eqA n t (pO A n) -> exists r1 : list (Term A n), reduceplus Q p r1 /\ reduceplus Q q (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r1).
intros Q s t H'; elim H'.
intros x y eqxy Op p q H'0 H'1 H'2 H'3; exists p; split; auto.
apply Rstar_0; auto.
cut (canonical A0 eqA ltM y); [ intros Cx | idtac ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pO A n) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec y (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec x (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q p) (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p)); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p p)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q (pO A n)); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply minuspf_refl with (1 := cs); auto.
apply eqp_imp_canonical with (1 := cs) (p := x); auto.
intros x y z H'0 H'1 H'2 H'3 p q H'4 H'5 H'6 H'7.
elim (rep_plus_reduce Q p q y); [ intros p1 E; elim E; intros q1 E0; elim E0; intros H'15 H'16; elim H'16; intros H'17 H'18; try exact H'17; clear H'16 E0 E | idtac | idtac | idtac ]; auto.
lapply H'2; [ intros H'8; elim (H'8 p1 q1); [ intros r1 E; elim E; intros H'16 H'19; clear E H'2 | clear H'2 | clear H'2 | clear H'2 | clear H'2 ] | clear H'2 ]; auto.
exists r1; split; auto.
apply reduceplus_trans with (y := p1); auto.
apply reduceplus_trans with (y := q1); auto.
apply canonical_reduceplus with (Q := Q) (p := p); auto.
apply canonical_reduceplus with (Q := Q) (p := q); auto.
apply eqp_imp_canonical with (1 := cs) (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p1 q1); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply canonical_pluspf; auto.
apply canonical_reduceplus with (Q := Q) (p := p); auto.
apply canonical_reduceplus with (Q := Q) (p := q); auto.
apply reduce_eqp_com with (p := x) (q := y) (1 := cs); auto.
