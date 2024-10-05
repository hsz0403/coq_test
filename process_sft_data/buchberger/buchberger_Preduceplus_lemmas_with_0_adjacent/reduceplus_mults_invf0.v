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

Theorem reduceplus_mults_invf0 : forall a : Term A n, ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqT a (T1 A1 n) -> forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)), reduceplus Q p q -> canonical A0 eqA ltM p -> forall r s : list (Term A n), canonical A0 eqA ltM r -> eqP A eqA n p (mults (A:=A) multA (n:=n) a r) -> eqP A eqA n q (mults (A:=A) multA (n:=n) a s) -> reduceplus Q r s.
intros a H' H'0 Q p q H'1; elim H'1; auto.
intros x y H'2 H'3 r s H'4 H'5 H'6.
apply Rstar_0; auto.
apply mults_eqp_inv with (a := a) (1 := cs); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := y); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := x); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x y z H'2 H'3 H'4 H'5 r s H'6 H'7 H'8.
apply Rstar_n with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=a) H') y); auto.
apply reduce_mults_invf with (1 := cs); auto.
apply reduce_eqp_com with (1 := cs) (p := x) (q := y); auto.
apply H'4; auto.
apply canonical_reduce with (1 := cs) (3 := H'2); auto.
apply canonical_mults with (1 := cs); auto.
apply canonical_reduce with (1 := cs) (3 := H'2); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) a (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=a) H')) y); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (multTerm (A:=A) multA (n:=n) a (T1 A1 n)) (b:=a) H') y); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a) H') y); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply divTerm_multTerm_l with (1 := cs); auto.
apply divTerm_on_eqT with (1 := cs); auto.
apply (eqT_sym A n); auto.
