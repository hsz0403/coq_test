Require Export Pspoly.
Require Export Pmult.
Section crit.
Load hCoefStructure.
Load hOrderStructure.
Load hSpoly.
Load hMult.
Definition Rminus : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), list (Term A n) -> list (Term A n) -> list (Term A n) -> list (Term A n).
intros a nZa p q r; elim r; clear r.
exact p.
intros b r Rec; exact (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec Rec (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=a) nZa) q)).
Defined.
Definition divPp : Term A n -> list (Term A n) -> Prop.
intros a p; elim p; clear p.
exact True.
intros b p Rec; exact (divP A A0 eqA multA divA n b a /\ Rec).
Defined.
Hint Resolve divP_inv3 : core.
Hint Resolve divP_inv3 : core.
Definition divpf : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), list (Term A n) -> list (Term A n).
intros a nZa p; elim p; clear p.
exact (pO A n).
intros b p Rec; exact (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (pX (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=a) nZa) (pO A n)) Rec).
Defined.
Hint Resolve divpf_canonical : core.
Hint Resolve canonical_Rminus : core.
Definition Dmult : forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a), list (Term A n) -> list (Term A n) -> list (Term A n).
intros a nZa p q; elim p; clear p.
exact (pO A n).
intros a1 p1 rec; exact (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (divpf a nZa (mults (A:=A) multA (n:=n) a1 q)) rec).
Defined.
Hint Resolve canonical_Dmult : core.
End crit.

Theorem minuspf_spoly_in : forall (a b : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b), eqT (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) a b) -> forall p q : list (Term A n), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> (forall c : Term A n, In c p -> ltT ltM c (multTerm (A:=A) multA (n:=n) a b) /\ eqT c (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) b)) -> (forall c : Term A n, In c q -> ltT ltM c (multTerm (A:=A) multA (n:=n) a b) /\ eqT c (multTerm (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) a)) -> forall c : Term A n, In c p -> In c (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q).
intros a b nZa nZb H'1 p q; pattern p, q in |- *.
apply (Opm_ind A n ltM ltM_dec); simpl in |- *; intros; auto.
elim H3; auto.
rewrite minuspf_pO_refl_eq; auto.
rewrite <- minuspf_inv2_eq; simpl in |- *; auto.
right; apply H; auto.
apply canonical_imp_canonical with (a := b0); auto.
rewrite <- minuspf_inv1_eq; simpl in |- *; auto.
elim H5; intros H'2; clear H5; auto.
right; apply H; auto.
apply canonical_imp_canonical with (a := a0); auto.
elim (H4 b0); [ intros H'4 H'5 | idtac ]; auto.
elim (H3 a0); [ intros H'6 H'7 | idtac ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p0); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) b0); [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q0); auto ].
absurd (eqT (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) a b)); auto.
apply eqT_not_ltT with (1 := os); auto.
case (ltT_dec A n ltM ltM_dec (ppc (A:=A) A1 (n:=n) a b) a0); intros test; [ case test; clear test; intros test | idtac ].
apply (ltT_trans A n ltM os) with (y := a0); auto.
absurd (ltT ltM a0 (ppc (A:=A) A1 (n:=n) a b)); auto.
apply divP_is_not_order with (1 := cs); auto.
cut (ppcm A A0 eqA multA divA n a b (ppc (A:=A) A1 (n:=n) a b)); [ intros H'8; inversion H'8 | idtac ]; auto.
apply H6; auto.
apply eqT_nzero_eqT_divP with (c := b0) (nZb := nZa) (1 := cs); auto.
apply eqT_nzero_divP with (nZb := nZb) (1 := cs); auto.
apply ppc_is_ppcm with (1 := cs); auto.
apply eqT_compat_ltTl with (b := a0); auto.
apply (eqT_sym A n); auto.
