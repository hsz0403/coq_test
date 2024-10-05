Require Export Pplus.
Section Pmults.
Load hCoefStructure.
Load hOrderStructure.
Load hPlus.
Set Implicit Arguments.
Unset Strict Implicit.
Definition mults : Term A n -> list (Term A n) -> list (Term A n).
intros a p; elim p; clear p.
exact (pO A n).
intros b p1 p'1.
exact (pX (multTerm (A:=A) multA (n:=n) a b) p'1).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve multTerm_eqT : core.
Hint Resolve invTerm_eqT : core.
Hint Resolve T1_is_min_ltT : core.
Set Implicit Arguments.
Unset Strict Implicit.
Definition tmults : Term A n -> list (Term A n) -> list (Term A n).
intros a; case (zeroP_dec A A0 eqA eqA_dec n a); intros Z0.
intros H'; exact (pO A n).
intros p; exact (mults a p).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve multlm_comp_canonical : core.
Let ffst := fst (A:=list (Term A n)) (B:=list (Term A n)).
Let ssnd := snd (A:=list (Term A n)) (B:=list (Term A n)).
Let ppair := pair (A:=list (Term A n)) (B:=list (Term A n)).
Definition twoP_ind : forall P : list (Term A n) -> list (Term A n) -> Prop, (forall p q : list (Term A n), (forall r s : list (Term A n), lessP A n (r, s) (p, q) -> P r s) -> P p q) -> forall p q : list (Term A n), P p q.
intros P H' p q; try assumption.
change ((fun pq : list (Term A n) * list (Term A n) => P (ffst pq) (ssnd pq)) (p, q)) in |- *.
cut (exists x : list (Term A n) * list (Term A n), x = ppair p q).
unfold ppair in |- *; intros H'0; elim H'0; intros x E; rewrite <- E; clear H'0.
pattern x in |- *; apply well_founded_ind with (A := (list (Term A n) * list (Term A n))%type) (R := lessP A n) (1 := wf_lessP A n); auto.
intros x0 H'0; apply H'; auto.
intros r s H'1.
apply (H'0 (r, s)).
generalize H'1; case x0; simpl in |- *; auto.
exists (ppair p q); auto.
Hint Resolve mults_dist_pluspf : core.
Definition smults : Term A n -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros a sp1.
case sp1.
intros p1 H'1; exists (tmults a p1); auto.
unfold tmults in |- *; case (zeroP_dec A A0 eqA eqA_dec n a); simpl in |- *; auto.
intros; apply canonical_mults; auto.
Defined.
End Pmults.

Theorem mults_ltP_comp : forall (a : Term A n) (p q : list (Term A n)), ltP (A:=A) (n:=n) ltM p q -> ltP (A:=A) (n:=n) ltM (mults a p) (mults a q).
intros a p q H'; elim H'; simpl in |- *; auto.
intros x y p0 q0 H'0; simpl in |- *; apply ltP_hd; auto.
apply multTerm_ltT_l with (1 := os); auto.
