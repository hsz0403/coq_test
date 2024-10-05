Require Export Pmults.
Section Pmult.
Load hCoefStructure.
Load hOrderStructure.
Load hMults.
Fixpoint multpf (p : list (Term A n)) : list (Term A n) -> list (Term A n) := fun q : list (Term A n) => match p with | nil => pO A n | a :: p' => pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a q) (multpf p' q) end.
Hint Resolve canonical_multpf : core.
Definition smult : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros sp1 sp2.
case sp1; case sp2.
intros p1 H'1 p2 H'2; exists (multpf p1 p2); auto.
Defined.
End Pmult.

Theorem multpf_head : forall (p q : list (Term A n)) (a b : Term A n), canonical A0 eqA ltM (pX a p) -> canonical A0 eqA ltM (pX b q) -> exists c : list (Term A n), multpf (pX a p) (pX b q) = pX (multTerm (A:=A) multA (n:=n) a b) c.
intros p; elim p; clear p; auto.
simpl in |- *; intros q a b H' H'0.
cut (canonical A0 eqA ltM q); [ intros Op0 | apply canonical_imp_canonical with (a := b) ]; auto.
exists (mults (A:=A) multA (n:=n) a q); simpl in |- *; auto.
rewrite <- pO_pluspf_inv2; auto.
intros a1 p H' q a0 b H'0 H'1; auto.
elim (H' q a1 b); simpl in |- *; [ intros c E | idtac | idtac ]; auto.
2: apply canonical_imp_canonical with (a := a0); auto.
rewrite E.
exists (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec (mults (A:=A) multA (n:=n) a0 q) (pX (multTerm (A:=A) multA (n:=n) a1 b) c)); auto.
rewrite <- pluspf_inv1_eq; auto.
apply multTerm_ltT_r; auto.
apply (canonical_pX_order _ A0 eqA) with (l := p); auto.
