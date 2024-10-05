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

Theorem in_multpf_head : forall (p q : list (Term A n)) (a b : Term A n), canonical A0 eqA ltM (pX a p) -> canonical A0 eqA ltM (pX b q) -> In (multTerm (A:=A) multA (n:=n) a b) (multpf (pX a p) (pX b q)).
intros p q a b H' H'0.
elim (multpf_head p q a b); [ intros c E; rewrite E | idtac | idtac ]; simpl in |- *; auto.
