From Undecidability.L Require Import Tactics.LTactics Datatypes.LSum Datatypes.LOptions.
From Undecidability.L Require Export Prelim.LoopSum.
Section uiter.
Variable X Y : Type.
Context `{registered X}.
Context `{registered Y}.
Variable f : X -> X + Y.
Variable fT : timeComplexity (X -> X + Y).
Context `{computableTime' f fT}.
Import HOAS_Notations.
Definition uiter := Eval cbn -[enc] in rho [L_HOAS (λ uiter x, !!(extT f) x (λ x' _ , uiter x') (λ y _ , y) !!I)].
Hint Resolve uiter_proc : LProc.
Fixpoint uiterTime n x := match n with 0 => 0 | S n' => fst (fT x tt) + 9 + match f x with inl x' => uiterTime n' x' | _ => 0 end end.
End uiter.
Hint Resolve uiter_proc : LProc.
Arguments uiter _ _ _ _ _ _ _ : clear implicits.
Arguments uiter {X Y H H0} f {fT H1}.

Lemma uiterTime_bound_recRel2 (P: nat -> _ -> Prop) (iterT : X -> nat): (forall i x, P i x -> match f x with | inl x' => P (S i) x' /\ iterT x' + 9 + fst (fT x tt) <= iterT x | inr y => fst (fT x tt) + 9 <= iterT x end) -> forall n x, P 0 x -> uiterTime n x <= iterT x.
Proof.
intros H' n x.
pose (n':=n).
assert (Hleq : n<=n') by (cbn;lia).
replace 0 with (n'-n) at 1 by (cbn;lia).
clearbody n'.
induction n in x,Hleq |-*.
1:cbn;Lia.nia.
intros HPx.
cbn -[plus].
specialize H' with (x:=x).
destruct (f x) as [x'|y] eqn:eq.
-
edestruct H' as [? H''].
eassumption.
rewrite IHn.
2:easy.
2:{
replace (n'-n) with (S (n'-S n)) by Lia.nia.
eassumption.
}
Lia.lia.
-
cbn.
rewrite <- H'.
2:easy.
all:Lia.lia.
