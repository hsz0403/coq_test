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

Lemma uiterTime_bound_onlyByN (P: nat -> _ -> Prop) boundL boundR n0 x0: (forall n x, n < n0 -> P n x -> match f x with | inl x' => P (S n) x' /\ fst (fT x tt) <= boundL | inr y => forall n', n <= n' -> fst (fT x tt) <= boundL + boundR n' end) -> P 0 x0 -> uiterTime n0 x0 <= n0 * (boundL + 9) + boundR n0.
Proof.
intros H'.
pose (n0':=n0).
assert (Hleq : n0<=n0') by (cbn;lia).
replace 0 with (n0'-n0) at 1 by (cbn;lia).
change (boundR n0) with (boundR n0').
change n0 with n0' in H'.
clearbody n0'.
induction n0 in x0,Hleq |-*.
1:cbn;Lia.nia.
intros HPx.
cbn -[plus].
specialize H' with (x:=x0).
destruct (f x0).
-
edestruct H' as [? ->].
2:eassumption.
lia.
rewrite IHn0.
2:easy.
now Lia.lia.
replace (n0'-n0) with (S (n0'-S n0)) by Lia.nia.
eapply H2.
-
rewrite H' with (n:=n0'-S n0) (n':=n0').
all:try now Lia.lia.
eassumption.
