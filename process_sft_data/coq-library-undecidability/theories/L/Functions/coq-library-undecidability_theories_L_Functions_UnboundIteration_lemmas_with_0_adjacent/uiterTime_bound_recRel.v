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

Lemma uiterTime_bound_recRel (P: nat -> _ -> Prop) (iterT : nat -> X -> nat) n: (forall i x, P i x -> match f x with | inl x' => P (S i) x' /\ iterT (n-i-1) x' + 9 + fst (fT x tt) <= iterT (n-i) x | inr y => fst (fT x tt) + 9 <= iterT (n-i) x end) -> forall x k, k <= n -> P (n-k) x -> uiterTime k x <= iterT k x.
Proof.
intros H' x k.
induction k in x |-*.
1:now cbn;Lia.nia.
intros ? HPx.
cbn -[plus].
specialize H' with (x:=x).
destruct (f x) as [x'|y] eqn:eq.
-
edestruct H' as [? H''].
eassumption.
rewrite IHk.
+
replace (n - (n - (S k))) with (1+k) in H'' by Lia.lia.
cbn in H''.
rewrite Nat.sub_0_r in H''.
Lia.nia.
+
easy.
+
replace (n-k) with (S (n-S k)) by Lia.nia.
eassumption.
-
replace (S k) with (n - (n - S k)) by Lia.lia.
rewrite <- H'.
all:easy.
