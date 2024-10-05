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

Lemma uiterTime_computesRel (R : X -> X -> Prop) x0 k0 (t__step t__end : nat): (forall k' x, k' < k0 -> pow R k' x0 x -> fst (fT x tt) <= t__step + match f x with | inr _ => t__end | _ => 0 end /\ match f x with | inl x' => R x x' | _ => True end) -> uiterTime k0 x0 <= k0 * (t__step + 9) + t__end.
Proof.
intros H'.
rewrite uiterTime_bound_onlyByN with (P:= fun n x =>pow R n x0 x) (boundL := t__step) (boundR := fun _ => t__end).
-
Lia.lia.
-
intros n x lt'' R'.
specialize H' with (1:=lt'') (2:=R') as [H' H''].
destruct (f x).
+
split.
2:easy.
replace (S n) with (n+1) by lia.
eapply pow_add.
eexists x.
split.
eauto.
apply rcomp_1 with (R:=R).
tauto.
+
intro.
lia.
-
reflexivity.
