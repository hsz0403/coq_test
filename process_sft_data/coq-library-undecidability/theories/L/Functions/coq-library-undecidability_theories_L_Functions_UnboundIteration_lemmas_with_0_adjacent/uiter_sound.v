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

Lemma uiter_sound n x y: loopSum n f x = Some y -> evalLe (uiterTime n x) (app uiter (enc x)) (enc y).
Proof.
unfold uiter.
Intern.recRem P.
induction n in x|-*;intros Heq.
now easy.
cbn in Heq|-*.
eapply (@le_evalLe_proper (match f x with inl x' => _ | _ => _ end)).
2,3:reflexivity.
2:{
destruct (f x) eqn:eqfx.
-
Intern.recStepNew P.
Lsimpl.
rewrite eqfx.
Lsimpl.
eapply IHn.
eauto.
-
inv Heq.
Intern.recStepNew P.
Lsimpl.
rewrite eqfx.
Lsimpl.
Lreflexivity.
}
destruct (f x).
all:solverec.
