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

Lemma uiter_total_instanceTime {Z} `{registered Z} (f': Z -> Y) (preprocess : Z -> X) preprocessT (fuel : Z -> nat) `{computableTime' preprocess preprocessT} : (forall x, loopSum (fuel x) f (preprocess x) = Some (f' x)) -> computesTime (TyArr _ _) f' (convert (λ x, !!uiter (!!(extT preprocess) x))) (fun z _ => (1 + fst (preprocessT z tt) + uiterTime (fuel z) (preprocess z),tt)).
Proof.
cbn [convert TH "-"].
intros total.
eapply computesTimeTyArr_helper with (time:=(fun x _ => _)).
{
unfold uiter.
now Lproc.
}
intros z [].
cbn.
split.
now reflexivity.
intros ? ->.
eexists.
split.
2:reflexivity.
eapply le_evalLe_proper.
2-3:reflexivity.
2:{
eapply evalLe_trans with (t := (L.app uiter (enc (preprocess z)))).
-
now Lsimpl.
-
eapply uiter_sound.
apply total.
}
cbn.
lia.
