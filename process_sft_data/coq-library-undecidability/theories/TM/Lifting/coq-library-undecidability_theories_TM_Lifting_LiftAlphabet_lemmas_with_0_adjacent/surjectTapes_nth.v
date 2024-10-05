From Undecidability Require Import TM.Util.Prelim TM.Util.Relations TM.Util.TM_facts.
Section SujectTape.
Variable sig tau : Type.
Variable g : tau -> option sig.
Variable def : sig.
Definition surject : tau -> sig := fun t => match (g t) with Some s => s | None => def end.
Definition surjectTape := mapTape surject.
End SujectTape.
Hint Unfold surjectTape : tape.
Section lift_sigma_tau.
Variable n : nat.
Variable sig tau : Type.
Variable g : tau -> option sig.
Variable def : sig.
Variable F : Type.
Definition surjectTapes : tapes tau n -> tapes sig n := Vector.map (surjectTape g def).
Definition lift_sigma_tau_Rel (R : Rel (tapes sig n) (F * tapes sig n)) : Rel (tapes tau n) (F * tapes tau n) := fun tin '(yout,tout) => R (surjectTapes tin) (yout, surjectTapes tout).
Definition lift_sigma_tau_T (T : Rel (Vector.t (tape sig) n) nat) : Rel (Vector.t (tape tau) n) nat := fun tin k => T (surjectTapes tin) k.
End lift_sigma_tau.
Arguments surjectTapes {n sig tau} (g) def !t.
Hint Rewrite surjectTapes_nth : tape.
Arguments lift_sigma_tau_Rel {n sig tau} (g def) {F} (R) x y /.
Arguments lift_sigma_tau_T {n sig tau} (g def T) x y /.
Section InjectTape.
Variable sig tau : Type.
Variable f : sig -> tau.
Definition injectTape := mapTape f.
Definition injectTapes {n: nat} := mapTapes (n := n) f.
End InjectTape.
Section InjectSurject.
Variable sig tau : Type.
Variable inj : Retract sig tau.
Variable def : sig.
End InjectSurject.
Section TranslateAct.
Variable X Y : Type.
Definition map_act : (X -> Y) -> option X * move -> option Y * move := fun f => map_fst (map_opt f).
End TranslateAct.
Section LiftAlphabet.
Variable sig tau : finType.
Variable n : nat.
Variable F : finType.
Variable pMSig : pTM sig F n.
Variable Inj : Retract sig tau.
Variable def : sig.
Definition surjectReadSymbols : Vector.t (option tau) n -> Vector.t (option sig) n := Vector.map (map_opt (surject Retr_g def)).
Definition lift_trans := fun '(q, sym) => let (q', act) := trans (m := projT1 pMSig) (q, surjectReadSymbols sym) in (q', Vector.map (map_act Retr_f) act).
Definition LiftAlphabet_TM : TM tau n := {| trans := lift_trans; start := start (projT1 pMSig); halt := halt (m := projT1 pMSig) |}.
Definition LiftAlphabet :pTM tau F n := (LiftAlphabet_TM; projT2 pMSig).
Definition surjectConf : (mconfig tau (state LiftAlphabet_TM) n) -> (mconfig sig (state (projT1 pMSig)) n) := fun c => mk_mconfig (cstate c) (surjectTapes Retr_g def (ctapes c)).
End LiftAlphabet.
Arguments LiftAlphabet : simpl never.
Ltac smpl_TM_LiftAlphabetSigma := once lazymatch goal with | [ |- LiftAlphabet _ _ _ ⊨ _] => eapply LiftAlphabet_Realise; swap 1 2 | [ |- LiftAlphabet _ _ _ ⊨c(_) _] => eapply LiftAlphabet_RealiseIn; swap 1 2 | [ |- projT1 (LiftAlphabet _ _ _) ↓ _] => eapply LiftAlphabet_TerminatesIn; swap 1 2 end.
Smpl Add smpl_TM_LiftAlphabetSigma : TM_Correct.

Lemma surjectTapes_nth t i : (surjectTapes t)[@i] = surjectTape g def t[@i].
Proof.
unfold surjectTapes.
now simpl_vector.
