From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import CaseList WriteString Hoare.
Module Cons_constant.
Section Fix.
Context {Σ__X: finType} {X : Type} {cX : codable Σ__X X}.
Variable (c:X).
Definition M : pTM (sigList Σ__X)^+ unit 1 := WriteString Lmove (rev (inr sigList_cons::map (fun x => inr (sigList_X x)) ((encode c))));; Move Lmove;; Write (inl START).
Definition Rel : pRel (sigList Σ__X)^+ unit 1 := ignoreParam ( fun tin tout => forall l (s0 : nat), tin[@Fin0] ≃(;s0) l -> tout[@Fin0] ≃(;s0 - size c - 1) c :: l ).
Definition time {sigX} {X : Type} {cX : codable sigX X} (c:X) := 5 + 2 * size c.
End Fix.
End Cons_constant.
Ltac hstep_Cons_constant := match goal with | [ |- TripleT ?P ?k (Cons_constant.M _) ?Q ] => eapply Cons_constant.SpecT end.
Smpl Add hstep_Cons_constant : hstep_Spec.

Lemma SpecT (l:list X) ss: TripleT ≃≃([],withSpace [|Contains _ l|] ss) (time c) M (fun _ => ≃≃([],withSpace [|Contains _ (c::l)|] (appSize [|fun s0 => s0 - size c - 1|] ss ))).
Proof.
unfold withSpace in *.
eapply Realise_TripleT.
now apply Realise.
now apply Terminates.
-
intros tin yout tout H HEnc.
cbn in *.
specialize (HEnc Fin0).
simpl_vector in *; cbn in *.
modpon H.
tspec_solve.
-
intros tin k HEnc Hk.
cbn in *.
specialize (HEnc Fin0).
simpl_vector in *; cbn in *.
do 2 eexists.
2:assumption.
contains_ext.
