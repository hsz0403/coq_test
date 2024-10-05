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

Lemma Realise : M ⊨ Rel.
Proof.
eapply Realise_monotone.
{
unfold M.
TM_Correct.
eapply RealiseIn_Realise,WriteString_Sem.
}
{
intros tin ((), tout) H.
TMSimp.
destruct H2 as (?&->&?);cbn.
simpl_tape.
rewrite WriteString_L_left;cbn.
autorewrite with list.
erewrite !tape_right_move_left.
2:{
rewrite WriteString_L_current.
autorewrite with list.
cbn.
reflexivity.
}
rewrite WriteString_L_right.
cbn.
eexists.
repeat (cbn;autorewrite with list;try rewrite !map_map).
split.
reflexivity.
rewrite tl_length,List.skipn_length.
unfold size.
nia.
}
