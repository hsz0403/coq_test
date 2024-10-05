Set Implicit Arguments.
Require Import List Arith Lia Morphisms FinFun Init.Wf.
From Undecidability.HOU Require Import std.decidable.
Import ListNotations.
Set Default Proof Using "Type".
Arguments incl {_} _ _.
Definition seteq {X: Type} (A B: list X) := incl A B /\ incl B A.
Definition strict_incl {X: Type} (A B: list X) := incl A B /\ exists x, In x B /\ ~ In x A.
Notation "a ∈ A" := (In a A) (at level 70).
Notation "A ⊆ B" := (incl A B) (at level 70).
Notation "A ⊊ B" := (strict_incl A B) (at level 70).
Notation "A === B" := (seteq A B) (at level 70).
Notation "| A |" := (length A) (at level 65).
Section BasicLemmas.
Variable X Y: Type.
Implicit Type f: X -> Y.
Implicit Type p: X -> bool.
Implicit Type A B C : list X.
Implicit Type a b c : X.
Global Instance incl_preorder: PreOrder (@incl X).
Proof.
firstorder.
Global Instance strict_incl_transitive: Transitive (@strict_incl X).
Proof.
firstorder.
Global Instance seteq_preorder: PreOrder (@seteq X).
Proof.
firstorder.
Global Instance seteq_equivalence: Equivalence (@seteq X).
Proof.
firstorder.
Hint Resolve incl_refl seteq_refl : listdb.
Global Instance proper_in_incl: Proper (eq ++> incl ==> Basics.impl) (@In X).
Proof.
intros ?? -> ???.
firstorder.
Global Instance in_seteq_proper: Proper (eq ++> seteq ++> iff) (@In X).
Proof.
intros ?? -> ???.
firstorder.
Global Instance subrel_incl_seteq: subrelation seteq (@incl X).
Proof.
intros ??; firstorder.
Global Instance incl_seteq_proper: Proper (seteq ++> seteq ++> iff) (@incl X).
Proof.
firstorder.
Global Instance incl_cons_proper: Proper (eq ++> incl ++> incl) (@cons X).
Proof.
intros ??-> ???; firstorder.
Global Instance seteq_cons_proper: Proper (eq ++> seteq ++> seteq) (@cons X).
Proof.
intros ??-> ???; firstorder.
Hint Resolve incl_seteq seteq_incl_left seteq_incl_right incl_nil incl_cons incl_cons_build incl_cons_project_l incl_cons_project_r incl_cons_drop incl_filter incl_distr_left incl_distr_right incl_app_project_left incl_app_project_right incl_app_build : listdb.
Global Instance strict_incl_incl_subrel: subrelation (@strict_incl X) (@incl X).
Proof.
firstorder.
Section WellFoundedStrictInclusion.
Context {D: Dis X}.
End WellFoundedStrictInclusion.
Global Instance proper_app_incl: Proper (incl ++> incl ++> incl) (@app X).
Proof.
intros A A' H1 B B' H2; induction A; firstorder auto with *.
Global Instance proper_app_seteq: Proper (seteq ++> seteq ++> seteq) (@app X).
Proof.
intros A A' [H1 H2] B B' [H3 H4].
split; eapply proper_app_incl; firstorder.
Hint Rewrite app_nil_l app_nil_r : listdb.
Hint Rewrite <- app_comm_cons : listdb.
Hint Rewrite -> in_app_iff : listdb.
Global Instance proper_incl_seteq: Proper (@seteq X ++> @seteq X ++> iff) incl.
Proof.
intros ??????; firstorder.
Global Instance proper_rev_incl: Proper (incl ++> incl) (@rev X).
Proof.
intros A B H.
now rewrite rev_seteq, H, rev_seteq.
Global Instance proper_rev_seteq: Proper (seteq ++> seteq) (@rev X).
Proof.
intros A B [H1 H2]; split; eapply proper_rev_incl; eauto.
Hint Rewrite rev_seteq rev_involutive rev_length rev_app_distr : listdb.
Global Instance map_incl_proper : Proper (eq ++> incl ++> incl) (@map Y X).
Proof.
intros ?? -> A B H.
induction A; cbn; eauto with listdb.
eapply incl_cons_build; firstorder.
eapply in_map; firstorder.
Global Instance map_seteq_proper : Proper (eq ++> seteq ++> seteq) (@map Y X).
Proof.
intros ?? -> A B [H1 H2]; split; apply map_incl_proper; firstorder.
Hint Rewrite map_id map_rev map_nil map_cons map_app map_length : listdb.
Hint Resolve in_map : listdb.
Hint Rewrite app_length map_length rev_length : listdb.
Global Instance filter_incl_proper: Proper (eq ++> incl ++> incl) (@filter X).
Proof.
intros ?? -> A B H2; induction A; cbn; eauto with listdb.
destruct y eqn: H1; eauto with listdb.
eapply incl_cons_build; eauto with listdb.
eapply filter_In; intuition.
Global Instance filter_seqteq_proper: Proper (eq ++> seteq ++> seteq) (@filter X).
Proof.
intros f g -> A B [H2 H3]; split; apply filter_incl_proper; firstorder.
End BasicLemmas.
Hint Resolve incl_refl seteq_refl : listdb.
Hint Resolve incl_seteq seteq_incl_left seteq_incl_right incl_nil incl_cons incl_cons_build incl_cons_project_l incl_cons_project_r incl_cons_drop incl_filter incl_distr_left incl_distr_right incl_app_project_left incl_app_project_right incl_app_build : listdb.
Hint Rewrite -> in_app_iff : listdb.
Hint Rewrite <- app_comm_cons : listdb.
Hint Rewrite app_nil_l app_nil_r : listdb.
Hint Rewrite rev_seteq rev_involutive rev_length rev_app_distr : listdb.
Hint Rewrite map_id map_rev map_nil map_cons map_app : listdb.
Hint Resolve in_map : listdb.
Hint Rewrite app_length map_length rev_length : listdb.
Hint Extern 4 => match goal with |[ H: ?x ∈ nil |- _ ] => destruct H end : core.
Ltac lsimpl := autorewrite with listdb.
Tactic Notation "lsimpl" "in" hyp_list(H) := autorewrite with listdb in H.
Tactic Notation "lsimpl" "in" "*" := autorewrite with listdb in *.
Ltac lauto := eauto with listdb.

Lemma incl_seteq A B: A ⊆ B -> B ⊆ A -> A === B.
Proof.
Admitted.

Lemma incl_nil A: nil ⊆ A.
Proof.
Admitted.

Lemma incl_cons a A B: a :: A ⊆ B <-> a ∈ B /\ A ⊆ B.
Proof.
Admitted.

Lemma incl_cons_build a A B: a ∈ B -> A ⊆ B -> a :: A ⊆ B.
Proof.
Admitted.

Lemma incl_cons_project_l a A B: a :: A ⊆ B -> a ∈ B.
Proof.
Admitted.

Lemma incl_cons_project_r a A B: a :: A ⊆ B -> A ⊆ B.
Proof.
Admitted.

Lemma incl_cons_drop b A B : A ⊆ B -> A ⊆ b :: B.
Proof.
Admitted.

Lemma incl_filter p A: filter p A ⊆ A.
Proof.
Admitted.

Lemma incl_distr_left A B C: A ⊆ B -> A ⊆ B ++ C.
Proof.
Admitted.

Lemma incl_distr_right A B C: A ⊆ C -> A ⊆ B ++ C.
Proof.
Admitted.

Lemma incl_app_project_right A B C: A ++ B ⊆ C -> B ⊆ C.
Proof.
intros H x Hx.
eapply H, in_app_iff.
Admitted.

Lemma incl_app_build A B C: A ⊆ C -> B ⊆ C -> A ++ B ⊆ C.
Proof.
Admitted.

Lemma strict_incl_incl A B: A ⊊ B -> A ⊆ B.
Proof.
Admitted.

Lemma incl_strict_incl x A B: x ∈ A -> ~ x ∈ B -> A ⊆ B -> A ⊊ B.
Proof.
Admitted.

Lemma strict_incl_eq A B: A ⊊ B -> ~ A === B.
Proof.
Admitted.

Lemma strict_incl_project A B: A ⊊ B -> exists x, x ∈ B /\ ~ x ∈ A.
Proof.
Admitted.

Lemma nodup_seteq A: nodup D A === A.
Proof.
Admitted.

Lemma wf_strict_incl: well_founded (@strict_incl X).
Proof using D.
eapply well_founded_lt_compat with (f := fun A => length (nodup eq_dec A)).
intros A B [H [x [H1 H2]]].
assert (nodup eq_dec A ⊆ nodup eq_dec B) as H3 by now rewrite !nodup_seteq.
eapply NoDup_incl_length in H3 as H4; [| eapply NoDup_nodup].
eapply le_lt_or_eq in H4 as []; eauto; exfalso.
eapply NoDup_length_incl in H3.
rewrite !nodup_seteq in H3; intuition.
eapply NoDup_nodup.
Admitted.

Lemma app_comm A B: A ++ B === B ++ A.
Proof.
Admitted.

Lemma rev_seteq A: rev A === A.
Proof.
Admitted.

Lemma incl_app_project_left A B C: A ++ B ⊆ C -> A ⊆ C.
Proof.
intros H x Hx.
eapply H, in_app_iff.
eauto.
