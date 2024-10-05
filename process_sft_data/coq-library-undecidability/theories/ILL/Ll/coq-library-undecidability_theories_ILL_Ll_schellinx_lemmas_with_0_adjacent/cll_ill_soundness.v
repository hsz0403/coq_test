Require Import List Permutation.
From Undecidability.Shared.Libs.DLW Require Import utils.
From Undecidability.ILL Require Import ILL CLL ill_cll.
Set Implicit Arguments.
Fact app_eq_single_inv X (l m : list X) x : l++m = x::nil -> l = nil /\ m = x::nil \/ l = x::nil /\ m = nil.
Proof.
intros H.
destruct l as [ | y l ]; auto.
right.
inversion H.
destruct l; destruct m; auto; discriminate.
Tactic Notation "app" "inv" "singleton" "in" hyp(H) := apply app_eq_single_inv in H as [ (-> & ->) | (-> & ->) ].
Tactic Notation "app" "inv" "nil" "in" hyp(H) := apply app_eq_nil in H as (-> & ->).
Local Infix "~p" := (@Permutation _) (at level 70).
Notation "Γ '⊢i' A" := (S_ill Γ A) (at level 70, no associativity).
Notation "Γ '⊢c' Δ" := (S_cll Γ Δ) (at level 70, no associativity).
Section ill_cll_is_sound.
Hint Resolve Permutation_map : core.
End ill_cll_is_sound.
Section Schellinx_observation.
Let schellinx_rec Γ Δ : Γ ⊢c Δ -> Δ = ∅ -> exists f, In f Γ /\ cll_has_bot_zero_neg f.
Proof.
induction 1 as [ A (* ax *) | Γ Δ Γ' Δ' H1 H2 H3 IH3 (* perm *) | Γ Δ A H1 IH1 | Γ Δ A H1 IH1 (* negation *) | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ Δ A B H1 IH1 (* -o *) | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 H2 IH2 (* & *) | Γ A B Δ H1 IH1 | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 (* * *) | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ A B Δ H1 IH1 (* par *) | Γ A B Δ H1 IH1 H2 IH2 | Γ A B Δ H1 IH1 | Γ A B Δ H1 IH1 (* + *) | | (* bot, top *) | Γ Δ H1 IH1 | (* unit *) | | (* zero *) | Γ A Δ H1 IH1 | Γ A Δ H1 IH1 (* bang *) | Γ A Δ H1 IH1 | (* qmrk *) | Γ A Δ H1 IH1 | (* weak *) | Γ A Δ H1 IH1 | ]; (* cntr *) try discriminate.
+
intros ->.
apply Permutation_sym, Permutation_nil in H2 as ->; auto.
destruct IH3 as (f & G1 & G2); auto.
exists f; split; auto.
revert G1; now apply Permutation_in.
+
intros ->; exists (⊖A); simpl; auto.
+
intros H.
app inv nil in H.
destruct IH2 as (f & [ <- | ] & ?); auto.
*
exists (A ⊸ B); simpl; split; auto.
*
exists f; split; auto.
right; apply in_or_app; tauto.
+
intros ->.
destruct IH1 as (f & [ <- | ] & ?); auto.
*
exists (A&B); simpl; auto.
*
exists f; simpl; auto.
+
intros ->.
destruct IH1 as (f & [ <- | ] & ?); auto.
*
exists (A&B); simpl; auto.
*
exists f; simpl; auto.
+
intros ->.
destruct IH1 as (f & [ <- | [ <- | ] ] & ?); auto.
*
exists (A⊗B); simpl; auto.
*
exists (A⊗B); simpl; auto.
*
exists f; simpl; auto.
+
intros H.
app inv nil in H.
destruct IH1 as (f & [ <- | ] & ?); auto.
*
exists (A⅋B); simpl; auto.
*
exists f; simpl; split; auto.
rewrite in_app_iff; auto.
+
intros ->.
destruct IH1 as (f & [ <- | ] & ?); auto.
*
exists (A⊕B); simpl; auto.
*
exists f; simpl; auto.
+
exists ⟘; simpl; auto.
+
intros ->.
destruct IH1 as (f & ? & ?); auto.
exists f; simpl; auto.
+
exists 𝟘; simpl; auto.
+
intros ->.
destruct IH1 as (f & [ <- | ] & ?); auto.
*
exists (!A); simpl; auto.
*
exists f; simpl; auto.
+
destruct Δ; try discriminate; intros _ ; simpl in *.
destruct IH1 as (f & [ <- | ] & ?); auto.
*
exists (‽A); simpl; auto.
*
exists f; simpl; auto.
+
intros ->.
destruct IH1 as (f & ? & ?); auto.
*
exists f; simpl; auto.
+
intros ->.
destruct IH1 as (f & [ <- | [ <- | ] ] & ?); auto.
*
exists (!A); simpl; auto.
*
exists (!A); simpl; auto.
*
exists f; simpl; auto.
End Schellinx_observation.
Section cll_ill_soundness.
Tactic Notation "solve" "Forall" := repeat rewrite Forall_cons_inv in *; repeat rewrite Forall_app in *; simpl in *; tauto.
Let cll_ill_rec Γ Δ A : Γ ⊢c Δ -> Δ = A::∅ -> Forall from_ill (A::Γ) -> ⟪Γ⟫ ⊢i ⟨A⟩ \/ cll_has_bot_zero_neg A \/ exists f, In f Γ /\ cll_has_bot_zero_neg f.
Proof.
intros H; revert H A.
induction 1 as [ A (* ax *) | Γ Δ Γ' Δ' H1 H2 H3 IH3 (* perm *) | Γ Δ A H1 IH1 | Γ Δ A H1 IH1 (* negation *) | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ Δ A B H1 IH1 (* -o *) | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 H2 IH2 (* & *) | Γ A B Δ H1 IH1 | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 (* * *) | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ A B Δ H1 IH1 (* par *) | Γ A B Δ H1 IH1 H2 IH2 | Γ A B Δ H1 IH1 | Γ A B Δ H1 IH1 (* + *) | | (* bot, top *) | Γ Δ H1 IH1 | (* unit *) | | (* zero *) | Γ A Δ H1 IH1 | Γ A Δ H1 IH1 (* bang *) | Γ A Δ H1 IH1 | (* qmrk *) | Γ A Δ H1 IH1 | (* weak *) | Γ A Δ H1 IH1 | ]; (* cntr *) intros C HΔ HΓ.
+
inversion HΔ; left; simpl; constructor.
+
subst.
apply Permutation_sym, Permutation_length_1_inv in H2 as ->.
destruct (IH3 _ eq_refl) as [ H | [ | (f & H & ?) ] ]; auto.
*
rewrite Forall_cons_inv in *.
destruct HΓ as (? & HΓ); split; auto.
revert HΓ; apply Permutation_Forall, Permutation_sym; auto.
*
left; apply in_ill3_perm with (2 := H).
now apply Permutation_map.
*
do 2 right; exists f; split; auto.
revert H; now apply Permutation_in.
+
contradict HΓ; solve Forall.
+
inversion HΔ; subst; contradict HΓ; solve Forall.
+
app inv singleton in HΔ.
*
destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; auto.
-
solve Forall.
-
destruct (IH2 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; auto.
++
solve Forall.
++
left; simpl; rewrite map_app; constructor; auto.
++
do 2 right; exists (A⊸B); simpl; tauto.
++
do 2 right; exists f; split; auto; right; apply in_or_app; tauto.
-
do 2 right; exists (A⊸B); simpl; tauto.
-
do 2 right; exists f; split; auto; right; apply in_or_app; tauto.
*
apply Schellinx_observation in H2 as (f & [ <- | ] & ?).
-
do 2 right; exists (A⊸B); simpl; tauto.
-
do 2 right; exists f; split; auto; right; apply in_or_app; tauto.
+
inversion HΔ; subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
*
solve Forall.
*
left; constructor; auto.
*
do 2 right; exists f; auto.
+
subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
*
solve Forall.
*
left; apply in_ill3_with_l1; auto.
*
do 2 right; exists (A&B); simpl; tauto.
*
do 2 right; exists f; auto.
+
subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
*
solve Forall.
*
left; apply in_ill3_with_l2; auto.
*
do 2 right; exists (A&B); simpl; tauto.
*
do 2 right; exists f; auto.
+
inversion HΔ; subst; clear HΔ.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
*
solve Forall.
*
destruct (IH2 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
-
solve Forall.
-
left; simpl; constructor; auto.
-
do 2 right; exists f; simpl; tauto.
*
do 2 right; exists f; simpl; tauto.
+
subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | [ <- | ] ] & ?) ] ]; simpl; auto.
*
solve Forall.
*
left; constructor; auto.
*
do 2 right; exists (A⊗B); simpl; tauto.
*
do 2 right; exists (A⊗B); simpl; tauto.
*
do 2 right; exists f; auto.
+
inversion HΔ; subst.
app inv nil in H3.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
*
solve Forall.
*
destruct (IH2 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
-
solve Forall.
-
left; rewrite map_app; constructor; auto.
-
do 2 right; exists f; split; auto.
apply in_or_app; auto.
*
do 2 right; exists f; split; auto.
apply in_or_app; auto.
+
contradict HΓ; solve Forall.
+
inversion HΔ; subst; contradict HΓ; solve Forall.
+
subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
*
solve Forall.
*
destruct (IH2 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
-
solve Forall.
-
left; simpl; now constructor.
-
do 2 right; exists (A⊕B); simpl; tauto.
-
do 2 right; exists f; auto.
*
do 2 right; exists (A⊕B); simpl; tauto.
*
do 2 right; exists f; auto.
+
inversion HΔ; subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
*
solve Forall.
*
left; now apply in_ill3_plus_r1.
*
do 2 right; exists f; auto.
+
inversion HΔ; subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
*
solve Forall.
*
left; now apply in_ill3_plus_r2.
*
do 2 right; exists f; auto.
+
left; constructor.
+
inversion HΔ; subst; left; constructor.
+
subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
*
solve Forall.
*
left; now constructor.
*
do 2 right; exists f; auto.
+
inversion HΔ; subst; left; constructor.
+
discriminate.
+
inversion HΔ; subst; contradict HΓ; solve Forall.
+
subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
*
solve Forall.
*
left; now constructor.
*
do 2 right; exists (!A); simpl; auto.
*
do 2 right; exists f; auto.
+
destruct Δ; try discriminate.
inversion HΔ; subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
*
solve Forall.
*
left; rewrite cll_ill_lbang in *; now constructor.
*
do 2 right; exists f; auto.
+
destruct Δ as [ | D [ ] ]; try discriminate.
inversion HΔ; subst; contradict HΓ; solve Forall.
+
inversion HΔ; subst; contradict HΓ; solve Forall.
+
subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
*
solve Forall.
*
left; now constructor.
*
do 2 right; exists f; auto.
+
inversion HΔ; subst.
rewrite Forall_cons_inv in HΓ; simpl in HΓ; tauto.
+
subst.
destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | [ <- | ] ] & ?) ] ]; simpl; auto.
*
solve Forall.
*
left; now constructor.
*
do 2 right; exists (!A); simpl; auto.
*
do 2 right; exists (!A); simpl; auto.
*
do 2 right; exists f; auto.
+
inversion HΔ; subst; contradict HΓ; solve Forall.
End cll_ill_soundness.

Lemma cll_ill_soundness Γ A : ⟦Γ⟧ ⊢c [A]::∅ -> Γ ⊢i A \/ ill_has_bot A \/ exists f, In f Γ /\ ill_has_bot f.
Proof.
intros H.
apply cll_ill_rec with (2 := eq_refl) in H.
*
rewrite ill_cll_ill_list, ill_cll_ill, <- ill_cll_has_bot_eq in H.
destruct H as [ | [ | (f & G1 & G2) ] ]; auto.
do 2 right.
apply in_map_iff in G1.
destruct G1 as (g & <- & ?).
exists g; rewrite ill_cll_has_bot_eq; auto.
*
rewrite -> Forall_map with (f := ill_cll) (ll := A::Γ), Forall_forall.
intros; apply ill_cll_from_ill.
