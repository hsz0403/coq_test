Require Import List Permutation Arith Lia.
From Undecidability.MinskyMachines Require Import ndMM2.
From Undecidability.ILL Require Import IMSELL imsell.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec.
From Undecidability.Synthetic Require Import Definitions ReducibilityFacts.
Set Implicit Arguments.
Local Infix "~p" := (@Permutation _) (at level 70).
Local Notation "X ⊆ Y" := (forall a, X a -> Y a : Prop) (at level 70).
Local Infix "∊" := In (at level 70).
Local Reserved Notation "'⟦' A '⟧'" (at level 1, format "⟦ A ⟧").
Local Fact pair_plus x1 y1 x2 y2 : vec_plus (x1##y1##vec_nil) (x2##y2##vec_nil) = (x1+x2)##(y1+y2)##vec_nil.
Proof.
reflexivity.
Local Tactic Notation "pair" "split" hyp(v) "as" ident(x) ident(y) := vec split v with x; vec split v with y; vec nil v; clear v.
Local Tactic Notation "intro" "pair" "as" ident(x) ident (y) := let v := fresh in intro v; pair split v as x y.
Local Notation "⦳" := vec_zero.
Local Notation ø := vec_nil.
Local Infix "≤" := (@IMSELL_le _) (at level 70).
Local Notation "u ≰ v" := (~ u ≤ v) (at level 70).
Local Notation U := (@IMSELL_U _).
Section ndmm2_imsell.
Variable (sig : IMSELL_sig) (a b i : sig).
Notation "∞" := i.
Notation bang_le := (IMSELL_le sig).
Hypothesis (Hai : a ≤ ∞) (Hbi : b ≤ ∞) (Hab : a ≰ b) (Hba : b ≰ a) (Ha : ~ U a) (Hb : ~ U b) (Hi : U ∞).
Implicit Type u v w : sig.
Local Definition bang_le_refl : forall u, u ≤ u := IMSELL_refl _.
Local Definition bang_le_trans : forall u v w, u ≤ v -> v ≤ w -> u ≤ w := IMSELL_trans _.
Local Definition bang_U_clos : forall u v, U u -> u ≤ v -> U v := IMSELL_clos _.
Hint Resolve Hai Hbi Ha Hb Hi Hab Hba bang_le_refl bang_U_clos : core.
Notation "£ A" := (@imsell_var _ _ A) (at level 1).
Notation "‼ l" := (@imsell_lban nat sig l).
Notation "‼∞" := (map (fun A => ![∞]A)).
Local Definition formA : imsell_form nat sig := ![a](£0).
Local Definition formB : imsell_form nat sig := ![b](£1).
Local Definition var2pc p : imsell_form nat sig := £ (2+p).
Notation α := formA.
Notation β := formB.
Notation "⌊ p ⌋" := (var2pc p) (format "⌊ p ⌋").
Local Definition bool2form (x : bool) := if x then α else β.
Local Definition bool2bang_op (x : bool) := if x then b else a.
Notation STOPₙ := (@ndmm2_stop _).
Notation INCₙ := (@ndmm2_inc _).
Notation DECₙ := (@ndmm2_dec _).
Notation ZEROₙ := (@ndmm2_zero _).
Definition ndmm2_imsell_form c := match c with | STOPₙ p => (⌊p⌋ ⊸ ⌊p⌋) ⊸ ⌊p⌋ | INCₙ x p q => (bool2form x ⊸ ⌊q⌋) ⊸ ⌊p⌋ | DECₙ x p q => bool2form x ⊸ ⌊q⌋ ⊸ ⌊p⌋ | ZEROₙ x p q => (![bool2bang_op x]⌊q⌋) ⊸ ⌊p⌋ end.
Notation "⟬ c ⟭" := (ndmm2_imsell_form c) (at level 1, format "⟬ c ⟭").
Definition ndmm2_imsell_ctx Σ x y := ‼∞ (map (fun c => ⟬c⟭) Σ) ++ repeat α x ++ repeat β y.
Notation "⟬ Σ , x , y ⟭" := (ndmm2_imsell_ctx Σ x y) (at level 1, format "⟬ Σ , x , y ⟭").
Fact ndmm2_imsell_eq1 Σ : map (fun c => ![∞]⟬c⟭) Σ = ‼(map (fun c => (∞,⟬c⟭)) Σ).
Proof.
unfold imsell_lban; rewrite map_map; auto.
Fact ndmm2_imsell_eq2 Σ x y : ⟬Σ,x,y⟭ = ‼(map (fun c => (∞,⟬c⟭)) Σ ++ repeat (a,£0) x ++ repeat (b,£1) y).
Proof.
unfold ndmm2_imsell_ctx.
rewrite map_map, ndmm2_imsell_eq1.
unfold imsell_lban; rewrite !map_app, !map_map; f_equal.
induction x; simpl; f_equal; auto.
induction y; simpl; f_equal; auto.
Fact ndmm2_imsell_perm1 Σ x y : ⟬Σ,1+x,y⟭ ~p α::⟬Σ,x,y⟭ .
Proof.
unfold ndmm2_imsell_ctx.
apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
rewrite !app_ass; apply Permutation_app; auto.
simpl; apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
now rewrite app_ass.
Fact ndmm2_imsell_perm2 Σ x y : ⟬Σ,x,1+y⟭ ~p β::⟬Σ,x,y⟭ .
Proof.
unfold ndmm2_imsell_ctx.
apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
rewrite !app_ass; repeat apply Permutation_app; auto.
simpl; apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _); auto.
Notation "Γ ⊢ A" := (S_imsell bang_le U Γ A) (at level 70).
Notation "Σ //ₙ a ⊕ b ⊦ p" := (ndmm2_accept Σ a b p) (at level 70, no associativity).
Hint Resolve ndmm2_imsell_perm1 ndmm2_imsell_perm2 in_imsell_ax : core.
Variable Σ : list (ndmm2_instr nat).
Let sem p (w : vec nat 2) := let x := vec_head w in let y := vec_head (vec_tail w) in match p with | 0 => x = 1 /\ y = 0 | 1 => x = 0 /\ y = 1 | S (S i) => Σ //ₙ x ⊕ y ⊦ i end.
Local Fact sem_0 x y : sem 0 (x##y##ø) <-> x = 1 /\ y = 0.
Proof.
simpl; tauto.
Local Fact sem_1 x y : sem 1 (x##y##ø) <-> x = 0 /\ y = 1.
Proof.
simpl; tauto.
Local Fact sem_2 p x y : sem (2+p) (x##y##ø) <-> Σ //ₙ x ⊕ y ⊦ p.
Proof.
simpl; tauto.
Let K m (w : vec nat 2) := let x := vec_head w in let y := vec_head (vec_tail w) in (a ≤ m -> y = 0) /\ (b ≤ m -> x = 0) /\ (U m -> x = 0 /\ y = 0).
Infix "⊛" := imsell_tps_mult (at level 65, right associativity).
Infix "-⊛" := imsell_tps_imp (at level 65, right associativity).
Notation "⟦ A ⟧" := (imsell_tps sem K A).
Notation "⟪ Γ ⟫" := (imsell_tps_list sem K Γ).
Local Fact HK1 p q : p ≤ q -> K q ⊆ K p.
Proof.
intros Hpq; intro pair as x y.
unfold K; simpl; intros (H1 & H2 & H3); msplit 2; intros H.
+
apply H1, bang_le_trans with (2 := Hpq); auto.
+
apply H2, bang_le_trans with (2 := Hpq); auto.
+
apply H3, bang_U_clos with (2 := Hpq); auto.
Local Fact HK2 : forall m, K m ⦳.
Proof.
intros; split; auto.
Local Fact HK3 m : K m ⊛ K m ⊆ K m.
Proof.
intro pair as x y.
intros (p & q & H); revert p q H.
intro pair as x1 y1; intro pair as x2 y2; simpl.
rewrite pair_plus; unfold K; simpl.
intros (H1 & (H2 & H3 & H6) & H4 & H5 & H7).
inversion H1; subst x y; clear H1.
msplit 2; intros.
+
rewrite H2, H4; auto.
+
rewrite H3, H5; auto.
+
destruct H6; subst; auto.
Local Fact HK4 u : U u -> forall x, K u x -> x = ⦳.
Proof.
intros Hu; intro pair as x y; unfold K; simpl.
intros (_ & _ & H); destruct H; subst; auto.
Local Fact HKa x y : K a (x##y##vec_nil) <-> y = 0.
Proof.
split; unfold K; simpl.
+
intros []; auto.
+
intros ->; msplit 2; auto; intros; tauto.
Local Fact HKb x y : K b (x##y##vec_nil) <-> x = 0.
Proof.
split; unfold K; simpl.
+
intros (? & ? & ?); auto.
+
intros ->; msplit 2; auto; tauto.
Local Fact HKi : forall x, K ∞ x -> x = ⦳.
Proof.
intro pair as x y; unfold K; simpl.
intros (H1 & H2 & ?); rewrite H1, H2; auto.
Local Lemma sem_Σ c : c ∊ Σ -> ⟦⟬ c⟭⟧ ⦳.
Proof.
intros H.
destruct c as [ p | [] p q | [] p q | [] p q ]; simpl; apply imsell_tps_imp_zero; intro pair as x y; simpl; intros H1.
+
specialize (H1 ⦳); rewrite vec_zero_plus in H1.
apply H1; constructor; auto.
+
constructor 2 with (1 := H).
apply (H1 (1##0##vec_nil)).
simpl; rewrite HKa; auto.
+
constructor 3 with (1 := H).
apply (H1 (0##1##vec_nil)); auto.
simpl; rewrite HKb; auto.
+
destruct H1 as ((-> & ->) & _); simpl.
intro pair as x y; simpl; rewrite (plus_comm x), (plus_comm y).
constructor 4 with q; auto.
+
destruct H1 as ((-> & ->) & _); simpl.
intro pair as x y; simpl; rewrite (plus_comm x), (plus_comm y).
constructor 5 with q; auto.
+
rewrite HKb in H1.
destruct H1 as (H1 & ->).
constructor 6 with q; auto.
+
rewrite HKa in H1.
destruct H1 as (H1 & ->).
constructor 7 with q; auto.
Hint Resolve HK1 HK2 HK3 HK4 HKa HKb HKi sem_Σ : core.
Local Fact sem_Σ_zero : ⟪map (fun c => ![∞]⟬ c⟭) Σ⟫ ⦳.
Proof.
apply imsell_tps_list_zero.
intros A; rewrite in_map_iff.
intros (c & <- & Hc); simpl; auto.
Hint Resolve ndmm2_imsell_sound ndmm2_imsell_complete : core.
End ndmm2_imsell.

Theorem conditional_reduction (S : IMSELL_sig) : (exists a b i : S, a ≤ i /\ b ≤ i /\ a ≰ b /\ b ≰ a /\ ~ U a /\ ~ U b /\ U i) -> @ndMM2_ACCEPT nat ⪯ @IMSELL_cf_PROVABILITY S.
Proof.
intros (a & b & i & ?).
apply reduces_dependent; exists.
intros (Σ & u & x & y).
exists (ndmm2_imsell_ctx _ a b i Σ x y, imsell_var _ (2+u)).
apply ndmm2_imsell_correct; simpl; tauto.
