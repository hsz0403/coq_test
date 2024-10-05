Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalChoice.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.RelationPairs_ext.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.UpwardsClosure.
Require Import Logic.SeparationLogic.Model.DownwardsClosure.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Coq.omega.Omega.
Section nat_algs.
Definition nat_leR: Relation nat := le.
Definition nat_geR: Relation nat := ge.
Instance po_nat_leR: PreOrder (@Krelation _ nat_leR) := Nat.le_preorder.
Instance po_nat_geR: PreOrder (@Krelation _ nat_geR).
Proof.
constructor.
+
hnf; intros; hnf; omega.
+
hnf; intros; hnf in *; omega.
Definition indexAlg: @SeparationAlgebra nat equiv_Join.
Proof.
constructor; intros.
-
inversion H; congruence.
-
inversion H; inversion H0; subst.
exists mxyz; split; constructor; auto.
Defined.
Instance IndexAlg_uSA: @UpwardsClosedSeparationAlgebra _ nat_geR equiv_Join.
Proof.
hnf; intros.
inversion H; subst.
exists n, n.
repeat split; auto.
Instance IndexAlg_increasing: @IncreasingSeparationAlgebra _ nat_geR equiv_Join.
Proof.
constructor; intro.
hnf; intros.
inversion H; subst.
hnf; reflexivity.
Instance IndexAlg_residual: @ResidualSeparationAlgebra _ nat_geR equiv_Join.
Proof.
constructor; intro.
exists n, n; split; constructor; reflexivity.
Instance IndexAlg_unital: @UnitalSeparationAlgebra _ nat_geR equiv_Join.
Proof.
apply <- (@incr_unital_iff_residual _ nat_geR _ equiv_Join).
+
apply IndexAlg_residual.
+
apply IndexAlg_increasing.
Inductive min_Join: nat -> nat -> nat -> Prop:= | min_j x y z: z <= x -> z <= y -> min_Join x y z.
Definition minAlg: @SeparationAlgebra nat min_Join.
Proof.
constructor; intros.
-
inversion H; subst; constructor; auto.
-
inversion H; inversion H0; subst.
exists (Min.min my mz); split; constructor.
+
apply Min.le_min_l.
+
apply Min.le_min_r.
+
transitivity mxy; auto.
+
apply Min.min_glb.
*
transitivity mxy; auto.
*
auto.
Instance minAlg_uSA: @UpwardsClosedSeparationAlgebra _ nat_geR min_Join.
Proof.
hnf; intros.
inversion H; subst.
exists m1, m2; split; constructor; first[ solve[transitivity m; auto] | reflexivity].
Instance minAlg_dSA: @DownwardsClosedSeparationAlgebra _ nat_geR min_Join.
Proof.
hnf; intros.
inversion H; subst.
exists m; split ; constructor.
-
transitivity m1; auto.
-
transitivity m2; auto.
Instance minAlg_increasing: @IncreasingSeparationAlgebra _ nat_geR min_Join.
Proof.
constructor; intro.
hnf; intros.
inversion H; subst; auto.
Instance minAlg_residual: @ResidualSeparationAlgebra _ nat_geR min_Join.
Proof.
constructor; intro.
exists n, n; split.
constructor; reflexivity.
reflexivity.
Instance minAlg_unital: @UnitalSeparationAlgebra _ nat_geR min_Join.
Proof.
apply incr_unital_iff_residual.
apply minAlg_increasing.
apply minAlg_residual.
Inductive sum_Join: nat -> nat -> nat -> Prop:= |sum_j x y z: x + y = z -> sum_Join x y z.
Definition sumAlg: @SeparationAlgebra _ sum_Join.
Proof.
constructor; intros.
-
inversion H; subst.
rewrite Nat.add_comm; constructor; auto.
-
inversion H; inversion H0; subst.
exists (my+mz); split; try constructor; simpl; omega.
Instance sumAlg_uSA: @UpwardsClosedSeparationAlgebra _ nat_geR sum_Join.
Proof.
hnf; intros.
simpl in H0.
inversion H; subst.
destruct (le_lt_dec n m1).
-
exists n, 0; split; constructor; simpl; hnf; try omega.
-
exists m1, (n - m1); split; constructor; simpl; hnf in *; try omega.
Instance sumAlg_dSA: @DownwardsClosedSeparationAlgebra _ nat_geR sum_Join.
Proof.
hnf; intros.
simpl in H0, H1.
inversion H; subst.
exists (n1 + n2); split; simpl; try constructor; hnf in *; try omega.
Instance sumAlg_unital: @UnitalSeparationAlgebra _ nat_geR sum_Join.
Proof.
constructor; intros.
-
exists 0; split.
+
exists n; split; simpl; try constructor; omega.
+
hnf; intros.
inversion H; subst; simpl; hnf; omega.
Instance sumAlg_residual: @ResidualSeparationAlgebra _ nat_geR sum_Join.
Proof.
constructor; intro.
exists 0, n; split.
constructor; omega.
hnf; omega.
Record natPlus: Type:= natp { nat_p:> nat; is_pos: 0 < nat_p}.
Inductive sump_Join: natPlus -> natPlus -> natPlus -> Prop:= |sump_j (x y z:natPlus): x + y = z -> sump_Join x y z.
Definition lep (n m:natPlus):= n <= m.
Definition natPlus_R: Relation natPlus:= lep.
Definition po_natPlus_R: PreOrder (@Krelation _ natPlus_R) := lep_preorder.
Definition sumpAlg: @SeparationAlgebra _ sump_Join.
Proof.
constructor; intros.
-
inversion H; subst.
rewrite Nat.add_comm in H0; constructor; auto.
-
inversion H; inversion H0; subst.
exists (natp (my+mz) ltac:(destruct my, mz; simpl in *; omega)) ; split; try constructor; simpl; omega.
Instance sumpAlg_uSA: @UpwardsClosedSeparationAlgebra _ natPlus_R sump_Join.
Proof.
hnf; intros.
simpl in H0.
inversion H; subst.
Abort.
Instance sumpAlg_dSA: @DownwardsClosedSeparationAlgebra _ natPlus_R sump_Join.
Proof.
hnf; intros.
simpl in H0, H1.
inversion H; subst.
unfold lep in *.
destruct m1, m2, m, n1, n2; simpl in *.
exists (natp (nat_p3 + nat_p4) ltac:(simpl in *; omega)); split; simpl; try constructor; try omega.
reflexivity.
unfold natPlus_R, lep in *; simpl.
rewrite <- H2.
unfold Krelation in *.
simpl in *.
omega.
Instance sumpAlg_residual: @ResidualSeparationAlgebra _ natPlus_R sump_Join.
Proof.
constructor; intro.
unfold residue.
Abort.
Definition suminvAlg: @SeparationAlgebra _ sum_Join.
Proof.
constructor; intros.
-
inversion H; subst.
rewrite Nat.add_comm; constructor; auto.
-
inversion H; inversion H0; subst.
exists (my+mz) ; split; try constructor; simpl; omega.
Instance suminvAlg_uSA: @UpwardsClosedSeparationAlgebra _ nat_leR sum_Join.
Proof.
hnf; intros.
simpl in H0.
inversion H; subst.
destruct (le_ge_dec m1 m2).
-
exists m1, (n- m1).
split; constructor; simpl; hnf in *; try omega.
-
exists (n-m2), m2.
split; constructor; simpl; hnf in *; try omega.
Instance suminvAlg_dSA: @DownwardsClosedSeparationAlgebra _ nat_leR sum_Join.
Proof.
hnf; intros.
simpl in H0, H1.
inversion H; subst.
exists (n1 + n2); split; simpl; try constructor; hnf in *; try omega.
Instance suminvAlg_increasing: @IncreasingSeparationAlgebra _ nat_leR sum_Join.
Proof.
constructor; intro.
hnf; intros.
inversion H; subst.
hnf.
omega.
Instance suminvAlg_residual: @ResidualSeparationAlgebra _ nat_leR sum_Join.
Proof.
constructor; intro.
exists 0, n; split.
constructor; omega.
reflexivity.
Instance suminvAlg_unital: @UnitalSeparationAlgebra _ nat_leR sum_Join.
Proof.
apply incr_unital_iff_residual.
apply suminvAlg_increasing.
apply suminvAlg_residual.
End nat_algs.
Require Import Coq.QArith.QArith.
Require Import Ring.
Section heaps.
Context (addr val: Type).
Definition Heap: Type := addr -> option val.
Instance Heap_Join: Join Heap := @fun_Join _ _ (@option_Join _ (trivial_Join)).
Instance Heap_SA: SeparationAlgebra Heap := @fun_SA _ _ _ (@option_SA _ _ (trivial_SA)).
Instance discHeap_R: Relation Heap := eq.
Instance po_discHeap_R: PreOrder Krelation := eq_preorder _.
Program Instance discHeap_ikiM: IdentityKripkeIntuitionisticModel Heap.
Instance discHeap_uSA: @UpwardsClosedSeparationAlgebra Heap discHeap_R Heap_Join.
Proof.
eapply ikiM_uSA.
Instance discHeap_dSA: @DownwardsClosedSeparationAlgebra Heap discHeap_R Heap_Join.
Proof.
eapply ikiM_dSA.
Instance discHeap_unital: @UnitalSeparationAlgebra Heap discHeap_R Heap_Join.
Proof.
constructor; intros.
-
exists (fun _ => None); split.
+
exists n; split.
*
hnf; intros.
unfold join.
destruct (n x); constructor.
*
hnf; intros.
reflexivity.
+
hnf; intros.
hnf; extensionality x.
specialize (H x).
inversion H; reflexivity.
Instance discHeap_residual: @ResidualSeparationAlgebra Heap discHeap_R Heap_Join.
Proof.
apply unital_is_residual; apply discHeap_unital.
Instance monHeap_R: Relation Heap := @pointwise_relation _ _ (@option01_relation _ eq).
Instance po_monHeap_R: PreOrder Krelation := @pointwise_preorder _ _ _ (@option01_preorder _ _ (eq_preorder _)).
Instance monHeap_uSA: @UpwardsClosedSeparationAlgebra Heap monHeap_R Heap_Join.
Proof.
apply fun_uSA.
apply option_ord_uSA.
apply (@ikiM_uSA val eq (eq_preorder _) (eq_ikiM)).
Definition monHeap_dSA: @DownwardsClosedSeparationAlgebra Heap monHeap_R Heap_Join.
Proof.
eapply fun_dSA.
eapply option_ord_dSA.
-
apply eq_preorder.
-
apply trivial_SA.
-
apply (@ikiM_dSA val eq (eq_preorder _) (eq_ikiM)).
-
apply trivial_incrSA.
Instance monHeap_increasing: @IncreasingSeparationAlgebra Heap monHeap_R Heap_Join.
Proof.
constructor; intros.
hnf; intros.
hnf; intros.
specialize (H a).
inversion H; constructor.
-
reflexivity.
-
inversion H3.
Instance monHeap_residual: @ResidualSeparationAlgebra Heap monHeap_R Heap_Join.
Proof.
constructor; intros.
exists (fun _ => None).
hnf; intros.
exists n; split.
-
hnf; intros x; destruct (n x); constructor.
-
reflexivity.
Instance monHeap_unital: @UnitalSeparationAlgebra Heap monHeap_R Heap_Join.
Proof.
apply incr_unital_iff_residual.
apply monHeap_increasing.
apply monHeap_residual.
End heaps.
Section heaps'.
Context (addr val: Type).
Definition Heap': Type := addr -> option val.
Instance Heap_Join': Join Heap' := @fun_Join _ _ (@option_Join _ (equiv_Join)).
Instance Heap_SA': SeparationAlgebra Heap' := @fun_SA _ _ _ (@option_SA _ _ (equiv_SA)).
Instance discHeap_R': Relation Heap' := eq.
Instance po_discHeap_R': PreOrder Krelation := eq_preorder _.
Program Instance discHeap_ikiM': IdentityKripkeIntuitionisticModel Heap'.
Instance discHeap_uSA': @UpwardsClosedSeparationAlgebra Heap' discHeap_R' Heap_Join'.
Proof.
eapply ikiM_uSA.
Instance discHeap_dSA': @DownwardsClosedSeparationAlgebra Heap' discHeap_R' Heap_Join'.
Proof.
eapply ikiM_dSA.
Instance discHeap_unital': @UnitalSeparationAlgebra Heap' discHeap_R' Heap_Join'.
Proof.
constructor; intros.
-
exists (fun _ => None); split.
+
exists n; split.
*
hnf; intros.
unfold join.
destruct (n x); constructor.
*
hnf; intros.
reflexivity.
+
hnf; intros.
hnf; extensionality x.
specialize (H x).
inversion H; reflexivity.
Instance discHeap_residual': @ResidualSeparationAlgebra Heap' discHeap_R' Heap_Join'.
Proof.
apply unital_is_residual; apply discHeap_unital'.
Instance monHeap_R': Relation Heap' := @pointwise_relation _ _ (@option01_relation _ eq).
Instance po_monHeap_R': PreOrder Krelation := @pointwise_preorder _ _ _ (@option01_preorder _ _ (eq_preorder _)).
Instance monHeap_uSA': @UpwardsClosedSeparationAlgebra Heap' monHeap_R' Heap_Join'.
Proof.
eapply fun_uSA.
eapply option_ord_uSA.
apply (@ikiM_uSA val eq (eq_preorder _) (eq_ikiM)).
Definition monHeap_dSA': @DownwardsClosedSeparationAlgebra Heap' monHeap_R' Heap_Join'.
Proof.
eapply fun_dSA.
eapply option_ord_dSA.
-
apply eq_preorder.
-
apply equiv_SA.
-
apply (@ikiM_dSA val eq (eq_preorder _) (eq_ikiM)).
-
apply equiv_incrSA.
Instance monHeap_increasing': @IncreasingSeparationAlgebra Heap' monHeap_R' Heap_Join'.
Proof.
constructor; intros.
hnf; intros.
hnf; intros.
specialize (H a).
inversion H; constructor.
-
reflexivity.
-
inversion H3.
subst; reflexivity.
Instance monHeap_residual': @ResidualSeparationAlgebra Heap' monHeap_R' Heap_Join'.
Proof.
constructor; intros.
exists (fun _ => None).
hnf; intros.
exists n; split.
-
hnf; intros x; destruct (n x); constructor.
-
reflexivity.
Instance monHeap_unital': @UnitalSeparationAlgebra Heap' monHeap_R' Heap_Join'.
Proof.
apply incr_unital_iff_residual.
apply monHeap_increasing'.
apply monHeap_residual'.
End heaps'.
Section typed_heaps.
Inductive htype:= |char |short1 |short2.
Inductive ht_ord: htype -> htype -> Prop := |htype_refl x: ht_ord x x |htype_sht1 : ht_ord char short1 |htype_sht2 : ht_ord char short2.
Instance ht_preorder: PreOrder ht_ord.
Proof.
constructor; hnf; intros.
-
constructor.
-
inversion H; inversion H0; subst; subst; try solve [constructor].
Notation THeap':= (nat -> option htype).
Definition THvalid (TH:THeap'):= forall n, TH n = Some short1 <-> TH (S n) = Some short2.
Record THeap: Type := { theap:> nat -> option htype; th_wf1: THvalid theap}.
Instance THeap_Join': Join THeap' := @fun_Join _ _ (@option_Join _ (trivial_Join)).
Inductive THeap_Join: Join THeap := | th_join (h1 h2 h3: THeap): THeap_Join' h1 h2 h3 -> THeap_Join h1 h2 h3.
Instance THeap_SA': @SeparationAlgebra _ THeap_Join':= @fun_SA _ _ _ (@option_SA _ _ (trivial_SA)).
Instance THeap_SA: @SeparationAlgebra THeap THeap_Join.
Proof.
constructor; intros.
-
inversion H; subst.
constructor.
apply join_comm; auto.
-
inversion H; inversion H0; subst.
pose ( join_assoc _ _ _ _ _ H1 H5) as HH.
destruct HH as [myz' [HH1 HH2]].
assert (forall n, myz' n = Some short1 <-> myz' (S n) = Some short2).
{
eapply (THeap_Join_valid HH1).
apply my.
apply mz.
}
exists (Build_THeap myz' H2); split; constructor; auto.
Inductive THeap_order': THeap' -> THeap' -> Prop:= | THeap_ord (h1 h2:THeap'): (forall (n:nat) (c:htype), h2 n = Some c -> exists (c':htype), h1 n = Some c' /\ ht_ord c' c) -> THeap_order' h2 h1.
Definition THeap_order (h1 h2: THeap): Prop:= THeap_order' h1 h2.
Instance THeap_preorder': PreOrder THeap_order'.
constructor.
-
hnf; intros.
constructor; intros.
exists c; split; auto; constructor.
-
hnf; intros.
inversion H; inversion H0; subst.
constructor; intros.
apply H1 in H2; destruct H2 as [c0 [HH1 HH2]].
apply H4 in HH1; destruct HH1 as [c' [HH3 HH4]].
exists c'; split; auto.
transitivity c0; auto.
Instance THeap_R': Relation THeap' := THeap_order'.
Instance po_THeap_R': PreOrder (@Krelation _ THeap_R').
Proof.
eapply THeap_preorder'.
Defined.
Instance THeap_R: Relation THeap := THeap_order.
Instance po_THeap_R: PreOrder (@Krelation _ THeap_R).
Proof.
eapply THeap_preorder.
Defined.
Instance THeap_uSA: @UpwardsClosedSeparationAlgebra THeap THeap_R THeap_Join.
Proof.
hnf; intros.
hnf in H0.
exists m1.
pose (m2':= (fun n => match m1 n with Some _ => None | _ => m n end)).
assert (THvalid m2').
Abort.
Instance THeap_dSA': @DownwardsClosedSeparationAlgebra _ THeap_R' THeap_Join'.
Proof.
hnf; intros.
inversion H0; inversion H1; subst.
exists (fun n => match n1 n with |Some x => Some x |_ => n2 n end); split.
-
hnf; intros.
destruct (n1 x) eqn:AA.
+
destruct (n2 x) eqn:BB.
*
specialize (H2 x); specialize (H5 x).
apply H2 in AA; destruct AA as [x' [AA1 AA2]].
apply H5 in BB; destruct BB as [x'' [BB1 BB2]].
specialize (H x).
rewrite AA1, BB1 in H.
inversion H; subst.
inversion H7.
*
constructor.
+
destruct (n2 x); constructor.
-
constructor; intros.
destruct (n1 n) eqn:n1n.
+
apply H2 in n1n; destruct n1n as [c' [HH1 HH2]].
exists c';split.
*
specialize (H n).
rewrite HH1 in H.
inversion H; subst; try reflexivity.
inversion H8.
*
inversion H3; subst; auto.
+
apply H5 in H3; destruct H3 as [c' [HH1 HH2]].
exists c';split.
*
specialize (H n).
rewrite HH1 in H.
inversion H; subst; try reflexivity.
inversion H7.
*
auto.
Instance THeap_dSA: @DownwardsClosedSeparationAlgebra THeap THeap_R THeap_Join.
Proof.
hnf; intros.
hnf in H0, H1.
inversion H; subst.
destruct (THeap_dSA' _ _ _ _ _ H2 H0 H1) as [n [HH1 HH2]].
assert (HH: THvalid n).
{
apply (THeap_Join_valid HH1); first [apply n1 | apply n2].
}
exists (Build_THeap n HH); split; auto; constructor; auto.
Instance THeap_increasingSA': @IncreasingSeparationAlgebra _ THeap_R' THeap_Join'.
Proof.
constructor; intros.
hnf; intros.
constructor; intros.
specialize (H n0).
rewrite H0 in H; inversion H; subst.
-
exists c; split; auto; reflexivity.
-
inversion H4.
Instance THeap_increasingSA: @IncreasingSeparationAlgebra _ THeap_R THeap_Join.
Proof.
constructor; intros.
hnf; intros.
simpl in *.
eapply THeap_increasingSA'; auto.
hnf in H; hnf ; intros.
inversion H; subst; auto.
Instance THeap_residualSA': @ResidualSeparationAlgebra _ THeap_R' THeap_Join'.
Proof.
constructor; intros.
exists (fun _ => None).
hnf; intros.
exists n; split; try reflexivity.
hnf; intros.
destruct (n x); constructor.
Instance THeap_residualSA: @ResidualSeparationAlgebra _ THeap_R THeap_Join.
Proof.
constructor; intros.
assert (THvalid (fun _ => None)).
{
constructor; intros HH; inversion HH.
}
exists (Build_THeap _ H).
exists n; split; try reflexivity.
constructor.
hnf; intros.
destruct (n x); constructor.
Instance THeap_UnitalSA': @UnitalSeparationAlgebra _ THeap_R' THeap_Join'.
Proof.
apply incr_unital_iff_residual.
apply THeap_increasingSA'.
apply THeap_residualSA'.
Instance THeap_UnitalSA: @UnitalSeparationAlgebra _ THeap_R THeap_Join.
Proof.
apply incr_unital_iff_residual.
apply THeap_increasingSA.
apply THeap_residualSA.
End typed_heaps.
Section step_index.
Definition StepIndex_R (worlds: Type) {R: Relation worlds}: Relation (nat * worlds) := @RelProd _ _ nat_geR R.
Definition po_StepIndex_R (worlds: Type) {R: Relation worlds} {po_R: PreOrder (@Krelation _ R)}: PreOrder (@Krelation _ (StepIndex_R worlds)):= @RelProd_Preorder _ _ _ _ po_nat_geR po_R.
Definition StepIndex_Join (worlds: Type) {J: Join worlds}: Join (nat * worlds) := @prod_Join _ _ equiv_Join J.
Definition StepIndex_SA (worlds: Type) {J: Join worlds} {SA: SeparationAlgebra worlds}: @SeparationAlgebra (nat * worlds) (StepIndex_Join worlds) := @prod_SA _ _ _ _ equiv_SA SA.
Definition StepIndex_uSA (worlds: Type) {R: Relation worlds} {J: Join worlds} {uSA: UpwardsClosedSeparationAlgebra worlds}: @UpwardsClosedSeparationAlgebra (nat * worlds) (StepIndex_R worlds) (StepIndex_Join worlds) := @prod_uSA _ _ _ _ _ _ (@identity_uSA _ nat_geR) uSA.
Definition StepIndex_Increasing (worlds: Type) {R: Relation worlds} {J: Join worlds} {incrSA: IncreasingSeparationAlgebra worlds}: @IncreasingSeparationAlgebra (nat * worlds) (StepIndex_R worlds) (StepIndex_Join worlds) := @prod_incrSA _ _ _ _ _ _ IndexAlg_increasing incrSA.
Definition StepIndex_Unital (worlds: Type) {R: Relation worlds} {J: Join worlds} {USA: UnitalSeparationAlgebra worlds}: @UnitalSeparationAlgebra (nat * worlds) (StepIndex_R worlds) (StepIndex_Join worlds) := @prod_unitalSA _ _ _ _ _ _ IndexAlg_unital USA.
Definition StepIndex_Residual (worlds: Type) {R: Relation worlds} {J: Join worlds} {rSA: ResidualSeparationAlgebra worlds}: @ResidualSeparationAlgebra (nat * worlds) (StepIndex_R worlds) (StepIndex_Join worlds) := @prod_residualSA _ _ _ _ _ _ IndexAlg_residual rSA.
Context (addr val: Type).
Notation heap:= (Heap addr val).
Instance heap_jn: Join heap:= (Heap_Join addr val).
Instance SIheap_Join: Join (nat * heap) := StepIndex_Join heap.
Definition monSIheap_R := @StepIndex_R heap (monHeap_R addr val).
Definition po_monSIheap_R := @po_StepIndex_R heap _ (po_monHeap_R addr val).
Instance monSIheap_uSA: @UpwardsClosedSeparationAlgebra _ monSIheap_R SIheap_Join.
Proof.
eapply StepIndex_uSA.
apply monHeap_uSA.
Instance monSIheap_increasing: @IncreasingSeparationAlgebra _ monSIheap_R SIheap_Join.
Proof.
eapply StepIndex_Increasing.
apply monHeap_increasing.
Instance monSIheap_unital: @UnitalSeparationAlgebra _ monSIheap_R SIheap_Join.
Proof.
eapply StepIndex_Unital.
apply monHeap_unital.
Instance monSIheap_residual: @ResidualSeparationAlgebra _ monSIheap_R SIheap_Join.
Proof.
eapply StepIndex_Residual.
apply monHeap_residual.
Definition discSIheap_R:= @StepIndex_R heap (discHeap_R addr val).
Definition po_discSIheap_R:= @po_StepIndex_R heap _ (po_discHeap_R addr val).
Instance discSIheap_uSA: @UpwardsClosedSeparationAlgebra _ discSIheap_R SIheap_Join.
Proof.
eapply StepIndex_uSA.
apply discHeap_uSA.
Instance discSIheap_unital: @UnitalSeparationAlgebra _ discSIheap_R SIheap_Join.
Proof.
eapply StepIndex_Unital.
apply discHeap_unital.
Instance discSIheap_residual: @ResidualSeparationAlgebra _ discSIheap_R SIheap_Join.
Proof.
eapply StepIndex_Residual.
apply discHeap_residual.
End step_index.
Section Prop_alg.
Instance Prop_Join: Join Prop := fun P Q R => (P \/ Q <-> R) /\ (P -> Q -> False).
Instance discProp_R: Relation Prop := fun P Q => P <-> Q.
Instance Prop_SA: SeparationAlgebra Prop.
Proof.
constructor.
+
intros.
hnf in *; tauto.
+
intros.
exists (my \/ mz).
split; hnf in *; tauto.
Instance po_discProp_R: PreOrder Krelation.
Proof.
constructor; constructor; hnf in *; tauto.
Instance discProp_ikiM: IdentityKripkeIntuitionisticModel Prop.
Proof.
constructor.
intros.
apply prop_ext; auto.
Instance discProp_uSA: @UpwardsClosedSeparationAlgebra Prop discProp_R Prop_Join.
Proof.
eapply ikiM_uSA.
Instance discProp_dSA: @DownwardsClosedSeparationAlgebra Prop discProp_R Prop_Join.
Proof.
eapply ikiM_dSA.
Instance discProp_unitSA: @UnitalSeparationAlgebra Prop discProp_R Prop_Join.
Proof.
constructor.
intros.
exists False.
split.
+
hnf.
exists n; split; hnf; tauto.
+
hnf.
intros.
hnf in *; tauto.
End Prop_alg.
Section pred_alg.
Context (A : Type).
Definition Pred: Type := A -> Prop.
Instance Pred_Join: Join Pred := @fun_Join _ _ Prop_Join.
Instance Pred_SA: SeparationAlgebra Pred := @fun_SA _ _ _ Prop_SA.
Instance discPred_R: Relation Pred := pointwise_relation _ discProp_R.
Instance po_discPred_R: PreOrder Krelation := pointwise_preorder _ _ po_discProp_R.
Instance discPred_uSA: @UpwardsClosedSeparationAlgebra Pred discPred_R Pred_Join := fun_uSA _ _ discProp_uSA.
Instance discPred_dSA: @DownwardsClosedSeparationAlgebra Pred discPred_R Pred_Join := fun_dSA _ _ discProp_dSA.
Instance discPred_unital: @UnitalSeparationAlgebra Pred discPred_R Pred_Join := fun_unitSA _ _ discProp_unitSA.
End pred_alg.

Instance monHeap_unital: @UnitalSeparationAlgebra Heap monHeap_R Heap_Join.
Proof.
apply incr_unital_iff_residual.
apply monHeap_increasing.
apply monHeap_residual.
