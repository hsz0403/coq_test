Require Import Equations.Equations.
Require Import Lia Arith.
Require Import Undecidability.PCP.PCP.
From Undecidability Require Import FOLP.FOLFS.
Require Import Undecidability.Shared.ListAutomation.
Import ListAutomationNotations.
Derive Signature for le.
Local Notation "| s |" := (length s) (at level 100).
Definition bstring n := { s : string bool | | s | <= n}.
Definition bnil n : bstring n.
Proof.
exists nil.
cbn.
lia.
Defined.
Definition bcons n (b : bool) : bstring n -> bstring (S n).
Proof.
intros [s H].
exists (b::s).
cbn.
lia.
Defined.
Definition bstring_step n (L : list (bstring n)) := [bnil (S n)] ++ map (bcons true) L ++ map (bcons false) L.
Definition bcast n s (H : |s| <= n) : bstring n := exist _ _ H.
Inductive what := pred | func.
Definition make_sig (T : what -> nat -> Type) : Signature := {| Funcs := {n & T func n} ; fun_ar := @projT1 _ _ ; Preds := {n & T pred n} ; pred_ar := @projT1 _ _ |}.
Inductive finsat_sig' : what -> nat -> Type := | f : bool -> finsat_sig' func 1 | e : finsat_sig' func 0 | dum : finsat_sig' func 0 | P : finsat_sig' pred 2 | less : finsat_sig' pred 2 | equiv : finsat_sig' pred 2.
Instance finsat_sig : Signature := make_sig finsat_sig'.
Definition i_f domain {I : interp domain} : bool -> domain -> domain := fun b x => (FullTarski.i_f (f := existT _ 1 (f b))) (Vector.cons x Vector.nil).
Definition i_e domain {I : interp domain} : domain := (FullTarski.i_f (f := existT _ 0 e)) Vector.nil.
Definition i_P domain {I : interp domain} : domain -> domain -> Prop := fun x y => (FullTarski.i_P (P := existT _ 2 P)) (Vector.cons x (Vector.cons y Vector.nil)).
Notation i_equiv x y := ((FullTarski.i_P (P := existT _ 2 equiv)) (Vector.cons x (Vector.cons y Vector.nil))).
Fixpoint iprep domain {I : interp domain} (x : list bool) (y : domain) := match x with | nil => y | b::x => i_f b (iprep x y) end.
Definition ienc domain {I : interp domain} (x : list bool) := iprep x i_e.
Local Definition BSRS := list (card bool).
Local Notation "x / y" := (x, y).
Section FIB.
Variable R : BSRS.
Definition obstring n := option (bstring n).
Notation obcast H := (Some (bcast H)).
Definition ccons n b (s : obstring n) : obstring n := match s with | Some (exist _ s _) => match (le_dec (|b::s|) n) with | left H => obcast H | right _ => None end | None => None end.
Definition cdrv n (s t : obstring n) := match s, t with | Some (exist _ s _), Some (exist _ t _) => derivable R s t | _, _ => False end.
Definition sub n (x y : obstring n) := match x, y with | Some (exist _ s _), Some (exist _ t _) => s <> t /\ exists s', t = s'++s | _, _ => False end.
Global Instance FIB n : interp (obstring n).
Proof.
split.
-
intros [k H]; cbn.
inversion H; subst.
+
intros v.
exact (ccons H0 (Vector.hd v)).
+
intros _.
exact (Some (bnil n)).
+
intros _.
exact None.
-
intros [k H]; cbn.
inversion H; subst.
+
intros v.
exact (cdrv (Vector.hd v) (Vector.hd (Vector.tl v))).
+
intros v.
exact (sub (Vector.hd v) (Vector.hd (Vector.tl v))).
+
intros v.
exact (eq (Vector.hd v) (Vector.hd (Vector.tl v))).
Defined.
Definition obembed n (s : obstring n) : obstring (S n) := match s with | Some (exist _ s H) => Some (exist _ s (le_S _ _ H)) | None => None end.
Section Ax.
Variable n : nat.
Implicit Type x y : obstring n.
End Ax.
End FIB.
Section Conv.
Variable R : BSRS.
Variable D : Type.
Hypothesis HD : listable D.
Variable I : interp D.
Notation sub x y := ((FullTarski.i_P (P := existT _ 2 less)) (Vector.cons x (Vector.cons y Vector.nil))).
Notation dum := ((FullTarski.i_f (f := existT _ 0 dum)) Vector.nil).
Hypothesis HP : forall x y, i_P x y -> x <> dum /\ y <> dum.
Hypothesis HS1 : forall x, ~ sub x x.
Hypothesis HS2 : forall x y z, sub x y -> sub y z -> sub x z.
Hypothesis HF1 : forall b x, i_f b x <> i_e.
Hypothesis HF2 : forall b1 b2 x y, i_f b1 x <> dum -> i_f b1 x = i_f b2 y -> x = y /\ b1 = b2.
Hypothesis HF3 : forall b x, i_f b x <> dum -> x <> dum.
Hypothesis HI : forall x y, i_P x y -> (exists s t, s/t el R /\ x = ienc s /\ y = ienc t) \/ (exists s t u v, s/t el R /\ x = iprep s u /\ y = iprep t v /\ i_P u v /\ ((sub u x /\ v = y) \/ (sub v y /\ u = x) \/ (sub u x /\ sub v y))).
Definition sub' L x y := sub x y /\ x el L.
Inductive psub : (D * D) -> (D * D) -> Prop := | psub1 x u : sub u x -> forall y, psub (u,y) (x,y) | psub2 y u : sub u y -> forall x, psub (x,u) (x,y) | psub3 x y u v : sub u x -> sub v y -> psub (u,v) (x,y).
End Conv.
Definition finsat phi := exists D (I : interp D) rho, listable D /\ (forall x y, i_equiv x y <-> eq x y) /\ rho ⊨ phi.
Section Reduction.
Notation "# x" := (var_term x) (at level 2).
Definition t_f b x := Func (existT _ 1 (f b)) (Vector.cons x Vector.nil).
Definition t_e := Func (existT _ 0 e) Vector.nil.
Definition t_dum := Func (existT _ 0 dum) Vector.nil.
Definition f_P x y := Pred (existT _ 2 P) (Vector.cons x (Vector.cons y Vector.nil)).
Notation "x ≡ y" := (Pred (existT _ 2 equiv) (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "x ≢ y" := (¬ (x ≡ y)) (at level 20).
Notation "x ≺ y" := (Pred (existT _ 2 less) (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Fixpoint tprep (x : list bool) (y : term) := match x with | nil => y | b::x => t_f b (tprep x y) end.
Definition tenc (x : list bool) := tprep x t_e.
Definition ax_P := ∀ ∀ f_P #1 #0 --> (#1 ≢ t_dum) ∧ (#0 ≢ t_dum).
Definition ax_S1 := ∀ ¬ (#0 ≺ #0).
Definition ax_S2 := ∀ ∀ ∀ #2 ≺ #1 --> #1 ≺ #0 --> #2 ≺ #0.
Definition ax_HF1_true := ∀ t_f true #0 ≢ t_e.
Definition ax_HF1_false := ∀ t_f false #0 ≢ t_e.
Definition ax_HF2_true := ∀ ∀ t_f true #1 ≢ t_dum --> t_f true #1 ≡ t_f true #0 --> #1 ≡ #0.
Definition ax_HF2_false := ∀ ∀ t_f false #1 ≢ t_dum --> t_f false #1 ≡ t_f false #0 --> #1 ≡ #0.
Definition ax_HF2 := ∀ ∀ t_f true #1 ≡ t_f false #0 --> (t_f true #1 ≡ t_dum ∧ t_f false #0 ≡ t_dum).
Definition ax_HF3_true := ∀ t_f true #0 ≢ t_dum --> #0 ≢ t_dum.
Definition ax_HF3_false := ∀ t_f false #0 ≢ t_dum --> #0 ≢ t_dum.
Definition ax_HI' c := (#1 ≡ tenc (fst c) ∧ #0 ≡ tenc (snd c)) ∨ (∃ ∃ #3 ≡ tprep (fst c) #1 ∧ #2 ≡ tprep (snd c) #0 ∧ f_P #1 #0 ∧ ((#1 ≺ #3 ∧ #0 ≡ #2) ∨ (#0 ≺ #2 ∧ #1 ≡ #3) ∨ (#1 ≺ #3 ∧ #0 ≺ #2))).
Definition ax_HI (R : BSRS) := ∀ ∀ f_P #1 #0 --> list_or (map ax_HI' R).
Definition finsat_formula (R : BSRS) := ax_P ∧ ax_S1 ∧ ax_S2 ∧ ax_HF1_true ∧ ax_HF1_false ∧ ax_HF2_true ∧ ax_HF2_false ∧ ax_HF2 ∧ ax_HF3_true ∧ ax_HF3_false ∧ ax_HI R ∧ ∃ f_P #0 #0.
End Reduction.

Lemma le_irrel' n : forall H : n <= n, H = le_n n.
Proof.
induction n; depelim H.
-
reflexivity.
-
assert (H = eq_refl) as -> by apply Eqdep_dec.UIP_refl_nat.
cbn in H1.
assumption.
-
exfalso.
Admitted.

Lemma string_nil (s : string bool) : |s| <= 0 <-> s = nil.
Proof.
destruct s; cbn.
-
split; trivial; lia.
-
split; try congruence.
intros H.
Admitted.

Definition bnil n : bstring n.
Proof.
exists nil.
cbn.
Admitted.

Definition bcons n (b : bool) : bstring n -> bstring (S n).
Proof.
intros [s H].
exists (b::s).
cbn.
Admitted.

Lemma bstring_eq n (s t : bstring n) : proj1_sig s = proj1_sig t <-> s = t.
Proof.
split; try now intros ->.
destruct s as [s H1], t as [t H2]; cbn.
intros ->.
Admitted.

Lemma bstring_eq' n (s t : bstring n) : proj1_sig s = proj1_sig t -> s = t.
Proof.
Admitted.

Lemma listable_bstring n : listable (bstring n).
Proof.
induction n.
-
exists [bnil 0].
intros [s H].
assert (s = nil) as -> by now apply string_nil.
left.
now apply bstring_eq.
-
destruct IHn as [L HL].
exists (bstring_step L).
intros [ [|[] s] H]; apply in_app_iff; cbn in H.
+
left.
left.
now apply bstring_eq.
+
right.
apply in_app_iff.
left.
apply in_map_iff.
assert (H' : |s| <= n) by lia.
exists (bcast H').
split; trivial.
now apply bstring_eq.
+
right.
apply in_app_iff.
right.
apply in_map_iff.
assert (H' : |s| <= n) by lia.
exists (bcast H').
split; trivial.
Admitted.

Lemma listable_obstring n : listable (obstring n).
Proof.
destruct (listable_bstring n) as [L HL].
exists (None :: map Some L).
intros [x|].
-
right.
apply in_map, HL.
-
cbn.
Admitted.

Lemma app_bound n (s t : string bool) : |t| <= n -> |s++t| <= n + |s|.
Proof.
intros H.
rewrite app_length.
Admitted.

Lemma obstring_iprep n x u (HX : |x++u| <= n) (HU : |u| <= n) : iprep x (obcast HU) = obcast HX.
Proof.
induction x; cbn.
-
f_equal.
now apply bstring_eq.
-
assert (H : |x++u| <= n).
{
rewrite app_length in *.
cbn in HX.
lia.
}
rewrite (IHx H).
unfold ccons, bcast at 1.
destruct le_dec.
+
f_equal.
now apply bstring_eq.
+
exfalso.
cbn in *.
rewrite app_length in *.
Admitted.

Lemma obstring_ienc n s (H : |s| <= n) : ienc s = obcast H.
Proof.
unfold ienc.
cbn.
setoid_rewrite obstring_iprep.
f_equal.
apply bstring_eq, app_nil_r.
Unshelve.
rewrite app_length.
cbn.
Admitted.

Lemma obstring_ienc' n s (H : ~ |s| <= n) : @ienc _ (FIB n) s = None.
Proof.
induction s; cbn in *; try lia.
change (@ccons n a (ienc s) = None).
destruct (le_dec (|s|) n) as [H'|H'].
-
setoid_rewrite (obstring_ienc H').
cbn.
destruct le_dec; tauto.
-
Admitted.

Lemma crdv_iff n (x y : obstring n) : i_P x y <-> exists s t, derivable R s t /\ x = ienc s /\ y = ienc t /\ |s| <= n /\ |t| <= n.
Proof.
destruct x as [ [x HX]|], y as [ [y HY]|]; split; cbn; auto.
{
intros H.
exists x, y.
repeat setoid_rewrite obstring_ienc.
now repeat split.
}
all: intros (s&t&H1&H2&H3&H4&H5).
all: try unshelve setoid_rewrite obstring_ienc in H2; try unshelve setoid_rewrite obstring_ienc in H3; auto.
all: try discriminate.
depelim H2.
depelim H3.
Admitted.

Lemma cdrv_mon n (s t : obstring n) : cdrv s t -> @cdrv (S n) (obembed s) (obembed t).
Proof.
Admitted.

Lemma cdrv_mon' n s t : @cdrv n (ienc s) (ienc t) -> @cdrv (S n) (ienc s) (ienc t).
Proof.
destruct (le_dec (|s|) n) as [H|H], (le_dec (|t|) n) as [H'|H'].
-
repeat unshelve setoid_rewrite obstring_ienc; trivial; lia.
-
setoid_rewrite (obstring_ienc H).
setoid_rewrite (obstring_ienc' H').
cbn.
tauto.
-
rewrite (obstring_ienc' H).
cbn.
tauto.
-
rewrite (obstring_ienc' H).
cbn.
Admitted.

Lemma drv_cdrv s t : derivable R s t <-> @cdrv (max (|s|) (|t|)) (ienc s) (ienc t).
Proof.
Admitted.

Lemma drv_cdrv' s : derivable R s s <-> @cdrv (|s|) (ienc s) (ienc s).
Proof.
Admitted.

Lemma BPCP_P : dPCPb R <-> exists n x, @i_P _ (FIB n) x x.
Proof.
split.
-
intros [s H].
exists (|s|), (ienc s).
cbn.
now apply drv_cdrv'.
-
intros [n[ [ [s H]|] H'] ].
+
cbn in H'.
now exists s.
+
Admitted.

Lemma app_eq_nil' (s t : string bool) : s = t++s -> t = nil.
Proof.
destruct t; trivial.
intros H.
exfalso.
assert (H' : |s| = |(b :: t) ++ s|) by now rewrite H at 1.
cbn in H'.
rewrite app_length in H'.
Admitted.

Lemma app_neq b (s t : string bool) : s <> (b :: t) ++ s.
Proof.
intros H.
apply app_eq_nil' in H.
Admitted.

Lemma FIB_HP x y : i_P x y -> x <> None /\ y <> None.
Proof.
destruct x as [ [s HS] |], y as [ [t HT]|]; auto.
intros _.
Admitted.

Lemma le_irrel k l : forall H1 H2 : k <= l, H1 = H2.
Proof.
induction l; depelim H1.
-
intros H2.
now rewrite le_irrel'.
-
intros H2.
now rewrite le_irrel'.
-
depelim H2; try apply le_irrel'.
f_equal.
apply IHl.
