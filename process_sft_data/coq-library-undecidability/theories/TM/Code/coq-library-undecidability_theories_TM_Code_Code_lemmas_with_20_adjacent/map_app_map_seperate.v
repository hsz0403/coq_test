From Undecidability Require Import TM.Util.Prelim.
Require Import Coq.Lists.List.
Require Import Undecidability.Shared.Libs.PSL.Bijection.
Class codable (sig: Type) (X: Type) := { encode : X -> list sig; }.
Arguments encode {sig} {X} {_}.
Hint Mode codable - ! : typeclass_instances.
Hint Mode codable ! - : typeclass_instances.
Hint Mode Retract ! + : typeclass_instances.
Hint Extern 4 (codable (FinType(EqType ?sigX)) ?X) => cbn : typeclass_instances.
Coercion encode : codable >-> Funclass.
Definition size (sig X : Type) (cX : codable sig X) (x : X) := length (cX x).
Arguments size {sig X cX} x, {_ _} _ _ (*legacy with two arguments*).
Create HintDb encode_comp.
Ltac simpl_comp := autorewrite with encode_comp.
Instance Encode_unit : codable Empty_set unit := {| encode x := nil |}.
Instance Encode_bool : codable bool bool:= {| encode x := [x] |}.
Instance Encode_Fin n : codable (Fin.t n) (Fin.t n):= {| encode i := [i] |}.
Section Encode_Finite.
Variable sig : finType.
Local Instance Encode_Finite : codable sig sig := {| encode x := [x]; |}.
End Encode_Finite.
Section Encode_map.
Variable (X : Type).
Variable (sig tau : Type).
Hypothesis (cX : codable sig X).
Variable inj : Retract sig tau.
Definition Encode_map : codable tau X := {| encode x := map Retr_f (encode x); |}.
End Encode_map.
Section Encode_map_comp.
Variable (X : Type).
Variable (sig1 sig2 sig3 : Type).
Variable (cX : codable sig1 X).
Variable (I1 : Retract sig1 sig2) (I2 : Retract sig2 sig3).
End Encode_map_comp.
Hint Rewrite Encode_map_id Encode_map_comp : encode_comp.
Local Hint Mode Retract - - : typeclass_instances.
Ltac build_simple_retract_g := once lazymatch goal with | [ |- ?Y -> option ?X ] => (* idtac "Retract function" X Y; *) let x := fresh "x" in intros x; destruct x; intros; try solve [now apply Retr_g ]; right end.
Ltac build_simple_retract := once lazymatch goal with | [ |- Retract ?X ?Y ] => (* idtac "Retract from" X "to" Y; *) let x := fresh "x" in let y := fresh "y" in let f := (eval simpl in (ltac:(intros x; constructor; now apply Retr_f) : X -> Y)) in (* idtac "f:" f; *) let g := (eval simpl in (ltac:(build_simple_retract_g) : Y -> option X)) in (* idtac "g:" g; *) apply Build_Retract with (Retr_f := f) (Retr_g := g); abstract now hnf; intros x y; split; [ destruct y; try congruence; now intros -> % retract_g_inv | now intros ->; now retract_adjoint ] end .
Ltac build_eq_dec := let x := fresh "x" in let y := fresh "y" in intros x y; hnf; decide equality; apply Dec; auto.
Section Encode_sum.
Variable (X Y : Type).
Inductive sigSum (sigX sigY : Type) : Type := | sigSum_X (s : sigX) | sigSum_Y (s : sigY) | sigSum_inl | sigSum_inr .
Arguments sigSum_inl {sigX sigY}.
Arguments sigSum_inr {sigX sigY}.
Arguments sigSum_X {sigX sigY}.
Arguments sigSum_Y {sigX sigY}.
Global Instance Retract_sigSum_X (sigX sigY tau : Type) (f : Retract sigX tau) : Retract sigX (sigSum tau sigY).
Proof.
build_simple_retract.
Defined.
Global Instance Retract_sigSum_Y (sigX sigY tau : Type) (f : Retract sigY tau) : Retract sigY (sigSum sigX tau).
Proof.
build_simple_retract.
Defined.
Global Instance sigSum_dec (sigX sigY : Type) (decX: eq_dec sigX) (decY: eq_dec sigY) : eq_dec (sigSum sigX sigY) := ltac:(build_eq_dec).
Global Instance sigSum_fin (sigX sigY : finType) : finTypeC (EqType (sigSum sigX sigY)).
Proof.
split with (enum := sigSum_inl :: sigSum_inr :: map sigSum_X enum ++ map sigSum_Y enum).
intros [x|y| | ]; cbn; f_equal.
-
rewrite <- !countSplit.
erewrite countMap_injective.
+
rewrite enum_ok.
rewrite countMap_zero.
lia.
congruence.
+
eapply (retract_f_injective) with (I := Retract_sigSum_X sigY (Retract_id _)).
-
rewrite <- !countSplit.
erewrite countMap_injective.
+
rewrite enum_ok.
rewrite countMap_zero.
lia.
congruence.
+
eapply (retract_f_injective) with (I := Retract_sigSum_Y sigX (Retract_id _)).
-
rewrite <- !countSplit.
rewrite !countMap_zero.
lia.
all: congruence.
-
rewrite <- !countSplit.
rewrite !countMap_zero.
lia.
all: congruence.
Variable (sigX sigY : Type).
Hypothesis (cX : codable sigX X) (cY : codable sigY Y).
Global Instance Encode_sum : codable (sigSum sigX sigY) (X+Y) := {| encode s := match s with | inl x => sigSum_inl :: (Encode_map _ _ x) | inr y => sigSum_inr :: (Encode_map _ _ y) end |}.
Definition Encode_sum_size (s:X+Y) := match s with | inl x => S (size x) | inr y => S (size y) end.
End Encode_sum.
Arguments sigSum_inl {sigX sigY}.
Arguments sigSum_inr {sigX sigY}.
Arguments sigSum_X {sigX sigY}.
Arguments sigSum_Y {sigX sigY}.
Hint Extern 4 (finTypeC (EqType (sigSum _ _))) => eapply sigSum_fin : typeclass_instances.
Section Encode_pair.
Inductive sigPair (sigX sigY : Type) : Type := | sigPair_X (s : sigX) | sigPair_Y (s : sigY) .
Arguments sigPair_X {sigX sigY}.
Arguments sigPair_Y {sigX sigY}.
Global Instance Retract_sigPair_X (sigX sigY tau : Type) (f : Retract sigX tau) : Retract sigX (sigPair tau sigY).
Proof.
build_simple_retract.
Defined.
Global Instance Retract_sigPair_Y (sigX sigY tau : Type) (f : Retract sigY tau) : Retract sigY (sigPair sigX tau).
Proof.
build_simple_retract.
Defined.
Global Instance sigPair_dec (sigX sigY : Type) (decX: eq_dec sigX) (decY: eq_dec sigY) : eq_dec (sigPair sigX sigY) := ltac:(build_eq_dec).
Global Instance sigPair_fin (sigX sigY : finType) : finTypeC (EqType (sigPair sigX sigY)).
Proof.
split with (enum := map sigPair_X enum ++ map sigPair_Y enum).
intros [x|y]; cbn; f_equal.
-
rewrite <- !countSplit.
erewrite countMap_injective.
+
rewrite enum_ok.
rewrite countMap_zero.
lia.
congruence.
+
eapply (retract_f_injective) with (I := Retract_sigPair_X sigY (Retract_id _)).
-
rewrite <- !countSplit.
erewrite countMap_injective.
+
rewrite enum_ok.
rewrite countMap_zero.
lia.
congruence.
+
eapply (retract_f_injective) with (I := Retract_sigPair_Y sigX (Retract_id _)).
Variable (sigX sigY: Type) (X Y: Type) (cX : codable sigX X) (cY : codable sigY Y).
Global Instance Encode_pair : codable (sigPair sigX sigY) (X*Y) := {| encode '(x,y) := Encode_map _ _ x ++ Encode_map _ _ y; |}.
Definition Encode_pair_size (p : X * Y) := let (x, y) := p in size x + size y.
End Encode_pair.
Arguments sigPair_X {sigX sigY}.
Arguments sigPair_Y {sigX sigY}.
Hint Extern 4 (finTypeC (EqType (sigPair _ _))) => eapply sigPair_fin : typeclass_instances.
Section Encode_option.
Inductive sigOption (sigX: Type) : Type := | sigOption_X (s : sigX) | sigOption_None | sigOption_Some .
Arguments sigOption_Some {sigX}.
Arguments sigOption_None {sigX}.
Arguments sigOption_X {sigX}.
Global Instance Retract_sigOption_X (sig tau : Type) (retr : Retract sig tau) : Retract sig (sigOption tau).
Proof.
build_simple_retract.
Defined.
Global Instance sigOption_dec sigX (decX : eq_dec sigX) : eq_dec (sigOption sigX) := ltac:(build_eq_dec).
Global Instance sigOption_fin (sigX : finType) : finTypeC (EqType (sigOption sigX)).
Proof.
split with (enum := sigOption_Some :: sigOption_None :: map sigOption_X enum).
intros [x| | ]; cbn; f_equal.
-
rewrite countMap_injective.
2: apply retract_f_injective with (I := Retract_sigOption_X (Retract_id _)).
now apply enum_ok.
-
rewrite countMap_zero.
lia.
congruence.
-
rewrite countMap_zero.
lia.
congruence.
Variable (sigX: Type) (X: Type) (cX : codable sigX X).
Global Instance Encode_option : codable (sigOption sigX) (option X) := {| encode o := match o with | None => [sigOption_None] | Some x => sigOption_Some :: Encode_map _ _ x end; |}.
Definition Encode_option_size (o : option X) := match o with | None => 1 | Some x => S (size x) end.
End Encode_option.
Arguments sigOption_Some {sigX}.
Arguments sigOption_None {sigX}.
Arguments sigOption_X {sigX}.
Hint Extern 4 (finTypeC (EqType (sigOption _))) => eapply sigOption_fin : typeclass_instances.
Section Encode_list.
Inductive sigList (sigX : Type) : Type := | sigList_X (s : sigX) | sigList_nil | sigList_cons .
Arguments sigList_nil {sigX}.
Arguments sigList_cons {sigX}.
Arguments sigList_X {sigX}.
Global Instance Retract_sigList_X (sig tau : Type) (retr : Retract sig tau) : Retract sig (sigList tau).
Proof.
build_simple_retract.
Defined.
Global Instance sigList_dec sigX (decX : eq_dec sigX) : eq_dec (sigList sigX) := ltac:(build_eq_dec).
Global Instance sigList_fin (sigX : finType) : finTypeC (EqType (sigList sigX)).
Proof.
split with (enum := sigList_nil :: sigList_cons :: map sigList_X enum).
intros [x| | ]; cbn; f_equal.
-
rewrite countMap_injective.
2: apply retract_f_injective with (I := Retract_sigList_X (Retract_id _)).
now apply enum_ok.
-
rewrite countMap_zero.
lia.
congruence.
-
rewrite countMap_zero.
lia.
congruence.
Variable sigX: Type.
Variable (X : Type) (cX : codable sigX X).
Fixpoint encode_list (xs : list X) : list (sigList sigX) := match xs with | nil => [sigList_nil] | x :: xs' => sigList_cons :: Encode_map _ _ x ++ encode_list xs' end.
Global Instance Encode_list : codable (sigList sigX) (list X) := {| encode := encode_list; |}.
Fixpoint Encode_list_size (xs : list X) : nat := match xs with | nil => 1 | x :: xs' => S (size x + Encode_list_size xs') end.
End Encode_list.
Arguments sigList_nil {sigX}.
Arguments sigList_cons {sigX}.
Arguments sigList_X {sigX}.
Hint Extern 4 (finTypeC (EqType (sigList _))) => eapply sigList_fin : typeclass_instances.
Section Encode_nat.
Inductive sigNat : Type := | sigNat_O | sigNat_S.
Global Instance sigNat_eq : eq_dec sigNat.
Proof.
unfold dec.
decide equality.
Defined.
Global Instance sigNat_fin : finTypeC (EqType sigNat).
Proof.
split with (enum := [sigNat_O; sigNat_S]).
intros [ | ]; cbn; reflexivity.
Global Instance Encode_nat : codable sigNat nat := {| encode n := repeat sigNat_S n ++ [sigNat_O]; |}.
End Encode_nat.

Lemma Encode_unit_hasSize (t:unit) : size t = 0.
Proof.
cbn.
Admitted.

Lemma Encode_unit_injective : injective Encode_unit.
Proof.
Admitted.

Lemma Encode_bool_hasSize (b:bool) : size Encode_bool b = 1.
Proof.
cbn.
Admitted.

Lemma Encode_bool_injective : injective Encode_bool.
Proof.
Admitted.

Lemma Encode_Fin_hasSize n i : size (Encode_Fin n) i = 1.
Proof.
cbn.
Admitted.

Lemma Encode_Fin_injective n : injective (Encode_Fin n).
Proof.
intros i1 i2.
cbn.
Admitted.

Lemma Encode_Finite_hasSize f : size Encode_Finite f = 1.
Proof.
Admitted.

Lemma Encode_Finite_injective : injective Encode_Finite.
Proof.
intros x1 x2.
cbn.
Admitted.

Lemma Encode_map_hasSize x : size Encode_map x =size x.
Proof.
cbn.
Admitted.

Lemma Encode_map_injective : injective cX -> injective Encode_map.
Proof.
intros H.
hnf in H; hnf.
cbn in *.
intros x1 x2 ? % map_injective; auto.
Admitted.

Lemma Encode_map_id x : Encode_map cX (Retract_id _) x = cX x.
Proof.
cbn.
Admitted.

Lemma Encode_map_comp x : Encode_map (Encode_map cX I1) I2 x = Encode_map cX (ComposeRetract I2 I1) x.
Proof.
cbn.
rewrite List.map_map.
Admitted.

Lemma countMap_injective (X Y : eqType) (x : X) (A : list X) (f : X -> Y) : (forall x y, f x = f y -> x = y) -> BasicDefinitions.count (map f A) (f x) = BasicDefinitions.count A x.
Proof.
intros HInj.
revert x.
induction A as [ | a A IH]; intros; cbn in *; auto.
decide (f x = f a) as [ -> % HInj | He].
-
decide (a = a) as [_ | Ha]; auto.
congruence.
-
decide (x = a) as [-> | Hx]; auto.
Admitted.

Lemma countMap_zero (X Y : eqType) (A : list X) (y : Y) (f : X -> Y) : (forall x, f x <> y) -> BasicDefinitions.count (map f A) y = 0.
Proof.
revert y.
induction A as [ | a A IH]; intros; cbn in *; auto.
decide (y = f a) as [-> | ?]; auto.
Admitted.

Lemma Encode_sum_hasSize s : size Encode_sum s = Encode_sum_size s.
Proof.
cbn.
Admitted.

Lemma Encode_sum_injective : injective cX -> injective cY -> injective Encode_sum.
Proof.
intros HX HY.
intros [ x1 | y1 ] [ x2 | y2] H; cbn in *; inv H; f_equal.
-
apply map_injective in H1; auto.
congruence.
-
apply map_injective in H1; auto.
Admitted.

Lemma cons_injective (X : Type) (x1 x2 : X) (l1 l2 : list X) : x1 :: l1 = x2 :: l2 -> x1 = x2 /\ l1 = l2.
Proof.
intros H.
inv H.
Admitted.

Lemma Encode_pair_hasSize p : size Encode_pair p = Encode_pair_size p.
Proof.
Admitted.

Lemma Encode_pair_injective : injective cX -> injective cY -> injective Encode_pair.
Proof.
intros HX HY.
intros [x1 y1] [x2 y2] H; cbn in *.
Admitted.

Lemma Encode_option_hasSize o : size o = Encode_option_size o.
Proof.
Admitted.

Lemma Encode_option_injective : injective cX -> injective Encode_option.
Proof.
intros HX.
intros [ x1 | ] [ x2 | ] H; inv H; auto.
f_equal.
apply map_injective in H1.
-
now apply HX in H1.
-
Admitted.

Lemma app_seperate (X : Type) (xs1 xs2 ys1 ys2 : list X) (s1 s2 : X) : (~ In s1 xs2) -> (~ In s2 xs1) -> xs1 ++ s1 :: ys1 = xs2 ++ s2 :: ys2 -> xs1 = xs2 /\ s1 = s2 /\ ys1 = ys2.
Proof.
revert xs2 ys1 ys2 s1 s2.
induction xs1 as [ | x1 xs1 IH]; intros xs2 ys1 ys2 s1 s2; intros H1 H2; intros Heq; cbn in *.
-
destruct xs2 as [ | x2 xs2]; cbn in *.
+
inv Heq.
auto.
+
inv Heq.
exfalso.
apply H1.
auto.
-
destruct xs2 as [ | x2 xs2]; cbn in *.
+
inv Heq.
exfalso.
apply H2.
auto.
+
apply cons_injective in Heq as [-> Heq].
enough (xs1 = xs2 /\ s1 = s2 /\ ys1 = ys2) as (->&->&->) by auto.
Admitted.

Lemma skipn_0 (A:Type) (xs : list A) : skipn 0 xs = xs.
Proof.
Admitted.

Lemma skipn_tl (A:Type) (xs : list A) (n : nat) : skipn (S n) xs = skipn n (tl xs).
Proof.
Admitted.

Lemma encode_list_concat l: encode_list l = concat (map (fun t => sigList_cons :: map sigList_X (encode t)) l) ++[sigList_nil].
Proof.
induction l;cbn.
reflexivity.
rewrite IHl.
cbn.
Admitted.

Lemma encode_list_app (xs ys : list X) : encode_list (xs ++ ys) = removelast (encode_list xs) ++ encode_list ys.
Proof.
revert ys.
induction xs; intros; cbn in *; f_equal.
rewrite IHxs.
rewrite app_assoc, app_comm_cons; f_equal.
destruct (map (fun x : sigX => sigList_X x) (cX a)) eqn:E; cbn.
-
destruct xs; cbn; auto.
-
f_equal.
destruct (cX a) eqn:E2; cbn in E.
congruence.
rewrite removelast_app.
+
destruct (l ++ encode_list xs) eqn:E3; cbn; auto.
apply app_eq_nil in E3 as (E3&E3').
destruct xs; inv E3'.
+
Admitted.

Corollary Encode_list_app (xs ys : list X) : Encode_list (xs ++ ys) = removelast (Encode_list xs) ++ Encode_list ys.
Proof.
cbn.
Admitted.

Lemma encode_list_neq_nil (xs : list X) : encode_list xs <> nil.
Proof.
Admitted.

Corollary Encode_list_neq_nil (xs : list X) : Encode_list xs <> nil.
Proof.
cbn.
Admitted.

Lemma encode_list_remove (xs : list X) : removelast (encode_list xs) ++ [sigList_nil] = encode_list xs.
Proof.
induction xs.
-
reflexivity.
-
cbn [encode_list].
change (sigList_cons :: Encode_map _ _ a ++ encode_list xs) with ((sigList_cons :: Encode_map _ _ a) ++ encode_list xs).
rewrite removelast_app by apply encode_list_neq_nil.
rewrite <- app_assoc.
f_equal.
Admitted.

Corollary Encode_list_remove (xs : list X) : removelast (Encode_list xs) ++ [sigList_nil] = Encode_list xs.
Proof.
cbn.
Admitted.

Lemma Encode_list_hasSize (xs : list X) : size xs = Encode_list_size xs.
Proof.
induction xs as [ | x xs IH]; cbn; f_equal.
rewrite app_length, !map_length.
fold (size x).
Admitted.

Lemma Encode_list_hasSize_skipn (xs : list X) (n : nat) : Encode_list_size (skipn n xs) <= Encode_list_size xs.
Proof.
revert n.
induction xs as [ | x xs' IH]; intros n.
-
cbn.
rewrite skipn_nil.
cbn.
reflexivity.
-
cbn.
destruct n.
+
rewrite skipn_0.
cbn.
reflexivity.
+
cbn.
rewrite IH.
Admitted.

Lemma Encode_list_hasSize_ge1 (xs : list X) : 1 <= Encode_list_size xs.
Proof.
Admitted.

Lemma Encode_list_hasSize_app (xs ys : list X) : Encode_list_size (xs ++ ys) = Encode_list_size xs + Encode_list_size ys - 1.
Proof.
induction xs as [ | x xs IH] in xs,ys|-*; cbn.
-
lia.
-
rewrite IH.
enough (1 <= Encode_list_size xs) by lia.
Admitted.

Lemma encode_list_eq_nil (xs : list X) : encode_list xs = [sigList_nil] -> xs = nil.
Proof.
Admitted.

Lemma encode_list_injective : injective cX -> injective encode_list.
Proof.
intros HX.
hnf in *.
intros xs.
induction xs as [ | x xs IH]; intros ys H; cbn in *.
-
symmetry in H.
apply encode_list_eq_nil in H.
auto.
-
destruct ys as [ | y ys]; cbn in *.
+
inv H.
+
apply cons_injective in H as [_ H].
destruct xs as [ | x' xs]; cbn in *.
*
destruct ys as [ | y' ys]; cbn in *.
--
apply app_inj_tail in H as [H _].
apply map_injective in H; auto.
now apply HX in H as ->.
congruence.
--
exfalso.
apply app_seperate in H as (H1&H2&H3); cbn; auto.
++
congruence.
++
intros (?&?&?) % in_map_iff.
congruence.
++
intros (?&?&?) % in_map_iff.
congruence.
*
destruct ys as [ | y' ys]; cbn in *.
--
exfalso.
eapply app_seperate in H as (H1&H2&H3); cbn; auto.
++
congruence.
++
intros (?&?&?) % in_map_iff.
congruence.
++
intros (?&?&?) % in_map_iff.
congruence.
--
apply app_seperate in H as (H1&H2&H3).
++
apply map_injective, HX in H1 as ->; auto.
2: congruence.
specialize (IH (y' :: ys)).
spec_assert IH by (cbn; f_equal; auto).
rewrite IH.
auto.
++
intros (?&?&?) % in_map_iff.
congruence.
++
intros (?&?&?) % in_map_iff.
Admitted.

Lemma map_app_map_seperate (X Y Z : Type) (f : X -> Z) (g : Y -> Z) (x1 x2 : list X) (y1 y2 : list Y) : injective f -> injective g -> (forall x y, f x <> g y) -> map f x1 ++ map g y1 = map f x2 ++ map g y2 -> x1 = x2 /\ y1 = y2.
Proof.
intros Hf Hg Hfg.
revert x2 y1 y2.
induction x1 as [ | x x1 IH]; intros x2 y1 y2 HApp; cbn in *.
-
apply map_eq_app in HApp as (l1&l2&->&HApp1&HApp2).
apply map_injective in HApp2 as ->; auto.
destruct x2, l1; cbn in *; auto; inv HApp1.
exfalso.
eapply Hfg; eauto.
-
destruct x2 as [ | x' x2]; cbn in *.
+
exfalso.
destruct y2; cbn in *; inv HApp.
eapply Hfg; eauto.
+
apply cons_injective in HApp as [-> % Hf HApp].
apply IH in HApp as [-> ->].
auto.
