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

Lemma Encode_list_injective : injective cX -> injective Encode_list.
Proof.
apply encode_list_injective.
