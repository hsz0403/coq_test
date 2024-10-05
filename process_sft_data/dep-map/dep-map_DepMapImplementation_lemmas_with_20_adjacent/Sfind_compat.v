Require Import Utf8.
Require Import MSets.
Require Import FMaps.
Require Import Orders.
Require Import Coqlib.
Require Import DepMapInterface.
Set Implicit Arguments.
Module DepMapImpl (X : OrderedType) : (DepMap X) with Definition key := X.t.
Module Dom := MSetAVL.Make(X).
Module Ddec := Decide(Dom).
Module DProp := EqProperties(Dom).
Ltac fsetdec := Ddec.fsetdec.
Module XOT := OTconvert X.
Module S := FMapList.Make(XOT).
Definition key := X.t.
Definition OK {A} dom (map : S.t A) := ∀ x, S.In x map <-> Dom.In x dom.
Definition t := fun A dom => { map : S.t A | OK dom map}.
Instance OK_compat A : Proper (Dom.eq ==> @S.Equal A ==> iff) OK.
Proof.
intros dom₁ dom₂ Hdom m₁ m₂ Heq.
split; intros Hok x.
+
rewrite <- Hdom, <- (Hok x).
split; intros [v Hin]; exists v; apply S.find_2.
-
rewrite Heq.
apply S.find_1.
assumption.
-
rewrite <- Heq.
apply S.find_1.
assumption.
+
rewrite Hdom, <- (Hok x).
split; intros [v Hin]; exists v; apply S.find_2.
-
rewrite <- Heq.
apply S.find_1.
assumption.
-
rewrite Heq.
apply S.find_1.
assumption.
Definition empty : forall A, t A Dom.empty := fun A => exist (OK Dom.empty) (@S.empty A) (empty_OK A).
Definition is_empty (A : Type) dom (m : t A dom) := Dom.equal dom Dom.empty.
Definition mem (A : Type) dom (x : key) (m : t A dom) := Dom.mem x dom.
Definition find (A : Type) dom (x : key) (m : t A dom) := S.find x (proj1_sig m).
Definition domain (A : Type) dom (m : t A dom) := dom.
Definition add {A : Type} {dom : Dom.t} (x : key) (v : A) (m : @t A dom) : @t A (Dom.add x dom) := exist (OK (Dom.add x dom)) (S.add x v (proj1_sig m)) (add_OK x v m).
Definition set {A : Type} {dom : Dom.t} (x : key) (v : A) (m : @t A dom) (Hin : Dom.In x dom) := exist (OK dom) (S.add x v (proj1_sig m)) (@set_OK _ _ x v m Hin).
Arguments set {A} {dom} x v m _.
Definition singleton {A : Type} (x : key) (v : A) : t A (Dom.singleton x) := exist (OK (Dom.singleton x)) (S.add x v (@S.empty A)) (singleton_OK x v).
Definition remove {A : Type} {dom : Dom.t} (x : key) (m : @t A dom) : @t A (Dom.remove x dom) := exist (OK (Dom.remove x dom)) (S.remove x (proj1_sig m)) (remove_OK x m).
Definition constant (A : Type) dom (v : A) : t A dom := exist (OK dom) (Dom.fold (fun x m => S.add x v m) dom (@S.empty A)) (constant_OK dom v).
Definition fold {A B : Type} (f : key -> A -> B -> B) dom (m : t A dom) (i : B) : B := S.fold f (proj1_sig m) i.
Definition map {A B : Type} (f : A -> B) dom (m : t A dom) : t B dom := exist (OK dom) (S.map f (proj1_sig m)) (map_OK f m).
Definition Scombine {A B C : Type} (f : A -> B -> C) (g : A -> C) (h : B -> C) (m₁ : S.t A) (m₂ : S.t B) : S.t C := Dom.fold (fun x acc => match S.find x m₁, S.find x m₂ with | Some v₁, Some v₂ => S.add x (f v₁ v₂) acc | Some v, None => S.add x (g v) acc | None, Some v => S.add x (h v) acc | None, None => acc end) (Dom.union (S.fold (fun x _ acc => Dom.add x acc) m₁ Dom.empty) (S.fold (fun x _ acc => Dom.add x acc) m₂ Dom.empty)) (S.empty C).
Definition combine A B C f g₁ g₂ dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t B dom₂) : t C (Dom.union dom₁ dom₂) := exist (OK (Dom.union dom₁ dom₂)) (Scombine f g₁ g₂ (proj1_sig m₁) (proj1_sig m₂)) (combine_OK f g₁ g₂ m₁ m₂).
Definition cast {A : Type} dom₁ dom₂ (Heq : Dom.eq dom₁ dom₂) (m : t A dom₁) : t A dom₂ := exist (OK dom₂) (proj1_sig m) (cast_OK Heq (proj2_sig m)).
Definition elements A dom (m : t A dom) := S.elements (proj1_sig m).
Definition from_elements A (l : list (key * A)) : t A (List.fold_left (fun acc xv => Dom.add (fst xv) acc) l Dom.empty) := exist (OK (List.fold_left (fun acc xv => Dom.add (fst xv) acc) l Dom.empty)) (List.fold_left (fun acc xv => S.add (fst xv) (snd xv) acc) l (@S.empty A)) (from_elements_OK l).
Instance find_elt_compat A dom (m : t A dom) : Proper (X.eq ==> Logic.eq) (fun x => find x m).
Proof.
intros x y Hxy.
unfold find.
destruct (S.find y (proj1_sig m)) as [v |] eqn:Hin.
+
eapply S.find_1, S.MapsTo_1, S.find_2; try eassumption.
now symmetry.
+
destruct (S.find x (proj1_sig m)) as [v |] eqn:Hin'; trivial.
eapply S.find_2, S.MapsTo_1, S.find_1 in Hin'; try eassumption; auto.
rewrite Hin in Hin'.
discriminate Hin'.
End DepMapImpl.

Instance OK_compat A : Proper (Dom.eq ==> @S.Equal A ==> iff) OK.
Proof.
intros dom₁ dom₂ Hdom m₁ m₂ Heq.
split; intros Hok x.
+
rewrite <- Hdom, <- (Hok x).
split; intros [v Hin]; exists v; apply S.find_2.
-
rewrite Heq.
apply S.find_1.
assumption.
-
rewrite <- Heq.
apply S.find_1.
assumption.
+
rewrite Hdom, <- (Hok x).
split; intros [v Hin]; exists v; apply S.find_2.
-
rewrite <- Heq.
apply S.find_1.
assumption.
-
rewrite Heq.
apply S.find_1.
Admitted.

Lemma empty_OK : forall A, OK Dom.empty (S.empty A).
Proof.
intro x.
split; intro Hin.
+
destruct Hin as [v Hin].
elim (S.empty_1 Hin).
+
Admitted.

Lemma add_OK : forall A dom x v (m : t A dom), OK (Dom.add x dom) (S.add x v (proj1_sig m)).
Proof.
destruct m as [m Hok].
simpl.
intro y.
split; intro Hin.
+
destruct Hin as [u Hy].
destruct (X.eq_dec x y) as [Hxy | Hxy].
-
fsetdec.
-
rewrite Dom.add_spec.
right.
rewrite <- (Hok y).
apply S.add_3 in Hy; trivial.
exists u.
assumption.
+
rewrite Dom.add_spec in Hin.
destruct (X.eq_dec x y) as [Hxy | Hxy].
-
exists v.
apply S.add_1.
assumption.
-
destruct Hin as [Hin | Hin]; try now symmetry in Hin; contradiction.
rewrite <- (Hok y) in Hin.
destruct Hin as [u Hy].
exists u.
Admitted.

Lemma set_OK : forall A dom x v (m : t A dom), Dom.In x dom -> OK dom (S.add x v (proj1_sig m)).
Proof.
destruct m as [m Hok].
intros Hx y.
simpl.
destruct (X.eq_dec y x) as [Hxy | Hxy].
+
split; intro Hin.
-
rewrite Hxy.
assumption.
-
exists v.
apply S.add_1.
symmetry.
assumption.
+
split; intro Hin.
-
destruct Hin as [v' Hin].
rewrite <- (Hok y).
exists v'.
eapply S.add_3.
symmetry.
eassumption.
eassumption.
-
rewrite <- (Hok y) in Hin.
destruct Hin as [v' Hin].
exists v'.
eapply S.add_2.
symmetry.
assumption.
Admitted.

Lemma singleton_OK : forall A x v, OK (Dom.singleton x) (S.add x v (S.empty A)).
Proof.
intros A x v y.
split; intro Hin.
+
destruct (X.eq_dec y x) as [Hxy | Hxy].
-
fsetdec.
-
destruct Hin as [u Hin].
apply S.add_3 in Hin.
elim (S.empty_1 Hin).
symmetry.
assumption.
+
rewrite Dom.singleton_spec in Hin.
exists v.
apply S.add_1.
Admitted.

Lemma remove_OK : forall A dom x (m : t A dom), OK (Dom.remove x dom) (S.remove (elt:=A) x (proj1_sig m)).
Proof.
destruct m as [m Hok].
simpl.
intro y.
split; intro Hin.
+
destruct (X.eq_dec x y) as [Hxy | Hxy].
-
elim (S.remove_1 Hxy Hin).
-
rewrite Dom.remove_spec.
destruct Hin as [u Hy].
apply S.remove_3 in Hy.
rewrite <- (Hok y).
split.
now exists u.
now symmetry.
+
rewrite Dom.remove_spec in Hin.
destruct Hin as [Hin Hxy].
rewrite <- (Hok y) in Hin.
destruct Hin as [u Hin].
exists u.
apply S.remove_2; trivial.
Admitted.

Lemma constant_OK_aux : forall A v (m : S.t A) l x, S.In x (fold_left (λ (a : S.t A) (e : Dom.elt), S.add e v a) l m) <-> S.In x m ∨ InA X.eq x l.
Proof.
intros A v m l x.
revert m.
induction l as [| y l]; intro m; simpl.
*
rewrite InA_nil.
intuition.
*
split; intro Hin.
+
destruct (X.eq_dec x y) as [Hxy | Hxy].
-
right; left.
assumption.
-
rewrite IHl in Hin.
destruct Hin as [[v' Hin] | Hin].
left.
exists v'.
apply S.add_3 in Hin; auto.
now symmetry.
now do 2 right.
+
rewrite IHl.
destruct Hin as [Hin | Hin].
-
left.
destruct (X.eq_dec x y) as [Hxy | Hxy].
exists v.
apply S.add_1.
now auto.
destruct Hin as [v' Hin].
exists v'.
apply S.add_2; auto.
now symmetry.
-
inversion_clear Hin.
left.
exists v.
apply S.add_1.
now auto.
Admitted.

Corollary constant_OK : forall A dom v, OK dom (Dom.fold (fun x m => S.add x v m) dom (S.empty A)).
Proof.
intros * ?.
rewrite Dom.fold_spec, <- Dom.elements_spec1, constant_OK_aux.
intuition.
destruct H0 as [? Hin].
Admitted.

Lemma map_OK : forall A B (f : A -> B) dom (m : t A dom), OK dom (S.map f (proj1_sig m)).
Proof.
intros A B f dom m.
intro x.
rewrite <- (proj2_sig m x).
split; intro Hin.
+
apply S.map_2 in Hin.
assumption.
+
destruct Hin as [v Hv].
exists (f v).
apply S.map_1.
Admitted.

Lemma Sdom_aux : forall A x (m : S.t A) s, Dom.In x (S.fold (fun x _ acc => Dom.add x acc) m s) <-> S.In x m ∨ Dom.In x s.
Proof.
intros A x m.
setoid_rewrite S.fold_1.
assert (Hequiv : S.In x m ↔ (∃ v : A, InA (X.eq * eq)%signature (x, v) (S.elements m))).
{
split; intros [v Hin]; exists v; apply S.elements_1 + apply S.elements_2; assumption.
}
setoid_rewrite Hequiv.
generalize (S.elements m).
intro l.
induction l as [| [x' v'] l]; simpl.
*
setoid_rewrite InA_nil.
firstorder.
*
intro s.
rewrite IHl.
clear IHl.
rewrite Dom.add_spec.
split; intros [[v Hin] | Hin].
+
left.
exists v.
right.
assumption.
+
destruct Hin as [Heq |Hin].
-
left.
exists v'.
left.
split; trivial.
reflexivity.
-
tauto.
+
inversion_clear Hin.
-
destruct H.
tauto.
-
left.
exists v.
assumption.
+
Admitted.

Corollary Sdom : forall A x (m : S.t A), Dom.In x (S.fold (fun x _ acc => Dom.add x acc) m Dom.empty) <-> S.In x m.
Proof.
intros.
rewrite Sdom_aux.
Admitted.

Lemma Scombine_spec_aux : forall A B C (f : A -> B -> C) g h x v m₁ m₂ l m, NoDupA X.eq l -> S.find (elt:=C) x (fold_left (fun (acc : S.t C) (x : Dom.elt) => match S.find x m₁, S.find x m₂ with | Some v₁, Some v₂ => S.add x (f v₁ v₂) acc | Some v, None => S.add x (g v) acc | None, Some v => S.add x (h v) acc | None, None => acc end) l m) = Some v <-> InA X.eq x l ∧ ((exists v₁ v₂, S.find x m₁ = Some v₁ ∧ S.find x m₂ = Some v₂ ∧ v = f v₁ v₂) ∨ (exists v₁, S.find x m₁ = Some v₁ ∧ S.find x m₂ = None ∧ v = g v₁) ∨ (exists v₂, S.find x m₁ = None ∧ S.find x m₂ = Some v₂ ∧ v = h v₂)) ∨ ((InA X.eq x l ∧ S.find x m₁ = None ∧ S.find x m₂ = None ∨ ¬InA X.eq x l) ∧ S.find x m = Some v).
Proof.
intros A B C f g h x v m₁ m₂ l.
induction l as [| x' l]; intros m Hnodup; simpl.
*
rewrite InA_nil.
tauto.
*
inversion_clear Hnodup.
rewrite IHl; trivial.
clear IHl.
split; intros [Hin | Hin].
+
left.
destruct Hin as [Hl Hin].
split.
-
now right.
-
destruct Hin as [Hin | [Hin| Hin]]; tauto.
+
destruct Hin as [[[Hl [Hin₁ Hin₂]] | Hl] Hm].
-
{
right.
split.
+
left.
repeat split; trivial.
now right.
+
destruct (X.eq_dec x x') as [Heq | Heq].
-
rewrite (Sfind_compat Heq) in Hin₁; rewrite (Sfind_compat Heq) in Hin₂.
rewrite Hin₁, Hin₂ in Hm.
assumption.
-
destruct (S.find x' m₁), (S.find x' m₂); trivial; apply S.find_2, S.add_3, S.find_1 in Hm; trivial; symmetry; assumption.
}
-
{
destruct (X.eq_dec x x') as [Heq | Heq].
+
destruct (S.find x' m₁) as [v₁ |] eqn:Hv₁, (S.find x' m₂) as [v₂ |] eqn:Hv₂.
-
left.
split; try (left; assumption).
left.
exists v₁, v₂.
repeat rewrite (Sfind_compat Heq).
repeat split; trivial.
cut (Some v = Some (f v₁ v₂)).
intro Hfv; inversion Hfv; reflexivity.
rewrite <- Hm.
apply S.find_1, S.add_1.
symmetry.
assumption.
-
left.
split; try (left; assumption).
right; left.
exists v₁.
repeat rewrite (Sfind_compat Heq).
repeat split; trivial.
cut (Some v = Some (g v₁)).
intro Hfv; inversion Hfv; reflexivity.
rewrite <- Hm.
apply S.find_1, S.add_1.
symmetry.
assumption.
-
left.
split; try (left; assumption).
do 2 right.
exists v₂.
repeat rewrite (Sfind_compat Heq).
repeat split; trivial.
cut (Some v = Some (h v₂)).
intro Hfv; inversion Hfv; reflexivity.
rewrite <- Hm.
apply S.find_1, S.add_1.
symmetry.
assumption.
-
right.
split; trivial.
left.
repeat rewrite (Sfind_compat Heq).
repeat split; trivial.
now left.
+
right.
split.
-
right.
intro Habs.
inversion_clear Habs; contradiction.
-
destruct (S.find x' m₁), (S.find x' m₂); trivial; apply S.find_2, S.add_3, S.find_1 in Hm; trivial; symmetry; assumption.
}
+
destruct Hin as [Hl Hin].
inversion_clear Hl.
-
right.
rewrite H1 at 4.
split; try now right.
destruct Hin as [[v₁ [v₂ [Hin₁ [Hin₂ Hv]]]] | [[v₁ [Hin₁ [Hin₂ Hv]]] | [v₂ [Hin₁ [Hin₂ Hv]]]]]; rewrite (Sfind_compat H1) in Hin₁; rewrite (Sfind_compat H1) in Hin₂; rewrite Hin₁, Hin₂; subst v; apply S.find_1, S.add_1; symmetry; assumption.
-
left.
split; assumption.
+
destruct Hin as [[[Hin [Hin₁ Hin₂]] | Hin] Hm].
-
{
right.
inversion_clear Hin.
+
rewrite (Sfind_compat H1) in Hin₁; rewrite (Sfind_compat H1) in Hin₂; rewrite Hin₁, Hin₂.
split; trivial.
right.
rewrite H1.
assumption.
+
assert (¬X.eq x x').
{
intro Habs.
apply H.
rewrite <- Habs.
assumption.
}
split; try tauto.
destruct (S.find x' m₁), (S.find x' m₂); trivial; apply S.find_1, S.add_2, S.find_2; trivial; symmetry; assumption.
}
-
{
right.
split.
+
right.
intro Habs.
apply Hin.
now right.
+
assert (¬X.eq x x').
{
intro Habs.
apply Hin.
now left.
}
destruct (S.find x' m₁), (S.find x' m₂); trivial; apply S.find_1, S.add_2, S.find_2; trivial; symmetry; assumption.
Admitted.

Theorem Scombine_spec : forall A B C (f : A -> B -> C) g h x v m₁ m₂, S.find x (Scombine f g h m₁ m₂) = Some v <-> (exists v₁ v₂, S.find x m₁ = Some v₁ ∧ S.find x m₂ = Some v₂ ∧ v = f v₁ v₂) ∨ (exists v₁, S.find x m₁ = Some v₁ ∧ S.find x m₂ = None ∧ v = g v₁) ∨ (exists v₂, S.find x m₁ = None ∧ S.find x m₂ = Some v₂ ∧ v = h v₂).
Proof.
intros A B C f g h x v m₁ m₂.
unfold Scombine.
rewrite Dom.fold_spec.
rewrite Scombine_spec_aux.
*
rewrite Dom.elements_spec1, Dom.union_spec, Sdom, Sdom.
split; intro Hin.
+
destruct Hin as [[_ ?] | [_ Habs]].
-
assumption.
-
apply S.find_2, S.empty_1 in Habs.
elim Habs.
+
left.
split; trivial.
destruct Hin as [[v' [? [Hin _]]] | [[v' [? _]] | [v' [_ [? _]]]]]; left + right; exists v'; apply S.find_2; assumption.
*
eapply SortA_NoDupA; refine _.
Admitted.

Lemma combine_OK : forall A B C (f : A -> B -> C) g₁ g₂ dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t B dom₂), OK (Dom.union dom₁ dom₂) (Scombine f g₁ g₂ (proj1_sig m₁) (proj1_sig m₂)).
Proof.
destruct m₁ as [m₁ Hok₁], m₂ as [m₂ Hok₂].
simpl.
intro x.
rewrite Dom.union_spec.
split; intro Hin.
+
destruct Hin as [v Hin].
apply S.find_1 in Hin.
rewrite (Scombine_spec f) in Hin.
destruct Hin as [Hin | [Hin | Hin]].
-
destruct Hin as [v₁ [v₂ [Hv₁ _]]].
left.
rewrite <- (Hok₁ x).
exists v₁.
apply S.find_2.
assumption.
-
destruct Hin as [v₁ [Hv₁ _]].
left.
rewrite <- (Hok₁ x).
exists v₁.
apply S.find_2.
assumption.
-
destruct Hin as [v₂ [_ [Hv₂ _]]].
right.
rewrite <- (Hok₂ x).
exists v₂.
apply S.find_2.
assumption.
+
destruct (Dom.mem x dom₁) eqn:Hin₁, (Dom.mem x dom₂) eqn:Hin₂; try rewrite Dom.mem_spec in *.
-
rewrite <- (Hok₁ x) in Hin₁.
destruct Hin₁ as [v₁ Hin₁].
rewrite <- (Hok₂ x) in Hin₂.
destruct Hin₂ as [v₂ Hin₂].
exists (f v₁ v₂).
apply S.find_2.
rewrite Scombine_spec.
left.
exists v₁, v₂.
now repeat split; apply S.find_1.
-
rewrite <- (Hok₁ x) in Hin₁.
destruct Hin₁ as [v₁ Hin₁].
exists (g₁ v₁).
apply S.find_2.
rewrite Scombine_spec.
right; left.
exists v₁.
repeat split; try now apply S.find_1.
destruct (S.find x m₂) as [v |] eqn:Hfind; trivial.
assert (Habs : S.In x m₂) by now exists v; apply S.find_2.
rewrite (Hok₂ x), <- Dom.mem_spec, Hin₂ in Habs.
discriminate Habs.
-
rewrite <- (Hok₂ x) in Hin₂.
destruct Hin₂ as [v₂ Hin₂].
exists (g₂ v₂).
apply S.find_2.
rewrite Scombine_spec.
do 2 right.
exists v₂.
repeat split; try now apply S.find_1.
destruct (S.find x m₁) as [v |] eqn:Hfind; trivial.
assert (Habs : S.In x m₁) by now exists v; apply S.find_2.
rewrite (Hok₁ x), <- Dom.mem_spec, Hin₁ in Habs.
discriminate Habs.
-
Admitted.

Lemma cast_OK : forall A dom₁ dom₂ (Heq : Dom.eq dom₁ dom₂) (m : S.t A), OK dom₁ m -> OK dom₂ m.
Proof.
intros.
apply (@OK_compat A _ _ Heq m m); trivial.
intro.
Admitted.

Lemma pre_from_elements_OK : forall A l dom (m : t A dom), OK (fold_left (fun acc xv => Dom.add (fst xv) acc) l (domain m)) (fold_left (fun acc xv => S.add (fst xv) (snd xv) acc) l (proj1_sig m)).
Proof.
intros A l.
induction l as [| [x v] l]; intros dom m; simpl; unfold domain.
+
apply (proj2_sig m).
+
change (Dom.add x dom) with (domain (add x v m)).
change (S.add x v (proj1_sig m)) with (proj1_sig (add x v m)).
Admitted.

Corollary from_elements_OK : forall A l, OK (fold_left (fun acc xv => Dom.add (fst xv) acc) l Dom.empty) (fold_left (fun acc xv => S.add (fst xv) (snd xv) acc) l (S.empty A)).
Proof.
intros.
change Dom.empty with (domain (@empty A)).
change (S.empty A) with (proj1_sig (@empty A)).
Admitted.

Lemma empty_spec : forall A x, find x (@empty A) = None.
Proof.
intros.
Admitted.

Lemma is_empty_spec : forall A dom (m : t A dom), is_empty m = true <-> forall x, find x m = None.
Proof.
unfold find, is_empty.
intros A dom [m Hok].
simpl.
split; intro Hempty.
+
intro x.
destruct (S.find x m) as [v |] eqn:?; trivial.
assert (Habs : S.In x m) by now exists v; apply S.find_2.
rewrite (Hok x) in Habs.
rewrite Dom.equal_spec in Hempty.
fsetdec.
+
apply Dom.equal_spec, DProp.MP.empty_is_empty_1.
intros x Habs.
rewrite <- (Hok x) in Habs.
destruct Habs as [v Habs].
apply S.find_1 in Habs.
rewrite Hempty in Habs.
Admitted.

Lemma mem_spec : forall A x dom (m : t A dom), mem x m = true <-> exists v, find x m = Some v.
Proof.
intros A x dom [m Hok].
unfold mem, find.
simpl.
rewrite Dom.mem_spec.
rewrite <- (Hok x).
Admitted.

Instance find_elt_compat A dom (m : t A dom) : Proper (X.eq ==> Logic.eq) (fun x => find x m).
Proof.
intros x y Hxy.
unfold find.
destruct (S.find y (proj1_sig m)) as [v |] eqn:Hin.
+
eapply S.find_1, S.MapsTo_1, S.find_2; try eassumption.
now symmetry.
+
destruct (S.find x (proj1_sig m)) as [v |] eqn:Hin'; trivial.
eapply S.find_2, S.MapsTo_1, S.find_1 in Hin'; try eassumption; auto.
rewrite Hin in Hin'.
Admitted.

Lemma find_spec : forall A x dom (m : t A dom), (exists v, find x m = Some v) <-> Dom.In x dom.
Proof.
intros A x dom [m Hok].
unfold find.
simpl.
rewrite <- (Hok x).
Admitted.

Lemma domain_spec : forall A dom (m : t A dom), domain m = dom.
Proof.
intros.
Admitted.

Lemma set_same : forall A x v dom (m : t A dom) Hin, find x (@set A dom x v m Hin) = Some v.
Proof.
intros.
unfold set, find.
simpl.
apply S.find_1, S.add_1.
Admitted.

Lemma set_other : forall A x y v dom (m : t A dom) Hin, ¬X.eq y x -> find y (@set A dom x v m Hin) = find y m.
Proof.
intros.
unfold set, find.
simpl.
destruct (S.find y (proj1_sig m)) eqn:Hin1.
+
apply S.find_1, S.add_2, S.find_2; trivial.
now symmetry.
+
destruct (S.find y (S.add x v (proj1_sig m))) eqn:Hin2; trivial.
apply S.find_2, S.add_3, S.find_1 in Hin2.
-
rewrite Hin1 in Hin2.
discriminate Hin2.
-
Admitted.

Lemma add_same : forall A x v dom (m : t A dom), find x (add x v m) = Some v.
Proof.
intros ? ? ? ? [? ?].
unfold add, find.
simpl.
apply S.find_1, S.add_1.
Admitted.

Lemma add_other : forall A x y v dom (m : t A dom), ¬X.eq y x -> find y (add x v m) = find y m.
Proof.
intros A x y v dom [m Hok] Heq.
unfold add, find.
simpl.
destruct (S.find y m) as [u |] eqn:Hin.
+
apply S.find_1, S.add_2, S.find_2; trivial; now symmetry.
+
destruct (S.find y (S.add x v m)) as [u |] eqn:Hin'; trivial.
apply S.find_2, S.add_3, S.find_1 in Hin'.
rewrite Hin in Hin'.
discriminate Hin'.
Admitted.

Lemma singleton_same : forall A x (v : A), find x (singleton x v) = Some v.
Proof.
intros.
unfold singleton, find.
simpl.
apply S.find_1, S.add_1.
Admitted.

Lemma singleton_other : forall A x y (v : A), ¬X.eq y x -> find y (singleton x v) = None.
Proof.
intros A x y v Heq.
unfold singleton, find.
simpl.
destruct (S.find y (S.add x v (S.empty A))) as [u |] eqn:Hin; trivial.
apply S.find_2, S.add_3 in Hin.
elim (S.empty_1 Hin).
Admitted.

Lemma remove_same : forall A x dom (m : t A dom), find x (remove x m) = None.
Proof.
intros A x dom [m Hok].
unfold remove, find.
simpl.
destruct (S.find x (S.remove x m)) as [v |] eqn:Hin; trivial.
apply S.find_2 in Hin.
eelim S.remove_1.
reflexivity.
exists v.
Admitted.

Lemma remove_other : forall A x y dom (m : t A dom), ¬X.eq y x -> find y (remove x m) = find y m.
Proof.
intros A x y dom [m Hok] Heq.
unfold find, remove.
simpl.
destruct (S.find y m) as [v |] eqn:Hin.
+
apply S.find_1, S.remove_2, S.find_2; trivial; now symmetry.
+
destruct (S.find y (S.remove x m)) as [v |] eqn:Hin'; trivial.
apply S.find_2, S.remove_3, S.find_1 in Hin'; auto.
rewrite Hin in Hin'.
Admitted.

Lemma Sfind_compat : forall {A x y} {m : S.t A}, X.eq x y -> S.find x m = S.find y m.
Proof.
intros A x y m Hxy.
destruct (S.find y m) eqn:Hin.
+
symmetry in Hxy.
eapply S.find_1, S.MapsTo_1, S.find_2; eassumption.
+
destruct (S.find x m) eqn:Habs; trivial.
rewrite <- Hin.
symmetry.
eapply S.find_1, S.MapsTo_1, S.find_2; eassumption.
