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

Lemma constant_aux : forall A v x u l (m : S.t A), NoDupA X.eq l -> S.find x (fold_left (fun a e => S.add e v a) l m) = Some u <-> InA X.eq x l ∧ u = v ∨ ¬InA X.eq x l ∧ S.find x m = Some u.
Proof.
intros A v x u l.
induction l as [| x' l]; intros m Hl; simpl.
*
rewrite InA_nil.
tauto.
*
rewrite IHl.
clear IHl.
split; intro Hin.
+
destruct Hin as [[Hin ?] | [? Hin]].
-
left.
split; trivial.
now right.
-
{
destruct (X.eq_dec x' x) as [Heq | Heq].
+
left.
rewrite Heq.
split; try now left.
cut (Some u = Some v).
intro Heq'; inversion Heq'; reflexivity.
rewrite <- Hin.
apply S.find_1.
eapply S.MapsTo_1, S.add_1; try eassumption || reflexivity.
+
right.
split.
-
intro Habs.
inversion_clear Habs; solve [contradiction | apply Heq; symmetry; assumption].
-
eapply S.find_1, S.add_3, S.find_2; eassumption.
}
+
destruct Hin as [[Hin ?] | [? Hin]].
-
subst.
inversion_clear Hin; try tauto.
right.
split.
inversion_clear Hl.
rewrite H.
assumption.
apply S.find_1, S.add_1.
symmetry; assumption.
-
right.
split.
intro Habs.
apply H.
now right.
apply S.find_1, S.add_2, S.find_2; trivial.
intro Habs.
apply H.
now left.
+
inversion_clear Hl.
Admitted.

Lemma constant_Some : forall A dom (v : A) x u, find x (constant dom v) = Some u <-> Dom.In x dom ∧ u = v.
Proof.
intros A dom v x u.
unfold constant, find.
simpl.
rewrite Dom.fold_spec, <- Dom.elements_spec1, constant_aux.
split; intro Hin.
+
destruct Hin; trivial.
exfalso.
destruct H as [_ Habs].
apply S.find_2 in Habs.
revert Habs.
apply S.empty_1.
+
left.
assumption.
+
eapply SortA_NoDupA; refine _.
Admitted.

Lemma constant_None : forall A dom (v : A) x, find x (constant dom v) = None <-> ¬Dom.In x dom.
Proof.
intros A dom v x.
unfold constant, find.
simpl.
rewrite Dom.fold_spec, <- Dom.elements_spec1.
split; intro Hin.
+
intro Habs.
assert (Hconj := conj Habs (eq_refl v)).
apply (@or_introl _ (¬ InA X.eq (x : Dom.elt) (Dom.elements dom) ∧ S.find x (S.empty A) = Some v)) in Hconj.
rewrite <- constant_aux in Hconj.
-
cut (None = Some v).
discriminate.
rewrite <- Hin.
assumption.
-
eapply SortA_NoDupA; refine _.
apply Dom.elements_spec2.
+
destruct (S.find x (fold_left (fun a (e : Dom.elt) => S.add e v a) (Dom.elements dom) (S.empty A))) eqn:H; trivial.
rewrite constant_aux in H.
destruct H as [[H _] | [_ H]].
-
contradiction.
-
exfalso.
apply S.find_2 in H.
revert H.
apply S.empty_1.
-
eapply SortA_NoDupA; refine _.
Admitted.

Lemma map_spec : forall A B (f : A -> B) dom (m : t A dom) x v, find x (map f m) = Some v <-> exists u, find x m = Some u ∧ f u = v.
Proof.
intros A B f dom m x v.
unfold find, map.
simpl.
split; intro Hin.
+
assert (Hf : S.In x (S.map f (proj1_sig m))).
{
exists v.
apply S.find_2.
assumption.
}
apply S.map_2 in Hf.
destruct Hf as [u Hu].
exists u.
split.
-
apply S.find_1.
assumption.
-
eapply S.map_1, S.find_1 in Hu.
erewrite Hu in Hin.
inversion Hin.
reflexivity.
+
destruct Hin as [u [Hu Heq]].
subst.
apply S.find_1, S.map_1, S.find_2.
Admitted.

Lemma combine_spec : forall A B C (f : A -> B -> C) g₁ g₂ dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t B dom₂) x v, find x (combine f g₁ g₂ m₁ m₂) = Some v <-> (exists v₁ v₂, find x m₁ = Some v₁ ∧ find x m₂ = Some v₂ ∧ v = f v₁ v₂) ∨ (exists v₁, find x m₁ = Some v₁ ∧ find x m₂ = None ∧ v = g₁ v₁) ∨ (exists v₂, find x m₁ = None ∧ find x m₂ = Some v₂ ∧ v = g₂ v₂).
Proof.
intros A B C f g₁ g₂ dom₁ dom₂ [m₁ Hok₁] [m₂ Hok₂] x v.
unfold combine, find.
simpl.
rewrite Scombine_spec.
split; intros [Hin | [Hin | Hin]].
+
destruct Hin as [v₁ [v₂ [Hin₁ [Hin₂ Heq]]]].
left.
exists v₁, v₂.
auto.
+
destruct Hin as [v₁ [Hin₁ [Hin₂ Heq]]].
right; left.
exists v₁.
auto.
+
destruct Hin as [v₂ [Hin₁ [Hin₂ Heq]]].
do 2 right.
exists v₂.
auto.
+
destruct Hin as [v₁ [v₂ [Hin₁ [Hin₂ Heq]]]].
left.
exists v₁, v₂.
auto.
+
destruct Hin as [v₁ [Hin₁ [Hin₂ Heq]]].
right; left.
exists v₁.
auto.
+
destruct Hin as [v₂ [Hin₁ [Hin₂ Heq]]].
do 2 right.
exists v₂.
Admitted.

Lemma add_same : forall A x v dom (m : t A dom), find x (add x v m) = Some v.
Proof.
intros ? ? ? ? [? ?].
unfold add, find.
simpl.
apply S.find_1, S.add_1.
reflexivity.
