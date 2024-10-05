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
}
