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
assumption.
