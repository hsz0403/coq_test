Require Import Utf8.
Require Import Bool.
Require Import SetoidList.
Require Import RelationPairs.
Require Import Orders.
Require Import Coqlib.
Require Import DepMapInterface.
Require Import DepMapFactsInterface.
Set Implicit Arguments.
Module DepMapFactsOn (X : OrderedType) (S : DepMap X) : DepMapFacts(X) with Definition key := X.t.
Include S.
Definition eq {A : Type} dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂) := forall x, find x m₁ = find x m₂.
Instance eq_refl : forall A dom, Reflexive (@eq A dom dom).
Proof.
repeat intro.
reflexivity.
Instance eq_equiv : forall A dom, Equivalence (@eq A dom dom).
Proof.
unfold eq.
split.
+
intros ?.
reflexivity.
+
intros ? ? Heq ?.
rewrite Heq.
reflexivity.
+
intros ? ? ? Heq₁ Heq₂ ?.
rewrite Heq₁, Heq₂.
reflexivity.
Definition incl {A : Type} dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂) := forall x v, find x m₁ = Some v -> find x m₂ = Some v.
Instance incl_refl : forall A dom (m : t A dom), Reflexive (@incl A dom dom).
Proof.
repeat intro.
assumption.
Instance incl_preorder : forall A dom, PreOrder (@incl A dom dom).
Proof.
split.
+
repeat intro; assumption.
+
intros ? ? ? Hle₁ Hle₂ ? ? ?.
now apply Hle₂, Hle₁.
Instance eq_incl_compat : forall A dom, PartialOrder (@eq A dom dom) (@incl A dom dom).
Proof.
intros A dom m₁ m₂.
split; intro Heq.
+
split; intros x v Hin.
-
now rewrite <- Heq.
-
now rewrite Heq.
+
intro x.
destruct (find x m₁) as [v₁ |] eqn:Hin₁, (find x m₂) as [v₂ |] eqn:Hin₂.
-
apply Heq in Hin₁.
rewrite Hin₁ in Hin₂.
assumption.
-
apply Heq in Hin₁.
rewrite Hin₁ in Hin₂.
discriminate Hin₂.
-
apply Heq in Hin₂.
rewrite Hin₂ in Hin₁.
discriminate Hin₁.
-
reflexivity.
Instance mem_compat (A : Type) dom : Proper (X.eq ==> @eq A dom dom ==> Logic.eq) (@mem A dom).
Proof.
intros x y Hxy m₁ m₂ Heq.
destruct (mem y m₂) eqn:Hmem.
+
rewrite mem_spec in *.
destruct Hmem as [v Hmem].
exists v.
rewrite Heq.
now rewrite (find_elt_compat _ Hxy).
+
destruct (mem x m₁) eqn:Hmem'; trivial.
rewrite mem_spec in *.
destruct Hmem' as [v Hmem'].
rewrite Heq, (find_elt_compat _ Hxy) in Hmem'.
assert (Hex : exists v, find y m₂ = Some v) by now exists v.
rewrite <- mem_spec, Hmem in Hex.
discriminate Hex.
Instance find_compat2 (A : Type) dom : Proper (X.eq ==> @eq A dom dom ==> Logic.eq) (@find A dom).
Proof.
repeat intro.
apply find_compat; assumption.
Arguments set {A} {dom} x v m _.
Instance set_compat2 (A : Type) x dom : Proper (Logic.eq ==> @eq A dom dom ==> full_relation ==> @eq A dom dom) (@set A dom x).
Proof.
do 9 intro.
subst.
apply set_compat; trivial; reflexivity.
Instance add_compat2 (A : Type) x dom : Proper (Logic.eq ==> @eq A dom dom ==> @eq A (Dom.add x dom) (Dom.add x dom)) (@add A dom x).
Proof.
do 6 intro.
subst.
apply add_compat; auto.
reflexivity.
Instance remove_compat2 (A : Type) x dom : Proper (@eq A dom dom ==> @eq A (Dom.remove x dom) (Dom.remove x dom)) (@remove A dom x).
Proof.
repeat intro.
apply remove_compat; auto.
reflexivity.
Definition for_all {A : Type} (f : key -> A -> bool) dom (m : t A dom) := fold (fun x v b => b && f x v) m true.
Definition exists_ {A : Type} (f : key -> A -> bool) dom (m : t A dom) := fold (fun x v b => b || f x v) m false.
End DepMapFactsOn.

Instance eq_refl : forall A dom, Reflexive (@eq A dom dom).
Proof.
repeat intro.
Admitted.

Lemma eq_sym : forall A dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂), eq m₁ m₂ -> eq m₂ m₁.
Proof.
intros * Heq x.
rewrite Heq.
Admitted.

Lemma eq_trans : forall A dom₁ dom₂ dom3 (m₁ : t A dom₁) (m₂ : t A dom₂) (m3 : t A dom3), eq m₁ m₂ -> eq m₂ m3 -> eq m₁ m3.
Proof.
intros * Heq₁ Heq₂ x.
rewrite Heq₁, Heq₂.
Admitted.

Instance eq_equiv : forall A dom, Equivalence (@eq A dom dom).
Proof.
unfold eq.
split.
+
intros ?.
reflexivity.
+
intros ? ? Heq ?.
rewrite Heq.
reflexivity.
+
intros ? ? ? Heq₁ Heq₂ ?.
rewrite Heq₁, Heq₂.
Admitted.

Instance incl_refl : forall A dom (m : t A dom), Reflexive (@incl A dom dom).
Proof.
repeat intro.
Admitted.

Lemma incl_trans : forall A dom₁ dom₂ dom3 (m₁ : t A dom₁) (m₂ : t A dom₂) (m3 : t A dom3), incl m₁ m₂ -> incl m₂ m3 -> incl m₁ m3.
Proof.
repeat intro.
Admitted.

Instance incl_preorder : forall A dom, PreOrder (@incl A dom dom).
Proof.
split.
+
repeat intro; assumption.
+
intros ? ? ? Hle₁ Hle₂ ? ? ?.
Admitted.

Instance eq_incl_compat : forall A dom, PartialOrder (@eq A dom dom) (@incl A dom dom).
Proof.
intros A dom m₁ m₂.
split; intro Heq.
+
split; intros x v Hin.
-
now rewrite <- Heq.
-
now rewrite Heq.
+
intro x.
destruct (find x m₁) as [v₁ |] eqn:Hin₁, (find x m₂) as [v₂ |] eqn:Hin₂.
-
apply Heq in Hin₁.
rewrite Hin₁ in Hin₂.
assumption.
-
apply Heq in Hin₁.
rewrite Hin₁ in Hin₂.
discriminate Hin₂.
-
apply Heq in Hin₂.
rewrite Hin₂ in Hin₁.
discriminate Hin₁.
-
Admitted.

Theorem find_compat : forall A x y dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂), X.eq x y -> eq m₁ m₂ -> find x m₁ = find y m₂.
Proof.
intros * Hxy Heq.
rewrite Heq.
apply find_elt_compat.
Admitted.

Instance find_compat2 (A : Type) dom : Proper (X.eq ==> @eq A dom dom ==> Logic.eq) (@find A dom).
Proof.
repeat intro.
Admitted.

Theorem set_compat : forall A x y v dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂) (Hin₁ : Dom.In x dom₁) (Hin₂ : Dom.In y dom₂), X.eq x y -> eq m₁ m₂ -> eq (set x v m₁ Hin₁) (set y v m₂ Hin₂).
Proof.
intros A x y v dom₁ dom₂ m₁ m₂ Hin₁ Hin₂ Hxy Hm z.
destruct (X.eq_dec z x) as [Hxz | Hxz].
+
rewrite Hxz.
rewrite Hxy at 3.
do 2 rewrite set_same.
reflexivity.
+
repeat rewrite set_other; auto.
rewrite <- Hxy.
Admitted.

Instance set_compat2 (A : Type) x dom : Proper (Logic.eq ==> @eq A dom dom ==> full_relation ==> @eq A dom dom) (@set A dom x).
Proof.
do 9 intro.
subst.
Admitted.

Theorem add_compat : forall A x y v dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂), X.eq x y -> eq m₁ m₂ -> eq (add x v m₁) (add y v m₂).
Proof.
intros ? x y * Hxy Heq z.
destruct (X.eq_dec z x) as [Hxz | Hxz].
+
rewrite Hxz.
rewrite Hxy at 4.
do 2 rewrite add_same.
reflexivity.
+
repeat rewrite add_other.
apply Heq.
now rewrite <- Hxy.
Admitted.

Instance add_compat2 (A : Type) x dom : Proper (Logic.eq ==> @eq A dom dom ==> @eq A (Dom.add x dom) (Dom.add x dom)) (@add A dom x).
Proof.
do 6 intro.
subst.
apply add_compat; auto.
Admitted.

Theorem remove_compat : forall A x y dom₁ dom₂ (m₁ : t A dom₁) (m₂ : t A dom₂), X.eq x y -> eq m₁ m₂ -> eq (remove x m₁) (remove y m₂).
Proof.
intros ? x y * Hxy Heq z.
destruct (X.eq_dec z x) as [Hxz | Hxz].
+
rewrite Hxz.
rewrite Hxy at 4.
do 2 rewrite remove_same.
reflexivity.
+
repeat rewrite remove_other.
apply Heq.
now rewrite <- Hxy.
Admitted.

Instance remove_compat2 (A : Type) x dom : Proper (@eq A dom dom ==> @eq A (Dom.remove x dom) (Dom.remove x dom)) (@remove A dom x).
Proof.
repeat intro.
apply remove_compat; auto.
Admitted.

Theorem find_None : forall A dom x (m : t A dom), find x m = None <-> ¬Dom.In x dom.
Proof.
intros.
rewrite <- (find_spec x m).
destruct (find x m).
+
split; intro Hfind.
discriminate Hfind.
elim Hfind.
eexists; reflexivity.
+
split; intro Hfind.
intros [? Habs].
discriminate Habs.
Admitted.

Corollary find_dom : forall A x v dom (m : t A dom), find x m = Some v -> Dom.In x dom.
Proof.
intros.
rewrite <- find_spec.
Admitted.

Theorem set_Some : forall A x y v u dom (m : t A dom) (Hin : Dom.In x dom), find y (set x v m Hin) = Some u <-> X.eq y x ∧ u = v ∨ ¬X.eq y x ∧ find y m = Some u.
Proof.
intros A x y v u dom m Hin.
destruct (X.eq_dec y x) as [Hxy | Hxy].
+
rewrite Hxy.
rewrite set_same.
split; intro Heq.
-
left.
inversion Heq.
split; reflexivity.
-
destruct Heq as [[_ Heq] | [Habs _]].
now subst.
now elim Habs.
+
rewrite set_other; trivial.
split; intro Heq.
-
right.
split; assumption.
-
destruct Heq as [[Habs _] | [_ Heq]].
contradiction.
Admitted.

Theorem set_None : forall A x y v dom (m : t A dom) (Hin : Dom.In x dom), find y (set x v m Hin) = None <-> ¬X.eq y x ∧ find y m = None.
Proof.
intros A x y v dom m Hdom.
destruct (X.eq_dec y x) as [Hxy | Hxy].
+
rewrite Hxy, set_same.
split; intro Hin.
-
discriminate Hin.
-
destruct Hin as [Hin _].
now elim Hin.
+
rewrite set_other; trivial.
Admitted.

Theorem add_Some : forall A x y v u dom (m : t A dom), find y (add x v m) = Some u <-> X.eq y x ∧ u = v ∨ ¬X.eq y x ∧ find y m = Some u.
Proof.
intros A x y v u dom m.
destruct (X.eq_dec y x) as [Hxy | Hxy].
+
rewrite Hxy.
rewrite add_same.
split; intro Heq.
-
left.
inversion Heq.
split; reflexivity.
-
destruct Heq as [[_ Heq] | [Habs _]].
now subst.
now elim Habs.
+
rewrite add_other; trivial.
split; intro Heq.
-
right.
split; assumption.
-
destruct Heq as [[Habs _] | [_ Heq]].
contradiction.
Admitted.

Theorem add_None : forall A x y v dom (m : t A dom), find y (add x v m) = None <-> ¬X.eq y x ∧ find y m = None.
Proof.
intros A x y v dom m.
destruct (X.eq_dec y x) as [Hxy | Hxy].
+
rewrite Hxy, add_same.
split; intro Hin.
-
discriminate Hin.
-
destruct Hin as [Hin _].
now elim Hin.
+
rewrite add_other; trivial.
Admitted.

Theorem remove_Some : forall A x y u dom (m : t A dom), find y (remove x m) = Some u <-> ¬X.eq y x ∧ find y m = Some u.
Proof.
intros A x y u dom m.
destruct (X.eq_dec y x) as [Hxy | Hxy].
+
rewrite Hxy, remove_same.
split; intro Hin.
-
discriminate Hin.
-
destruct Hin as [Hin _].
now elim Hin.
+
rewrite remove_other; trivial.
Admitted.

Theorem remove_None : forall A x y dom (m : t A dom), find y (remove x m) = None <-> X.eq y x ∨ find y m = None.
Proof.
intros A x y dom m.
destruct (X.eq_dec y x) as [Hxy | Hxy].
+
rewrite Hxy.
rewrite remove_same.
split; intro Heq; try left; reflexivity.
+
rewrite remove_other; trivial.
split; intro Heq.
-
right.
assumption.
-
destruct Heq.
contradiction.
Admitted.

Theorem add_cancel : forall A x v dom (m : t A dom), find x m = Some v -> eq (add x v m) m.
Proof.
intros A x v dom m Heq y.
destruct (X.eq_dec y x) as [Hxy | Hxy].
+
rewrite Hxy, add_same, Heq.
reflexivity.
+
Admitted.

Theorem remove_cancel : forall A x dom (m : t A dom), find x m = None -> eq (remove x m) m.
Proof.
intros A x dom m Heq y.
destruct (X.eq_dec y x) as [Hxy | Hxy].
+
rewrite Hxy, remove_same, Heq.
reflexivity.
+
Admitted.

Theorem add_merge : forall A x v₁ v₂ dom (m : t A dom), eq (add x v₂ (add x v₁ m)) (add x v₂ m).
Proof.
intros A x v₁ v₂ dom m y.
destruct (X.eq_dec y x) as [Hxy | Hxy].
+
rewrite Hxy, add_same, add_same.
reflexivity.
+
Admitted.

Theorem add_comm : forall A x y v₁ v₂ dom (m : t A dom), ¬X.eq x y -> eq (add y v₂ (add x v₁ m)) (add x v₁ (add y v₂ m)).
Proof.
intros A x y v₁ v₂ dom m Hxy z.
destruct (X.eq_dec z x) as [Hxz | Hxz].
+
rewrite Hxz, add_same, add_other, add_same; trivial.
+
destruct (X.eq_dec z y) as [Hyz | Hyz].
-
rewrite Hyz, add_same, add_other, add_same; trivial.
rewrite <- Hyz.
assumption.
-
Admitted.

Instance mem_compat (A : Type) dom : Proper (X.eq ==> @eq A dom dom ==> Logic.eq) (@mem A dom).
Proof.
intros x y Hxy m₁ m₂ Heq.
destruct (mem y m₂) eqn:Hmem.
+
rewrite mem_spec in *.
destruct Hmem as [v Hmem].
exists v.
rewrite Heq.
now rewrite (find_elt_compat _ Hxy).
+
destruct (mem x m₁) eqn:Hmem'; trivial.
rewrite mem_spec in *.
destruct Hmem' as [v Hmem'].
rewrite Heq, (find_elt_compat _ Hxy) in Hmem'.
assert (Hex : exists v, find y m₂ = Some v) by now exists v.
rewrite <- mem_spec, Hmem in Hex.
discriminate Hex.
