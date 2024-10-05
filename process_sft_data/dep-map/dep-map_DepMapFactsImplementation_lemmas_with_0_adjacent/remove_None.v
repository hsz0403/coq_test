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
assumption.
