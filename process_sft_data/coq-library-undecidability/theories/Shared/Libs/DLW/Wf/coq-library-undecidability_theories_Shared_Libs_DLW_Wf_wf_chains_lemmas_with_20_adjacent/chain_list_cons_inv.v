Require Import Arith List Lia.
Set Implicit Arguments.
Section wf_chains.
Variables (X : Type) (R : X -> X -> Prop).
Inductive chain : nat -> X -> X -> Prop := | in_chain_0 : forall x, chain 0 x x | in_chain_1 : forall n x y z, R x y -> chain n y z -> chain (S n) x z.
Hint Constructors chain : core.
Fact chain_inv_0 x y : chain 0 x y -> x = y.
Proof.
inversion 1; auto.
Fact chain_inv_S n x y : chain (S n) x y -> exists z, R x z /\ chain n z y.
Proof.
inversion 1; exists y0; auto.
Fact chain_plus a b x y z : chain a x y -> chain b y z -> chain (a+b) x z.
Proof.
induction 1 as [ | ? ? y ].
+
simpl; auto.
+
intros.
simpl.
constructor 2 with y.
*
auto.
*
auto.
Fact chain_plus_inv a b x z : chain (a+b) x z -> exists y, chain a x y /\ chain b y z.
Proof.
revert x; induction a as [ | a IHa ]; intros x; simpl.
+
exists x; split; auto.
+
intros H.
apply chain_inv_S in H.
destruct H as (y & H1 & H2).
specialize (IHa _ H2).
destruct IHa as (k & ? & ?).
exists k; split; auto.
constructor 2 with y; auto.
Fact chain_snoc_inv n x z : chain (S n) x z -> exists y, chain n x y /\ R y z.
Proof.
replace (S n) with (n+1) by lia.
intros H; apply chain_plus_inv in H.
destruct H as (y & H1 & H2).
exists y; split; auto.
apply chain_inv_S in H2.
destruct H2 as (k & H2 & H3).
apply chain_inv_0 in H3; subst; auto.
Inductive chain_list : list X -> X -> X -> Prop := | in_chain_list_0 : forall x, chain_list nil x x | in_chain_list_1 : forall x l y z, R x y -> chain_list l y z -> chain_list (x::l) x z.
Fact chain_chain_list n x y : chain n x y -> exists l, chain_list l x y /\ n = length l.
Proof.
induction 1 as [ x | n x y z H1 _ (l & H2 & H3) ]; auto.
+
exists nil; simpl; split; auto; constructor.
+
exists (x::l); simpl; split; auto; constructor 2 with y; auto.
Fact chain_list_chain l x y : chain_list l x y -> chain (length l) x y.
Proof.
induction 1 as [ ? | ? ? y ]; simpl; try constructor.
constructor 2 with y; auto.
Fact chain_list_app l x y m z : chain_list l x y -> chain_list m y z -> chain_list (l++m) x z.
Proof.
induction 1 as [ | l x y ]; simpl; auto.
constructor 2 with y; auto.
Hypothesis (HR : forall x, exists k, forall n y, chain n y x -> n <= k).
End wf_chains.

Fact chain_inv_0 x y : chain 0 x y -> x = y.
Proof.
Admitted.

Fact chain_inv_S n x y : chain (S n) x y -> exists z, R x z /\ chain n z y.
Proof.
Admitted.

Fact chain_plus a b x y z : chain a x y -> chain b y z -> chain (a+b) x z.
Proof.
induction 1 as [ | ? ? y ].
+
simpl; auto.
+
intros.
simpl.
constructor 2 with y.
*
auto.
*
Admitted.

Corollary chain_snoc n x y z : chain n x y -> R y z -> chain (S n) x z.
Proof.
intros H1 H2.
replace (S n) with (n+1) by lia.
apply chain_plus with y; auto.
Admitted.

Fact chain_plus_inv a b x z : chain (a+b) x z -> exists y, chain a x y /\ chain b y z.
Proof.
revert x; induction a as [ | a IHa ]; intros x; simpl.
+
exists x; split; auto.
+
intros H.
apply chain_inv_S in H.
destruct H as (y & H1 & H2).
specialize (IHa _ H2).
destruct IHa as (k & ? & ?).
exists k; split; auto.
Admitted.

Fact chain_snoc_inv n x z : chain (S n) x z -> exists y, chain n x y /\ R y z.
Proof.
replace (S n) with (n+1) by lia.
intros H; apply chain_plus_inv in H.
destruct H as (y & H1 & H2).
exists y; split; auto.
apply chain_inv_S in H2.
destruct H2 as (k & H2 & H3).
Admitted.

Fact chain_chain_list n x y : chain n x y -> exists l, chain_list l x y /\ n = length l.
Proof.
induction 1 as [ x | n x y z H1 _ (l & H2 & H3) ]; auto.
+
exists nil; simpl; split; auto; constructor.
+
Admitted.

Fact chain_list_chain l x y : chain_list l x y -> chain (length l) x y.
Proof.
induction 1 as [ ? | ? ? y ]; simpl; try constructor.
Admitted.

Fact chain_list_app l x y m z : chain_list l x y -> chain_list m y z -> chain_list (l++m) x z.
Proof.
induction 1 as [ | l x y ]; simpl; auto.
Admitted.

Lemma chain_list_inv l x y : chain_list l x y -> l = nil /\ x = y \/ exists k l', l = x::l' /\ R x k /\ chain_list l' k y.
Proof.
Admitted.

Corollary chain_list_nil_inv x y : chain_list nil x y -> x = y.
Proof.
intros H; apply chain_list_inv in H.
Admitted.

Lemma chain_list_app_inv l m x z : chain_list (l++m) x z -> exists y, chain_list l x y /\ chain_list m y z.
Proof.
revert x; induction l as [ | a l IHl ]; intros x.
+
exists x; simpl; split; auto; constructor.
+
simpl; intros H; apply chain_list_cons_inv in H.
destruct H as (-> & b & H1 & H2).
apply IHl in H2; destruct H2 as (y & H2 & H3).
Admitted.

Lemma Acc_chains k x : (forall n y, chain n y x -> n <= k) -> Acc R x.
Proof.
revert x.
induction k as [ | k IHk ]; intros x Hx.
+
constructor 1; intros y Hy.
assert (chain 1 y x) as C.
{
constructor 2 with x.
+
trivial.
+
constructor 1.
}
apply Hx in C; lia.
+
constructor 1; intros y Hy.
apply IHk; intros n z Hn.
apply le_S_n.
apply (Hx _ z).
Admitted.

Theorem wf_chains : well_founded R.
Proof.
intros x.
destruct (HR x) as (k & Hk).
Admitted.

Corollary chain_list_cons_inv x l y z : chain_list (x::l) y z -> x = y /\ exists k, R x k /\ chain_list l k z.
Proof.
intros H.
apply chain_list_inv in H.
destruct H as [ (? & _) | (k & l' & H & ? & ?) ]; try discriminate.
inversion H; firstorder.
