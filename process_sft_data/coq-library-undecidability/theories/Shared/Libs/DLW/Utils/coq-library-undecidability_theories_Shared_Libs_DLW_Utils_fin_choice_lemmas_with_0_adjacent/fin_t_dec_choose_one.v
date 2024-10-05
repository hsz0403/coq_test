Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat fin_base.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
Set Implicit Arguments.
Fact list_reif_t X Y (R : X -> Y -> Prop) l : (forall x, In x l -> sig (R x)) -> { f | forall x (Hx : In x l), R x (f x Hx) }.
Proof.
apply constructive_dep_choice.
Fact pos_reif_t X n (R : pos n -> X -> Prop) : (forall p, { x | R p x }) -> { f | forall p, R p (f p) }.
Proof.
apply constructive_choice.
Fact vec_reif_t X n (R : pos n -> X -> Prop) : (forall p, sig (R p)) -> { v | forall p, R p (vec_pos v p) }.
Proof.
intros H.
apply pos_reif_t in H.
destruct H as (f & Hf).
exists (vec_set_pos f).
intro; rewrite vec_pos_set; trivial.
Section finite_discrete_choice.
Variable (X Y : Type) (R : X -> Y -> Prop) (X_discrete : forall x y : X, { x = y } + { x <> y }).
Fact finite_discrete_choice : finite X -> (forall x, ex (R x)) -> exists f, forall x, R x (f x).
Proof.
intros (l & Hl) H.
destruct list_discrete_choice with (l := l) as (f & Hf); auto.
exists (fun x => f x (Hl x)); auto.
End finite_discrete_choice.
Local Hint Resolve finite_t_pos finite_t_finite : core.
Fact pos_reification X n (R : pos n -> X -> Prop) : (forall p, exists x, R p x) -> exists f, forall p, R p (f p).
Proof.
apply finite_discrete_choice; auto.
apply pos_eq_dec.
Notation pos_reif := pos_reification.
Fact vec_reif X n (R : pos n -> X -> Prop) : (forall p, ex (R p)) -> exists v, forall p, R p (vec_pos v p).
Proof.
intros H.
apply pos_reification in H.
destruct H as (f & Hf).
exists (vec_set_pos f).
intro; rewrite vec_pos_set; trivial.
Section finite_t_dec_choose_one.
Variable (X : Type) (P Q : X -> Prop) (HX : finite_t X) (HQ : fin_t Q) (Pdec : forall x, { P x } + { ~ P x }).
Fact list_dec_choose_one l : (exists x, In x l /\ P x) -> { x | In x l /\ P x }.
Proof.
clear HX Q HQ.
induction l as [ | x l IHl ]; intros H.
+
exfalso; destruct H as (_ & [] & _).
+
destruct (Pdec x) as [ H1 | H1 ].
*
exists x; simpl; auto.
*
destruct IHl as (y & H2 & H3).
-
destruct H as (y & [ -> | Hy ] & ?); firstorder.
-
exists y; simpl; auto.
Fact fin_t_dec_choose_one : (exists x, Q x /\ P x) -> { x | Q x /\ P x }.
Proof.
revert HQ; intros (l & Hl) H.
destruct (list_dec_choose_one l) as (x & H1 & H2).
+
destruct H as (x & ? & ?); exists x; rewrite <- Hl; auto.
+
exists x; rewrite Hl; auto.
Fact finite_t_dec_choose_one : ex P -> sig P.
Proof.
clear Q HQ.
revert HX; intros (l & Hl) H.
destruct (list_dec_choose_one l) as (x & H1 & H2); firstorder.
End finite_t_dec_choose_one.
Definition finite_t_dec_choice X Y (R : X -> Y -> Prop) : finite_t Y -> (forall x y, { R x y } + { ~ R x y }) -> (forall x, ex (R x)) -> { f | forall x, R x (f x) }.
Proof.
intros H2 H1 H3.
exists (fun x => proj1_sig (finite_t_dec_choose_one H2 (H1 x) (H3 x))).
intros x; apply (proj2_sig (finite_t_dec_choose_one H2 (H1 x) (H3 x))).
Fact pos_dec_reif n (P : pos n -> Prop) (HP : forall p, { P p } + { ~ P p }) : ex P -> sig P.
Proof.
apply finite_t_dec_choose_one; auto.
Fact pos_dec_rel2fun n (R : pos n -> pos n -> Prop) : (forall a b, { R a b } + { ~ R a b }) -> (forall p, ex (R p)) -> { f | forall p, R p (f p) }.
Proof.
apply finite_t_dec_choice; auto.

Fact fin_t_dec_choose_one : (exists x, Q x /\ P x) -> { x | Q x /\ P x }.
Proof.
revert HQ; intros (l & Hl) H.
destruct (list_dec_choose_one l) as (x & H1 & H2).
+
destruct H as (x & ? & ?); exists x; rewrite <- Hl; auto.
+
exists x; rewrite Hl; auto.
