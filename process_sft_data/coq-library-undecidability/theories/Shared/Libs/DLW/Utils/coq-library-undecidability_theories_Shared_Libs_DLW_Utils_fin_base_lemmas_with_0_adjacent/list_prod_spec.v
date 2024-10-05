Require Import List Arith Lia Eqdep_dec Bool.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
Set Implicit Arguments.
Section finite.
Definition finite_t X := { lX | forall x : X, In x lX }.
Definition finite X := exists lX, forall x : X, In x lX.
Fact finite_t_finite X : finite_t X -> finite X.
Proof.
intros (l & ?); exists l; auto.
Definition fin_t X (P : X -> Prop) := { l | forall x, P x <-> In x l }.
Definition fin X (P : X -> Prop) := exists l, forall x, P x <-> In x l.
Fact fin_t_fin X P : @fin_t X P -> fin P.
Proof.
intros (l & ?); exists l; auto.
Fact finite_t_fin_t_eq X : (finite_t X -> fin_t (fun _ : X => True)) * (fin_t (fun _ : X => True) -> finite_t X).
Proof.
split; intros (l & ?); exists l; firstorder.
Fact finite_fin_eq X : finite X <-> fin (fun _ : X => True).
Proof.
split; intros (l & ?); exists l; firstorder.
Fact fin_t_map X Y (f : X -> Y) (P Q : _ -> Prop) : (forall y, Q y <-> exists x, f x = y /\ P x) -> @fin_t X P -> @fin_t Y Q.
Proof.
intros H (lP & HP).
exists (map f lP).
intros x; rewrite in_map_iff, H.
firstorder.
Fact finite_t_map X Y (f : X -> Y) : (forall y, exists x, f x = y) -> finite_t X -> finite_t Y.
Proof.
intros H (l & Hl).
exists (map f l).
intros y.
destruct (H y) as (x & <-).
apply in_map_iff; exists x; auto.
Fact Forall_reif_t X l (P : X -> Prop) : Forall P l -> { m : list (sig P) | map (@proj1_sig _ _) m = l }.
Proof.
induction l as [ | x l IHl ].
+
exists nil; auto.
+
intros H; rewrite Forall_cons_inv in H.
destruct H as (H1 & H2).
destruct (IHl H2) as (m & Hm).
exists (exist _ x H1 :: m); simpl; f_equal; auto.
Fact fin_t_finite_t X (P : X -> Prop) (Pirr : forall x (H1 H2 : P x), H1 = H2) : fin_t P -> finite_t (sig P).
Proof.
intros (l & Hl).
destruct (@Forall_reif_t _ l P) as (m & Hm).
+
rewrite Forall_forall; intro; apply Hl.
+
exists m.
intros (x & Hx).
generalize Hx; intros H.
rewrite Hl, <- Hm, in_map_iff in Hx.
destruct Hx as (y & <- & Hy).
eq goal Hy; f_equal.
destruct y; simpl; f_equal; apply Pirr.
Fact fin_t_equiv X (P Q : X -> Prop) : (forall x, P x <-> Q x) -> fin_t P -> fin_t Q.
Proof.
intros H (l & Hl); exists l.
intro; rewrite <- H, Hl; tauto.
Fixpoint list_prod X Y (l : list X) (m : list Y) := match l with | nil => nil | x::l => map (fun y => (x,y)) m ++ list_prod l m end.
Fact list_prod_spec X Y l m c : In c (@list_prod X Y l m) <-> In (fst c) l /\ In (snd c) m.
Proof.
revert c; induction l as [ | x l IHl ]; intros c; simpl; try tauto.
rewrite in_app_iff, IHl, in_map_iff; simpl.
split.
+
intros [ (y & <- & ?) | (? & ?) ]; simpl; auto.
+
intros ([ -> | ] & ? ); destruct c; simpl; firstorder.
Fact fin_t_prod X Y (P Q : _ -> Prop) : @fin_t X P -> @fin_t Y Q -> fin_t (fun c => P (fst c) /\ Q (snd c)).
Proof.
intros (l & Hl) (m & Hm).
exists (list_prod l m); intro; rewrite list_prod_spec, Hl, Hm; tauto.
Fact finite_t_prod X Y : finite_t X -> finite_t Y -> finite_t (X*Y).
Proof.
intros (l & Hl) (m & Hm); exists (list_prod l m).
intros []; apply list_prod_spec; auto.
Fact finite_prod X Y : finite X -> finite Y -> finite (X*Y).
Proof.
intros (l & Hl) (m & Hm); exists (list_prod l m).
intros []; apply list_prod_spec; auto.
Fact fin_t_sum X Y (P Q : _ -> Prop) : @fin_t X P -> @fin_t Y Q -> fin_t (fun z : X + Y => match z with inl x => P x | inr y => Q y end).
Proof.
intros (l & Hl) (m & Hm).
exists (map inl l ++ map inr m).
intros z; rewrite in_app_iff, in_map_iff, in_map_iff.
destruct z as [ x | y ]; [ rewrite Hl | rewrite Hm ].
+
split.
*
left; exists x; auto.
*
intros [ (z & E & ?) | (z & C & _) ]; try discriminate; inversion E; subst; auto.
+
split.
*
right; exists y; auto.
*
intros [ (z & C & _) | (z & E & ?) ]; try discriminate; inversion E; subst; auto.
Fact finite_t_sum X Y : finite_t X -> finite_t Y -> finite_t (X+Y)%type.
Proof.
intros H1 H2.
apply finite_t_fin_t_eq in H1.
apply finite_t_fin_t_eq in H2.
apply finite_t_fin_t_eq.
generalize (fin_t_sum H1 H2).
apply fin_t_equiv.
intros []; tauto.
Fact finite_sum X Y : finite X -> finite Y -> finite (X+Y)%type.
Proof.
intros (l & Hl) (r & Hr).
exists (map inl l++map inr r).
intros []; apply in_app_iff; [ left | right ]; apply in_map; auto.
Fact finite_t_unit : finite_t unit.
Proof.
exists (tt::nil); intros []; simpl; auto.
Fact finite_unit : finite unit.
Proof.
apply finite_t_finite, finite_t_unit.
Fact finite_t_bool : finite_t bool.
Proof.
exists (true::false::nil); intros []; simpl; auto.
Fact finite_t_pos n : finite_t (pos n).
Proof.
exists (pos_list n); apply pos_list_prop.
Section filter.
Variable (X : Type) (P : X -> Prop) (Pdec : forall x, { P x } + { ~ P x }).
End filter.
Fact finite_t_fin_t_dec (X : Type) (P : X -> Prop) (Pdec : forall x, { P x } + { ~ P x }) : finite_t X -> fin_t P.
Proof.
intros H.
apply finite_t_fin_t_eq in H.
apply fin_t_dec with (1 := Pdec) in H.
revert H; apply fin_t_equiv; tauto.
End finite.

Fact list_prod_spec X Y l m c : In c (@list_prod X Y l m) <-> In (fst c) l /\ In (snd c) m.
Proof.
revert c; induction l as [ | x l IHl ]; intros c; simpl; try tauto.
rewrite in_app_iff, IHl, in_map_iff; simpl.
split.
+
intros [ (y & <- & ?) | (? & ?) ]; simpl; auto.
+
intros ([ -> | ] & ? ); destruct c; simpl; firstorder.
