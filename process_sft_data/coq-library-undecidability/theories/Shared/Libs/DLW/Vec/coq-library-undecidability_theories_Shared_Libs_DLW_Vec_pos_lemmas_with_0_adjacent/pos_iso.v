Require Import List Arith Lia.
Require Fin.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils.
Set Implicit Arguments.
Notation pos := Fin.t.
Notation pos_fst := Fin.F1.
Notation pos_nxt := Fin.FS.
Notation pos0 := (@pos_fst _).
Notation pos1 := (pos_nxt pos0).
Notation pos2 := (pos_nxt pos1).
Notation pos3 := (pos_nxt pos2).
Notation pos4 := (pos_nxt pos3).
Notation pos5 := (pos_nxt pos4).
Notation pos6 := (pos_nxt pos5).
Notation pos7 := (pos_nxt pos6).
Notation pos8 := (pos_nxt pos7).
Notation pos9 := (pos_nxt pos8).
Notation pos10 := (pos_nxt pos9).
Notation pos11 := (pos_nxt pos10).
Notation pos12 := (pos_nxt pos11).
Notation pos13 := (pos_nxt pos12).
Notation pos14 := (pos_nxt pos13).
Notation pos15 := (pos_nxt pos14).
Notation pos16 := (pos_nxt pos15).
Notation pos17 := (pos_nxt pos16).
Notation pos18 := (pos_nxt pos17).
Notation pos19 := (pos_nxt pos18).
Notation pos20 := (pos_nxt pos19).
Definition pos_iso n m : n = m -> pos n -> pos m.
Proof.
intros []; auto.
Defined.
Section pos_inv.
Let pos_inv_t n := match n as x return pos x -> Set with | 0 => fun _ => False | S n => fun i => (( i = pos_fst ) + { p | i = pos_nxt p })%type end.
Let pos_inv : forall n p, @pos_inv_t n p.
Proof.
intros _ [ | n p ]; simpl; [ left | right ]; auto; exists p; auto.
Defined.
Definition pos_O_inv : pos 0 -> False.
Proof.
apply pos_inv.
Defined.
Definition pos_S_inv n (p : pos (S n)) : ( p = pos_fst ) + { q | p = pos_nxt q }.
Proof.
apply (pos_inv p).
Defined.
Definition pos_nxt_inj n (p q : pos n) (H : pos_nxt p = pos_nxt q) : p = q := match H in _ = a return match a as a' in pos m return match m with | 0 => Prop | S n' => pos n' -> Prop end with | pos_fst => fun _ => True | pos_nxt y => fun x' => x' = y end p with | eq_refl => eq_refl end.
End pos_inv.
Arguments pos_S_inv {n} p /.
Section pos_invert.
Let pos_invert_t n : (pos n -> Type) -> Type := match n with 0 => fun P => True | S n => fun P => (P (pos_fst) * forall p, P (pos_nxt p))%type end.
Let pos_invert n : forall (P : pos n -> Type), pos_invert_t P -> forall p, P p.
Proof.
intros P HP; induction p; simpl in HP; apply HP.
Defined.
Definition pos_eq_dec n (x y : pos n) : { x = y } + { x <> y }.
Proof.
revert n x y.
induction x as [ x | n x IH ]; intros y; invert pos y.
1: left; trivial.
1,2: right; discriminate.
destruct (IH y) as [ | C ].
+
left; subst; trivial.
+
right; contradict C; revert C; apply pos_nxt_inj.
Defined.
Fixpoint pos_left n m (p : pos n) : pos (n+m) := match p with | pos_fst => pos_fst | pos_nxt p => pos_nxt (pos_left m p) end.
Fixpoint pos_right n m : pos m -> pos (n+m) := match n with | 0 => fun x => x | S n => fun p => pos_nxt (pos_right n p) end.
Definition pos_both n m : pos (n+m) -> pos n + pos m.
Proof.
induction n as [ | n IHn ]; intros p.
+
right; exact p.
+
simpl in p; pos_inv p.
*
left; apply pos_fst.
*
destruct (IHn p) as [ a | b ].
-
left; apply (pos_nxt a).
-
right; apply b.
Defined.
Definition pos_lr n m : pos n + pos m -> pos (n+m).
Proof.
intros [ p | p ]; revert p.
+
apply pos_left.
+
apply pos_right.
Defined.
Fact pos_both_left n m p : @pos_both n m (@pos_left n m p) = inl p.
Proof.
induction p as [ | n p IHp ]; simpl; auto.
rewrite IHp; auto.
Fact pos_both_right n m p : @pos_both n m (@pos_right n m p) = inr p.
Proof.
revert p; induction n as [ | n IHn]; intros p; simpl; auto.
rewrite IHn; auto.
Fact pos_both_lr n m p : @pos_both n m (pos_lr p) = p.
Proof.
destruct p as [ p | p ].
+
apply pos_both_left.
+
apply pos_both_right.
Fact pos_lr_both n m p : pos_lr (@pos_both n m p) = p.
Proof.
revert p; induction n as [ | n IHn ]; intros p; auto.
simpl in p; pos_inv p; simpl; auto.
specialize (IHn p).
destruct (pos_both n m p); simpl in *; f_equal; auto.
Section pos_left_right_rect.
Variable (n m : nat) (P : pos (n+m) -> Type).
Hypothesis (HP1 : forall p, P (pos_left _ p)) (HP2 : forall p, P (pos_right _ p)).
End pos_left_right_rect.
Fixpoint pos_list n : list (pos n) := match n with | 0 => nil | S n => pos0::map pos_nxt (pos_list n) end.
Fact pos_list_prop n p : In p (pos_list n).
Proof.
induction p as [ | n p Hp ].
left; auto.
simpl; right.
apply in_map_iff.
exists p; auto.
Fact pos_list_length n : length (pos_list n) = n.
Proof.
induction n; simpl; auto.
rewrite map_length; f_equal; auto.
Section pos_map.
Definition pos_map m n := pos m -> pos n.
Definition pm_ext_eq m n (r1 r2 : pos_map m n) := forall p, r1 p = r2 p.
Definition pm_lift m n (r : pos_map m n) : pos_map (S m) (S n).
Proof.
intros p.
invert pos p.
apply pos_fst.
apply pos_nxt, (r p).
Defined.
Fact pm_lift_fst m n (r : pos_map m n) : pm_lift r pos0 = pos0.
Proof.
auto.
Fact pm_lift_nxt m n (r : pos_map m n) p : pm_lift r (pos_nxt p) = pos_nxt (r p).
Proof.
auto.
Arguments pm_lift [ m n ] r p.
Fact pm_lift_ext m n r1 r2 : @pm_ext_eq m n r1 r2 -> pm_ext_eq (pm_lift r1) (pm_lift r2).
Proof.
intros H12 p; unfold pm_lift.
invert pos p; simpl; auto.
f_equal; apply H12.
Definition pm_comp l m n : pos_map l m -> pos_map m n -> pos_map l n.
Proof.
intros H1 H2 p.
exact (H2 (H1 p)).
Defined.
Fact pm_comp_lift l m n r s : pm_ext_eq (pm_lift (@pm_comp l m n r s)) (pm_comp (pm_lift r) (pm_lift s)).
Proof.
intros p.
unfold pm_comp, pm_lift; simpl.
invert pos p; simpl; auto.
Definition pm_id n : pos_map n n := fun p => p.
End pos_map.
Arguments pm_lift { m n } _ _ /.
Arguments pm_comp [ l m n ] _ _ _ /.
Arguments pm_id : clear implicits.
Section pos_nat.
Fixpoint pos_nat n (p : pos n) : { i | i < n }.
Proof.
refine (match p with | pos_fst => exist _ 0 _ | pos_nxt q => exist _ (S (proj1_sig (pos_nat _ q))) _ end).
apply lt_O_Sn.
apply lt_n_S, (proj2_sig (pos_nat _ q)).
Defined.
Definition pos2nat n p := proj1_sig (@pos_nat n p).
Fact pos2nat_prop n p : @pos2nat n p < n.
Proof.
apply (proj2_sig (pos_nat p)).
Fixpoint nat2pos n : forall x, x < n -> pos n.
Proof.
refine (match n as n' return forall x, x < n' -> pos n' with | O => fun x H => _ | S i => fun x H => _ end).
exfalso; revert H; apply lt_n_O.
destruct x as [ | x ].
apply pos_fst.
apply pos_nxt.
apply (nat2pos i x); revert H; apply lt_S_n.
Defined.
Definition nat_pos n : { i | i < n } -> pos n.
Proof.
intros (? & H); revert H; apply nat2pos.
Defined.
Arguments pos2nat n !p /.
Fact pos2nat_inj n (p q : pos n) : pos2nat p = pos2nat q -> p = q.
Proof.
revert q.
induction p as [ n | n p IHp ]; intros q; invert pos q; simpl; auto; try discriminate 1.
intros H; f_equal; apply IHp; injection H; trivial.
Fact pos2nat_nat2pos n i (H : i < n) : pos2nat (nat2pos H) = i.
Proof.
revert i H; induction n as [ | n IHn ]; intros [ | i ] H; simpl; auto; try lia.
f_equal.
apply IHn.
Fact nat2pos_pos2nat n p (H : pos2nat p < n) : nat2pos H = p.
Proof.
apply pos2nat_inj; rewrite pos2nat_nat2pos; auto.
Fact pos2nat_fst n : pos2nat (@pos_fst n) = 0.
Proof.
auto.
Fact pos2nat_nxt n p : pos2nat (@pos_nxt n p) = S (pos2nat p).
Proof.
auto.
Fact pos2nat_left n m p : pos2nat (@pos_left n m p) = pos2nat p.
Proof.
induction p; simpl; auto.
Fact pos2nat_right n m p : pos2nat (@pos_right n m p) = n+pos2nat p.
Proof.
revert m p; induction n as [ | n IHn ]; intros m p; auto.
simpl pos_right; simpl plus; rewrite pos2nat_nxt; f_equal; auto.
Fixpoint pos_sub n (p : pos n) { struct p } : forall m, n < m -> pos m.
Proof.
destruct p as [ | n p ]; intros [ | m ] Hm.
exfalso; clear pos_sub; abstract lia.
apply pos_fst.
exfalso; clear pos_sub; abstract lia.
apply pos_nxt.
apply (pos_sub n p), lt_S_n, Hm.
Defined.
Fact pos_sub2nat n p m Hm : pos2nat (@pos_sub n p m Hm) = pos2nat p.
Proof.
revert m Hm; induction p as [ n | n p IH ]; intros [ | m ] Hm; try lia.
simpl; auto.
simpl pos_sub; repeat rewrite pos2nat_nxt; f_equal; auto.
End pos_nat.
Global Opaque pos_nat.
Fact pos_list2nat n : map (@pos2nat n) (pos_list n) = list_an 0 n.
Proof.
induction n as [ | n IHn ]; simpl; f_equal.
rewrite <- (map_S_list_an 0), <- IHn.
do 2 rewrite map_map.
apply map_ext.
intros; rewrite pos2nat_nxt; auto.
Section pos_prod.
Variable n : nat.
Let ll := flat_map (fun p => map (fun q => (p,q)) (pos_list n)) (pos_list n).
Let ll_prop p q : In (p,q) ll.
Proof.
apply in_flat_map; exists p; split.
apply pos_list_prop.
apply in_map_iff.
exists q; split; auto.
apply pos_list_prop.
Definition pos_not_diag := filter (fun c => if pos_eq_dec (fst c) (snd c) then false else true) ll.
Fact pos_not_diag_spec p q : In (p,q) pos_not_diag <-> p <> q.
Proof.
unfold pos_not_diag.
rewrite filter_In; simpl.
destruct (pos_eq_dec p q).
split.
intros (_ & ?); discriminate.
intros []; auto.
split; try tauto; split; auto.
End pos_prod.

Definition pos_iso n m : n = m -> pos n -> pos m.
Proof.
intros []; auto.
