Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils gcd pos vec subcode sss.
From Undecidability.MinskyMachines.MMA Require Import mma_defs.
Set Implicit Arguments.
Set Default Proof Using "Type".
Tactic Notation "rew" "length" := autorewrite with length_db.
Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).
Local Notation "P // s -[ k ]-> t" := (sss_steps (@mma_sss _) P k s t).
Local Notation "P // s -+> t" := (sss_progress (@mma_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mma_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@mma_sss _) P s).
Section Minsky_Machine_alt_utils.
Variable (n : nat).
Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.
Hint Resolve subcode_refl : core.
Section mma_jump.
Variable (j : nat) (x : pos n).
Definition mma_jump := INCₐ x :: DECₐ x j :: nil.
Notation JUMPₐ := mma_jump.
Fact mma_jump_length : length JUMPₐ = 2.
Proof.
auto.
Fact mma_jump_progress i v w : w = v -> (i,JUMPₐ) // (i,v) -+> (j,w).
Proof.
intros ->.
unfold mma_jump.
mma sss INC with x.
mma sss DEC S with x j (v#>x); rew vec.
mma sss stop.
End mma_jump.
Notation JUMPₐ := mma_jump.
Hint Rewrite mma_jump_length : length_db.
Section mma_null.
Variable (x : pos n) (i : nat).
Definition mma_null := DECₐ x i :: nil.
Fact mma_null_length : length mma_null = 1.
Proof.
auto.
Let mma_null_spec k v w : v#>x = k -> w = v[0/x] -> (i,mma_null) // (i,v) -+> (1+i,w).
Proof.
unfold mma_null.
revert v w.
induction k as [ | k IHk ]; intros v w H1 H2; subst w.
+
mma sss DEC 0 with x i.
mma sss stop; f_equal.
apply vec_pos_ext; intros z; dest z x.
+
mma sss DEC S with x i k.
apply sss_progress_compute.
apply IHk; rew vec.
Fact mma_null_progress v st : st = (1+i,v[0/x]) -> (i,mma_null) // (i,v) -+> st.
Proof.
intros; subst.
apply mma_null_spec with (1 := eq_refl); auto.
End mma_null.
Notation NULLₐ := mma_null.
Hint Rewrite mma_null_length : length_db.
Section mma_incs.
Variable (x : pos n).
Fixpoint mma_incs k := match k with | 0 => nil | S k => INCₐ x :: mma_incs k end.
Fact mma_incs_length k : length (mma_incs k) = k.
Proof.
induction k; simpl; f_equal; auto.
Fact mma_incs_compute k i v st : st = (k+i,v[(k+(v#>x))/x]) -> (i,mma_incs k) // (i,v) ->> st.
Proof.
revert i v st; induction k as [ | k IHk ]; intros i v st ?; subst.
+
mma sss stop; f_equal; auto.
apply vec_pos_ext; intros p; dest p x.
+
simpl; mma sss INC with x.
apply subcode_sss_compute with (P := (1+i,mma_incs k)); auto.
apply IHk; f_equal; try lia.
apply vec_pos_ext; intros p; dest p x.
End mma_incs.
Notation INCSₐ := mma_incs.
Hint Rewrite mma_incs_length : length_db.
Section mma_isempty.
Variable (x : pos n) (p i : nat).
Definition mma_isempty := DECₐ x (3+i) :: JUMPₐ p x ++ INCₐ x :: nil.
Notation EMPTYₐ := mma_isempty.
Fact mma_isempty_length : length EMPTYₐ = 4.
Proof.
auto.
Fact mma_empty_progress v st : st = (p,v) -> v#>x = 0 -> (i,EMPTYₐ) // (i,v) -+> st.
Proof.
intros -> H.
unfold mma_isempty, mma_jump; simpl app.
mma sss DEC 0 with x (3+i); rew vec.
mma sss INC with x.
mma sss DEC S with x p (0); rew vec.
mma sss stop; f_equal.
apply vec_pos_ext; intros y; dest y x; lia.
Fact mma_non_empty_progress v st : st = (4+i,v) -> v#>x <> 0 -> (i,EMPTYₐ) // (i,v) -+> st.
Proof.
intros -> H.
unfold mma_isempty.
case_eq (v#>x).
+
now intros; subst.
+
clear H; intros u H.
mma sss DEC S with x (3+i) u; rew vec.
mma sss INC with x; auto.
mma sss stop; f_equal.
apply vec_pos_ext; intros y; dest y x; lia.
End mma_isempty.
Notation EMPTYₐ := mma_isempty.
Hint Rewrite mma_isempty_length : length_db.
Section mma_transfert.
Variables (src dst : pos n) (Hsd : src <> dst) (i : nat).
Definition mma_transfert := INCₐ dst :: DECₐ src i :: DECₐ dst (3+i) :: nil.
Fact mma_transfert_length : length mma_transfert = 3.
Proof.
reflexivity.
Let mma_transfert_spec v w k x : v#>src = k -> v#>dst = x -> w = v[0/src][(1+k+x)/dst] -> (i,mma_transfert) // (i,v) -+> (2+i,w).
Proof.
unfold mma_transfert.
revert v w x.
induction k as [ | k IHk ]; intros v w x H1 H2 H3; subst w.
+
mma sss INC with dst.
mma sss DEC 0 with src i; rew vec.
mma sss stop; f_equal; auto.
apply vec_pos_ext; intros z; dest z dst; dest z src.
+
mma sss INC with dst.
mma sss DEC S with src i k; rew vec.
apply sss_progress_compute, IHk with (x := 1+x); rew vec.
apply vec_pos_ext; intros p.
dest p dst; try lia; dest p src.
Fact mma_transfert_progress v st : st = (3+i,v[0/src][((v#>src)+(v#>dst))/dst]) -> (i,mma_transfert) // (i,v) -+> st.
Proof using Hsd.
intros ?; subst.
apply sss_progress_trans with (2+i, v[0/src][(1+(v#>src)+(v#>dst))/dst]).
+
apply mma_transfert_spec with (1 := eq_refl) (2 := eq_refl); auto.
+
unfold mma_transfert.
mma sss DEC S with dst (3+i) ((v#>src)+(v#>dst)); rew vec.
mma sss stop.
End mma_transfert.
Notation TRANSFERTₐ := mma_transfert.
Hint Rewrite mma_transfert_length : length_db.
Section mma_mult_cst.
Variable (src dst : pos n) (Hsd : src <> dst) (k i : nat).
Definition mma_mult_cst := DECₐ src (3+i) :: JUMPₐ (5+k+i) src ++ INCSₐ dst k ++ JUMPₐ i src.
Fact mma_mult_cst_length : length mma_mult_cst = 5+k.
Proof.
unfold mma_mult_cst; rew length; lia.
Let mma_mult_cst_spec x v st : v#>src = x -> st = (5+k+i,v[0/src][(x*k+(v#>dst))/dst]) -> (i,mma_mult_cst) // (i,v) -+> st.
Proof.
unfold mma_mult_cst.
revert v st; induction x as [ | x IHx ]; intros v st Hv ?; subst.
+
mma sss DEC 0 with src (3+i).
apply sss_progress_compute.
apply subcode_sss_progress with (P := (1+i,JUMPₐ (5+k+i) src)); auto.
apply mma_jump_progress.
apply vec_pos_ext; intros y; dest y dst; dest y src; lia.
+
mma sss DEC S with src (3+i) x.
apply sss_compute_trans with (3+k+i,v[x/src][(k+(v#>dst))/dst]).
*
apply subcode_sss_compute with (P := (3+i,mma_incs dst k)); auto.
apply mma_incs_compute; f_equal; try lia.
apply vec_pos_ext; intros y; dest y dst; lia.
*
apply sss_compute_trans with (i,v[x/src][(k+(v#>dst))/dst]).
-
apply sss_progress_compute.
apply subcode_sss_progress with (P := (3+k+i,JUMPₐ i src)); auto.
apply mma_jump_progress.
apply vec_pos_ext; intros y; dest y dst; dest y src; lia.
-
apply sss_progress_compute, IHx; rew vec; f_equal.
apply vec_pos_ext; intros y; dest y dst; try ring.
dest y src.
Fact mma_mult_cst_progress v st : st = (5+k+i,v[0/src][(k*(v#>src)+(v#>dst))/dst]) -> (i,mma_mult_cst) // (i,v) -+> st.
Proof using Hsd.
intros ?; subst.
apply mma_mult_cst_spec with (1 := eq_refl); do 2 f_equal.
ring.
End mma_mult_cst.
Notation MULT_CSTₐ := mma_mult_cst.
Hint Rewrite mma_mult_cst_length : length_db.
Section mma_decs.
Variable (dst : pos n) (p q : nat).
Fixpoint mma_decs k i := match k with | 0 => INCₐ dst :: DECₐ dst p :: nil | S k => DECₐ dst (3+i) :: INCₐ dst :: DECₐ dst q :: mma_decs k (3+i) end.
Fact mma_decs_length k i : length (mma_decs k i) = 2+3*k.
Proof.
revert i; induction k as [ | ? IHk ]; intros i; simpl; auto.
rewrite IHk; lia.
Let mma_decs_spec_lt k i v w : v#>dst < k -> w = v[0/dst] -> (i,mma_decs k i) // (i,v) -+> (q,w).
Proof.
revert i v w; induction k as [ | k IHk ]; intros i v w H1 ?; subst w.
+
lia.
+
unfold mma_decs; fold mma_decs.
case_eq (v#>dst).
*
intros H2.
mma sss DEC 0 with dst (3+i).
mma sss INC with dst.
mma sss DEC S with dst q (v#>dst); rew vec.
mma sss stop; f_equal.
apply vec_pos_ext; intros x; dest x dst.
*
intros d Hd.
mma sss DEC S with dst (3+i) d.
apply subcode_sss_compute with (P := (3+i,mma_decs k (3+i))); auto.
apply sss_progress_compute, IHk; rew vec; try lia.
Let mma_decs_spec_le k i v w : k <= v#>dst -> w = v[((v#>dst)-k)/dst] -> (i,mma_decs k i) // (i,v) -+> (p,w).
Proof.
revert i v w; induction k as [ | k IHk ]; intros i v w H1 ?; subst w.
+
simpl.
mma sss INC with dst.
mma sss DEC S with dst p (v#>dst); rew vec.
mma sss stop; f_equal.
apply vec_pos_ext; intros x; dest x dst; try lia.
+
unfold mma_decs; fold mma_decs.
mma sss DEC S with dst (3+i) ((v#>dst) - 1); try lia.
apply subcode_sss_compute with (P := (3+i,mma_decs k (3+i))); auto.
apply sss_progress_compute, IHk; rew vec; try lia.
apply vec_pos_ext; intros x; dest x dst; lia.
Fact mma_decs_lt_progress k i v st : v#>dst < k -> st = (q,v[0/dst]) -> (i,mma_decs k i) // (i,v) -+> st.
Proof.
intros H1 ?; subst st.
apply mma_decs_spec_lt; auto.
Fact mma_decs_le_progress k i v st : k <= v#>dst -> st = (p,v[((v#>dst)-k)/dst]) -> (i,mma_decs k i) // (i,v) -+> st.
Proof.
intros H1 ?; subst st.
apply mma_decs_spec_le; auto.
End mma_decs.
Notation DECSₐ := mma_decs.
Section mma_decs_copy.
Variable (dst tmp : pos n) (Hdt : dst <> tmp) (p q : nat).
Fixpoint mma_decs_copy k i := match k with | 0 => INCₐ dst :: DECₐ dst p :: nil | S k => DECₐ dst (3+i) :: INCₐ dst :: DECₐ dst q :: INCₐ tmp :: mma_decs_copy k (4+i) end.
Fact mma_decs_copy_length k i : length (mma_decs_copy k i) = 2+4*k.
Proof.
revert i; induction k as [ | ? IHk ]; intros i; simpl; auto.
rewrite IHk; lia.
Let mma_decs_copy_spec_lt k i v w : v#>dst < k -> w = v[0/dst][((v#>dst)+(v#>tmp))/tmp] -> (i,mma_decs_copy k i) // (i,v) -+> (q,w).
Proof.
revert i v w; induction k as [ | k IHk ]; intros i v w H1 ?; subst w.
+
lia.
+
unfold mma_decs_copy; fold mma_decs_copy.
case_eq (v#>dst).
*
intros H2.
mma sss DEC 0 with dst (3+i).
mma sss INC with dst.
mma sss DEC S with dst q (v#>dst); rew vec.
mma sss stop; f_equal.
apply vec_pos_ext; intros x; dest x tmp; dest x dst.
*
intros d Hd.
mma sss DEC S with dst (3+i) d.
mma sss INC with tmp.
apply subcode_sss_compute with (P := (4+i,mma_decs_copy k (4+i))); auto.
apply sss_progress_compute; rewrite plus_assoc.
apply IHk; rew vec; try lia.
apply vec_pos_ext; intros x; dest x tmp; try lia; dest x dst.
Let mma_decs_copy_spec_le k i v w : k <= v#>dst -> w = v[((v#>dst)-k)/dst][(k+(v#>tmp))/tmp] -> (i,mma_decs_copy k i) // (i,v) -+> (p,w).
Proof.
revert i v w; induction k as [ | k IHk ]; intros i v w H1 ?; subst w.
+
simpl.
mma sss INC with dst.
mma sss DEC S with dst p (v#>dst); rew vec.
mma sss stop; f_equal.
apply vec_pos_ext; intros x; dest x dst; try lia; dest x tmp.
+
unfold mma_decs_copy; fold mma_decs_copy.
mma sss DEC S with dst (3+i) ((v#>dst) - 1); try lia.
mma sss INC with tmp.
apply subcode_sss_compute with (P := (4+i,mma_decs_copy k (4+i))); auto.
apply sss_progress_compute, IHk; rew vec; try lia.
apply vec_pos_ext; intros x; dest x tmp; try lia; dest x dst; lia.
Fact mma_decs_copy_lt_progress k i v st : v#>dst < k -> st = (q,v[0/dst][((v#>dst)+(v#>tmp))/tmp]) -> (i,mma_decs_copy k i) // (i,v) -+> st.
Proof using Hdt.
intros H1 ?; subst st.
apply mma_decs_copy_spec_lt; auto.
Fact mma_decs_copy_le_progress k i v st : k <= v#>dst -> st = (p,v[((v#>dst)-k)/dst][(k+(v#>tmp))/tmp]) -> (i,mma_decs_copy k i) // (i,v) -+> st.
Proof using Hdt.
intros H1 ?; subst st.
apply mma_decs_copy_spec_le; auto.
End mma_decs_copy.
Notation DECS_COPYₐ := mma_decs_copy.
Hint Rewrite mma_decs_length mma_decs_copy_length : length_db.
Section mma_mod_cst.
Variable (x t : pos n) (Hxt : x <> t) (p q k i : nat).
Definition mma_mod_cst := EMPTYₐ x p i ++ DECS_COPYₐ x t i q k (4+i).
Fact mma_mod_cst_length : length mma_mod_cst = 6+4*k.
Proof.
unfold mma_mod_cst; rew length; lia.
Hypothesis (Hk : 0 < k).
Let mma_mod_cst_spec_0 v : v#>x = 0 -> (i,mma_mod_cst) // (i,v) -+> (p,v).
Proof.
intros H; unfold mma_mod_cst.
apply subcode_sss_progress with (P := (i, EMPTYₐ x p i)); auto.
apply mma_empty_progress; auto.
Let mma_mod_cst_spec_1 a b v w : v#>x = a*k+b -> w = v[b/x][(a*k+(v#>t))/t] -> (i,mma_mod_cst) // (i,v) ->> (i,w).
Proof.
revert v w; induction a as [ | a IHa ]; intros v w H1 H2; subst w.
+
mma sss stop; f_equal.
simpl in H1; rewrite <- H1; simpl; rew vec.
+
unfold mma_mod_cst.
apply sss_compute_trans with (4+i,v).
*
apply sss_progress_compute, subcode_sss_progress with (P := (i, EMPTYₐ x p i)); auto.
apply mma_non_empty_progress; auto; lia.
*
apply sss_compute_trans with (i, v[(a*k+b)/x][(k+(v#>t))/t]).
-
apply subcode_sss_compute with (P := (4+i,mma_decs_copy x t i q k (4+i))); auto.
apply sss_progress_compute, mma_decs_copy_le_progress; auto; rew vec.
{
simpl; generalize (a*k); intro; lia.
}
do 3 f_equal; rewrite H1; simpl mult; generalize (a*k); intro; lia.
-
apply IHa; rew vec.
apply vec_pos_ext; intros y; dest y t; try ring; dest y x.
Let mma_mod_cst_spec_2 v w : 0 < v#>x < k -> w = v[0/x][((v#>x)+(v#>t))/t] -> (i,mma_mod_cst) // (i,v) -+> (q,w).
Proof.
intros H ?; subst; unfold mma_mod_cst.
apply sss_progress_trans with (4+i,v).
+
apply subcode_sss_progress with (P := (i, EMPTYₐ x p i)); auto.
apply mma_non_empty_progress; auto; lia.
+
apply subcode_sss_progress with (P := (4+i, DECS_COPYₐ x t i q k (4+i))); auto.
apply mma_decs_copy_lt_progress; auto; lia.
Fact mma_mod_cst_divides_progress v a st : v#>x = a*k -> st = (p,v[0/x][((v#>x)+(v#>t))/t]) -> (i,mma_mod_cst) // (i,v) -+> st.
Proof using Hxt Hk.
intros H1 ?; subst st.
apply sss_compute_progress_trans with (i,v[0/x][((v#>x)+(v#>t))/t]).
+
apply mma_mod_cst_spec_1 with (a := a) (b := 0); try lia.
rewrite <- H1; auto.
+
apply mma_mod_cst_spec_0; rew vec.
Fact mma_mod_cst_not_divides_progress v a b st : v#>x = a*k+b -> 0 < b < k -> st = (q,v[0/x][((v#>x)+(v#>t))/t]) -> (i,mma_mod_cst) // (i,v) -+> st.
Proof using Hxt Hk.
intros H1 H2 ?; subst st.
apply sss_compute_progress_trans with (i,v[b/x][(a*k+(v#>t))/t]).
+
apply mma_mod_cst_spec_1 with (a := a) (b := b); try lia; auto.
+
apply mma_mod_cst_spec_2; rew vec.
apply vec_pos_ext; intros y; dest y t; try lia; dest y x.
End mma_mod_cst.
Notation MOD_CSTₐ := mma_mod_cst.
Hint Rewrite mma_decs_length mma_mod_cst_length : length_db.
Section mma_div_cst.
Variable (s d : pos n) (Hsd : s <> d) (k i : nat).
Let p := (2+3*k+i).
Let q := (5+3*k+i).
Definition mma_div_cst := DECSₐ s p q k i ++ INCₐ d :: JUMPₐ i s.
Fact mma_div_cst_length : length mma_div_cst = 5+3*k.
Proof.
unfold mma_div_cst; rew length; lia.
Hypothesis (Hk : 0 < k).
Let mma_div_cst_spec a v w : v#>s = a*k -> w = v[0/s][(a+(v#>d))/d] -> (i, mma_div_cst) // (i,v) -+> (q,w).
Proof.
unfold mma_div_cst; revert v w; induction a as [ | a IHa ]; intros v w H1 ?; subst w.
+
apply subcode_sss_progress with (P := (i,mma_decs s p q k i)); auto.
apply mma_decs_lt_progress; try lia.
f_equal; simpl.
apply vec_pos_ext; intros y; dest y d.
+
apply sss_progress_trans with (p,v[(a*k)/s]).
*
apply subcode_sss_progress with (P := (i,mma_decs s p q k i)); auto.
apply mma_decs_le_progress.
-
rewrite H1; simpl; generalize (a*k); intro; lia.
-
f_equal.
apply vec_pos_ext; intros y; dest y d; dest y s.
rewrite H1; simpl; generalize (a*k); intro; lia.
*
unfold p.
mma sss INC with d.
apply sss_compute_trans with (i,v[(a*k)/s][(S (v[(a*k)/s]#>d))/d]).
-
apply sss_progress_compute, subcode_sss_progress with (P := (3+3*k+i, JUMPₐ i s)); auto.
apply mma_jump_progress; auto.
-
apply sss_progress_compute, IHa; rew vec.
apply vec_pos_ext; intros y; dest y d; try lia; dest y s.
Fact mma_div_cst_progress a v st : v#>s = a*k -> st = (q,v[0/s][(a+(v#>d))/d]) -> (i, mma_div_cst) // (i,v) -+> st.
Proof using Hsd Hk.
intros H1 H2; subst st; apply mma_div_cst_spec with (1 := H1); auto.
End mma_div_cst.
Notation DIV_CSTₐ := mma_div_cst.
Hint Rewrite mma_div_cst_length : length_db.
Section mma_loop.
Variables (x : pos n) (i : nat).
Definition mma_loop := JUMPₐ i x.
Fact mma_loop_loop v : (i,mma_loop) // (i,v) -+> (i,v).
Proof.
apply mma_jump_progress; auto.
End mma_loop.
Notation LOOPₐ := mma_loop.
End Minsky_Machine_alt_utils.

Let mma_div_cst_spec a v w : v#>s = a*k -> w = v[0/s][(a+(v#>d))/d] -> (i, mma_div_cst) // (i,v) -+> (q,w).
Proof.
unfold mma_div_cst; revert v w; induction a as [ | a IHa ]; intros v w H1 ?; subst w.
+
apply subcode_sss_progress with (P := (i,mma_decs s p q k i)); auto.
apply mma_decs_lt_progress; try lia.
f_equal; simpl.
apply vec_pos_ext; intros y; dest y d.
+
apply sss_progress_trans with (p,v[(a*k)/s]).
*
apply subcode_sss_progress with (P := (i,mma_decs s p q k i)); auto.
apply mma_decs_le_progress.
-
rewrite H1; simpl; generalize (a*k); intro; lia.
-
f_equal.
apply vec_pos_ext; intros y; dest y d; dest y s.
rewrite H1; simpl; generalize (a*k); intro; lia.
*
unfold p.
mma sss INC with d.
apply sss_compute_trans with (i,v[(a*k)/s][(S (v[(a*k)/s]#>d))/d]).
-
apply sss_progress_compute, subcode_sss_progress with (P := (3+3*k+i, JUMPₐ i s)); auto.
apply mma_jump_progress; auto.
-
apply sss_progress_compute, IHa; rew vec.
apply vec_pos_ext; intros y; dest y d; try lia; dest y s.
