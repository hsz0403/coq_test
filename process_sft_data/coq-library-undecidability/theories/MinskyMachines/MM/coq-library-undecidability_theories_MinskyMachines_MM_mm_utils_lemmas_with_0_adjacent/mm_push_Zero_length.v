Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils list_bool pos vec subcode sss.
From Undecidability.MinskyMachines.MM Require Import mm_defs.
Set Default Proof Using "Type".
Set Implicit Arguments.
Tactic Notation "rew" "length" := autorewrite with length_db.
Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).
Local Notation "P // s -[ k ]-> t" := (sss_steps (@mm_sss _) P k s t).
Local Notation "P // s -+> t" := (sss_progress (@mm_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mm_sss _) P s t).
Section Minsky_Machine_utils.
Variable (n : nat).
Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.
Section mm_null.
Variable (src zero : pos n) (Hsz : src <> zero).
Definition mm_null i := DEC src (2+i) :: DEC zero i :: nil.
Fact mm_null_length i : length (mm_null i) = 2.
Proof.
auto.
Let mm_null_spec i k v w : v#>src = k -> v#>zero = 0 -> w = v[0/src] -> (i,mm_null i) // (i,v) -+> (2+i,w).
Proof.
unfold mm_null.
revert v w.
induction k as [ | k IHk ]; intros v w H1 H2 H3; subst w.
mm sss DEC 0 with src (2+i).
mm sss stop; f_equal.
apply vec_pos_ext; intros z; dest z src.
mm sss DEC S with src (2+i) k.
mm sss DEC 0 with zero i; rew vec.
apply sss_progress_compute.
apply IHk; rew vec.
Fact mm_null_progress i v st : v#>zero = 0 -> st = (2+i,v[0/src]) -> (i,mm_null i) // (i,v) -+> st.
Proof using Hsz.
intros; subst.
apply mm_null_spec with (1 := eq_refl); auto.
End mm_null.
Hint Rewrite mm_null_length : length_db.
Section mm_nullify.
Variable (zero : pos n).
Fixpoint mm_nullify i lr := match lr with | nil => nil | x::lr => mm_null x zero i ++ mm_nullify (2+i) lr end.
Fact mm_nullify_length i lr : length (mm_nullify i lr) = 2*length lr.
Proof.
revert i; induction lr as [ | x lr IH ]; simpl; intros i; auto.
rewrite IH; lia.
Fact mm_nullify_compute i lr v w : v#>zero = 0 -> (forall p, In p lr -> p <> zero) -> (forall p, In p lr -> w#>p = 0) -> (forall p, ~ In p lr -> w#>p = v#>p) -> (i,mm_nullify i lr) // (i,v) ->> (length (mm_nullify i lr)+i,w).
Proof.
rewrite mm_nullify_length.
revert i v w; induction lr as [ | x lr IH ]; intros i v w H1 H2 H3 H4.
mm sss stop; f_equal.
apply vec_pos_ext; intros; rewrite H4; auto.
rew length.
unfold mm_nullify; fold mm_nullify.
apply sss_compute_trans with (2+i,v[0/x]).
apply subcode_sss_compute with (P := (i,mm_null x zero i)); auto.
apply sss_progress_compute, mm_null_progress; auto.
apply H2; left; auto.
apply subcode_sss_compute with (P := (2+i,mm_nullify (2+i) lr)).
subcode_tac; solve list eq.
replace (2*S (length lr)+i) with (2*(length lr)+(2+i)) by lia.
apply IH.
specialize (H2 x (or_introl eq_refl)); rew vec.
intros; apply H2; right; auto.
intros; apply H3; right; auto.
intros p Hp.
dest p x.
apply H3; left; auto.
apply H4; intros [|]; auto.
End mm_nullify.
Section transfert.
Variables (src dst zero : pos n).
Hypothesis (Hsd : src <> dst) (Hsz : src <> zero) (Hdz : dst <> zero).
Definition mm_transfert i := DEC src (3+i) :: INC dst :: DEC zero i :: nil.
Fact mm_transfert_length i : length (mm_transfert i) = 3.
Proof.
reflexivity.
Let mm_transfert_spec i v w k x : v#>src = k -> v#>dst = x -> v#>zero = 0 -> w = v[0/src][(k+x)/dst] -> (i,mm_transfert i) // (i,v) -+> (3+i,w).
Proof.
unfold mm_transfert.
revert v w x.
induction k as [ | k IHk ]; intros v w x H1 H2 H3 H4; subst w.
mm sss DEC 0 with src (3+i).
mm sss stop; f_equal; auto.
apply vec_pos_ext; intros p.
dest p dst; dest p src.
mm sss DEC S with src (3+i) k.
mm sss INC with dst.
mm sss DEC 0 with zero i; rew vec.
replace (S k + x) with (k + S x) by lia.
apply sss_progress_compute.
apply IHk with (S x); rew vec.
apply vec_pos_ext; intros p.
dest p dst; dest p src.
Fact mm_transfert_progress i v st : v#>dst = 0 -> v#>zero = 0 -> st = (3+i,v[0/src][(v#>src)/dst]) -> (i,mm_transfert i) // (i,v) -+> st.
Proof using Hdz Hsz Hsd.
intros H1 H2 ?; subst; apply mm_transfert_spec with (1 := eq_refl) (2 := eq_refl); auto.
rewrite H1; apply vec_pos_ext; intros p; dest p dst.
End transfert.
Hint Rewrite mm_transfert_length : length_db.
Section div2.
Variables (src quo rem : pos n) (Hsq : src <> quo) (Hsr : src <> rem) (Hqr : quo <> rem) (i : nat).
Definition mm_div2 := DEC src (6+i) :: INC rem :: DEC src (i+6) :: DEC rem (4+i) :: INC quo :: DEC rem i :: nil.
Fact mm_div2_length : length mm_div2 = 6.
Proof.
reflexivity.
Let mm_div2_spec_0 k v w : v#>src = 2*k -> v#>rem = 0 -> w = v[0/src][(k+(v#>quo))/quo] -> (i,mm_div2) // (i,v) -+> (6+i,w).
Proof.
unfold mm_div2.
revert v w.
induction k as [ | k IHk ]; intros v w H1 H4 H3.
simpl in H1.
mm sss DEC 0 with src (6+i).
mm sss stop; f_equal; subst.
apply vec_pos_ext; intros p.
dest p quo; dest p src.
replace (2*S k) with (S (S (2*k))) in H1 by lia.
mm sss DEC S with src (6+i) (S (2*k)).
mm sss INC with rem.
mm sss DEC S with src (i+6) (2*k); rew vec.
mm sss DEC S with rem (4+i) (v#>rem); rew vec.
mm sss INC with quo; rew vec.
mm sss DEC 0 with rem i; rew vec.
apply sss_progress_compute.
apply IHk; auto; rew vec.
subst; apply vec_pos_ext; intros p.
dest p quo; try lia.
dest p src; dest p rem.
Let mm_div2_spec_1 k v w : v#>src = 1+2*k -> v#>rem = 0 -> w = v[0/src][(k+(v#>quo))/quo][1/rem] -> (i,mm_div2) // (i,v) -+> (6+i,w).
Proof.
unfold mm_div2.
revert v w.
induction k as [ | k IHk ]; intros v w H1 H4 H3.
simpl in H1.
mm sss DEC S with src (6+i) 0.
mm sss INC with rem.
mm sss DEC 0 with src (i+6); rew vec.
mm sss stop; f_equal; try lia.
subst; simpl.
apply vec_pos_ext; intros p.
dest p rem; dest p quo; dest p src.
replace (1 + 2*S k) with (S (S (1+2*k))) in H1 by lia.
mm sss DEC S with src (6+i) (S (1+2*k)).
mm sss INC with rem.
mm sss DEC S with src (i+6) (1+2*k); rew vec.
mm sss DEC S with rem (4+i) (v#>rem); rew vec.
mm sss INC with quo; rew vec.
mm sss DEC 0 with rem i; rew vec.
apply sss_progress_compute.
apply IHk; auto; rew vec.
subst; apply vec_pos_ext; intros p.
dest p quo; try lia.
dest p src; dest p rem.
Fact mm_div2_progress v : v#>quo = 0 -> v#>rem = 0 -> let (k,b) := div2 (v#>src) in (i,mm_div2) // (i,v) -+> (6+i,v[0/src][k/quo][(if b then 1 else 0)/rem]).
Proof using Hsr Hsq Hqr.
intros H2 H3.
generalize (div2_spec (v#>src)).
destruct (div2 (v#>src)) as (k,[]); intros H4.
apply mm_div2_spec_1 with k; auto.
lia.
apply vec_pos_ext; intros p.
dest p rem; dest p quo; lia.
apply mm_div2_spec_0 with k; auto.
apply vec_pos_ext; intros p.
dest p rem; dest p quo; lia.
End div2.
Hint Rewrite mm_div2_length : length_db.
Section mul2.
Variables (src dst zero : pos n) (Hsd : src <> dst) (Hsz : src <> zero) (Hdz : dst <> zero) (i : nat).
Let dst' := dst.
Definition mm_mul2 := DEC src (4+i) :: INC dst :: INC dst' :: DEC zero i :: nil.
Fact mm_mul2_length : length mm_mul2 = 4.
Proof.
reflexivity.
Let mm_mul2_spec k v w : v#>src = k -> v#>zero = 0 -> w = v[0/src][(2*k+(v#>dst))/dst] -> (i,mm_mul2) // (i,v) -+> (4+i,w).
Proof.
unfold mm_mul2.
revert v w; induction k as [ | k IHk ]; intros v w H1 H2 H3.
mm sss DEC 0 with src (4+i).
mm sss stop; f_equal; subst.
apply vec_pos_ext; intros p.
dest p dst; dest p src.
mm sss DEC S with src (4+i) k.
mm sss INC with dst.
mm sss INC with dst'.
mm sss DEC 0 with zero i; rew vec.
unfold dst'; rew vec.
apply sss_progress_compute.
apply IHk; unfold dst'; rew vec.
subst; apply vec_pos_ext; intros p.
dest p dst.
lia.
dest p src.
Fact mm_mul2_progress v st : v#>dst = 0 -> v#>zero = 0 -> st = (4+i,v[0/src][(2*(v#>src))/dst]) -> (i,mm_mul2) // (i,v) -+> st.
Proof using Hsz Hsd Hdz.
intros H1 H2 ?; subst.
apply mm_mul2_spec with (1 := eq_refl); auto.
rewrite H1; f_equal; lia.
End mul2.
Hint Rewrite mm_mul2_length : length_db.
Fixpoint stack_enc (s : list bool) : nat := match s with | nil => 1 | One::s => 1+2*stack_enc s | Zero::s => 2*stack_enc s end.
Fact stack_enc_S s : { k | stack_enc s = S k }.
Proof.
induction s as [ | [] s (k & Hk) ].
exists 0; auto.
exists (2*stack_enc s); auto.
exists (S (2*k)); simpl; lia.
Section push.
Variables (src tmp zero : pos n) (Hst : src <> tmp) (Hsz : src <> zero) (Htz : tmp <> zero) (i : nat).
Definition mm_push_Zero := mm_transfert src tmp zero i ++ mm_mul2 tmp src zero (3+i).
Fact mm_push_Zero_length : length mm_push_Zero = 7.
Proof.
reflexivity.
Fact mm_push_Zero_progress s v : v#>tmp = 0 -> v#>zero = 0 -> v#>src = stack_enc s -> (i,mm_push_Zero) // (i,v) -+> (7+i,v[(stack_enc (Zero::s))/src]).
Proof using Htz Hsz Hst.
intros H1 H2 H3.
unfold mm_push_Zero.
apply sss_progress_trans with (st2 := (3+i,v[0/src][(v#>src)/tmp])).
apply subcode_sss_progress with (P := (i,mm_transfert src tmp zero i)); auto.
apply mm_transfert_progress; auto.
apply subcode_sss_progress with (P := (3+i,mm_mul2 tmp src zero (3 + i))); auto.
apply mm_mul2_progress; auto; rew vec.
f_equal.
apply vec_pos_ext; intros p.
dest p src.
rewrite H3; auto.
dest p tmp.
Definition mm_push_One := mm_push_Zero ++ INC src :: nil.
Hint Rewrite mm_push_Zero_length : length_db.
Fact mm_push_One_length : length mm_push_One = 8.
Proof.
reflexivity.
Fact mm_push_One_progress s v : v#>tmp = 0 -> v#>zero = 0 -> v#>src = stack_enc s -> (i,mm_push_One) // (i,v) -+> (8+i,v[(stack_enc (One::s))/src]).
Proof using Htz Hsz Hst.
intros H1 H2 H3.
unfold mm_push_One.
apply sss_progress_trans with (7+i,v[(stack_enc (Zero::s))/src]).
apply subcode_sss_progress with (P := (i,mm_push_Zero)); auto.
apply mm_push_Zero_progress; auto.
mm sss INC with src.
mm sss stop; f_equal; auto.
apply vec_pos_ext; intros p.
dest p src.
End push.
Hint Rewrite mm_push_Zero_length mm_push_One_length : length_db.
Section pop.
Variables (src tmp1 tmp2 zero : pos n) (Hs1 : src <> tmp1) (Hs2 : src <> tmp2) (Hsz : src <> zero) (H12 : tmp1 <> tmp2) (H1z : tmp1 <> zero) (H2z : tmp2 <> zero) (i j k e : nat).
Let src' := src.
Definition mm_pop := (* i *) mm_transfert src tmp1 tmp2 i ++ (* 3+i *) mm_div2 tmp1 src tmp2 (3+i) ++ (* 9+i *) DEC src (13+i) :: (* 10+i *) INC src :: (* 11+i *) DEC tmp2 j :: (* 12+i *) DEC tmp1 k :: (* 13+i *) DEC tmp2 k :: (* 14+i *) INC src' :: (* 15+i *) DEC tmp2 e :: nil.
Fact mm_pop_length : length mm_pop = 16.
Proof.
reflexivity.
Fact mm_pop_void_progress v : v#>tmp1 = 0 -> v#>tmp2 = 0 -> v#>src = stack_enc nil -> (i,mm_pop) // (i,v) -+> (e,v).
Proof using Hs1 Hs2 H12.
unfold mm_pop.
intros H1 H2 H4; simpl in H4.
apply sss_progress_trans with (3+i,v[0/src][1/tmp1]).
apply subcode_sss_progress with (P := (i,mm_transfert src tmp1 tmp2 i)); auto.
apply mm_transfert_progress; auto; f_equal.
rewrite H4; auto.
apply sss_progress_trans with (9+i,v[0/tmp1][0/src][1/tmp2]).
apply subcode_sss_progress with (P := (3+i,mm_div2 tmp1 src tmp2 (3 + i))); auto.
apply mm_div2_progress_1 with (k := 0); auto; rew vec.
f_equal.
apply vec_pos_ext; intros p.
dest p tmp2; dest p src; dest p tmp1.
mm sss DEC 0 with src (13+i); rew vec.
mm sss DEC S with tmp2 k 0; rew vec.
mm sss INC with src'; unfold src'; rew vec.
mm sss DEC 0 with tmp2 e; rew vec.
mm sss stop; f_equal.
apply vec_pos_ext; intros p.
dest p tmp2; dest p src; dest p tmp1.
Fact mm_pop_Zero_progress v s: v#>tmp1 = 0 -> v#>tmp2 = 0 -> v#>src = stack_enc (Zero::s) -> (i,mm_pop) // (i,v) -+> (j,v[(stack_enc s)/src]).
Proof using Hs1 Hs2 H12.
unfold mm_pop.
intros H1 H2 H4; unfold stack_enc in H4; fold stack_enc in H4.
apply sss_progress_trans with (3+i,v[0/src][(2*stack_enc s)/tmp1]).
apply subcode_sss_progress with (P := (i,mm_transfert src tmp1 tmp2 i)); auto.
apply mm_transfert_progress; auto; f_equal.
rewrite H4; auto.
apply sss_progress_trans with (9+i,v[0/tmp1][(stack_enc s)/src][0/tmp2]).
apply subcode_sss_progress with (P := (3+i,mm_div2 tmp1 src tmp2 (3 + i))); auto.
apply mm_div2_progress_0 with (k := stack_enc s); auto; rew vec.
rewrite div2_2p0; auto.
f_equal.
apply vec_pos_ext; intros p.
dest p tmp2; dest p src; dest p tmp1.
destruct (stack_enc_S s) as (q & Hq).
mm sss DEC S with src (13+i) q; rew vec.
mm sss INC with src; rew vec.
mm sss DEC 0 with tmp2 j; rew vec.
mm sss stop; f_equal.
apply vec_pos_ext; intros p.
dest p src; dest p tmp2; dest p tmp1.
Fact mm_pop_One_progress v s: v#>tmp1 = 0 -> v#>tmp2 = 0 -> v#>src = stack_enc (One::s) -> (i,mm_pop) // (i,v) -+> (k,v[(stack_enc s)/src]).
Proof using Hs1 Hs2 H12.
unfold mm_pop.
intros H1 H2 H4; unfold stack_enc in H4; fold stack_enc in H4.
apply sss_progress_trans with (3+i,v[0/src][(2*stack_enc s+1)/tmp1]).
apply subcode_sss_progress with (P := (i,mm_transfert src tmp1 tmp2 i)); auto.
apply mm_transfert_progress; auto; f_equal.
rewrite H4; f_equal; lia.
apply sss_progress_trans with (9+i,v[0/tmp1][(stack_enc s)/src][1/tmp2]).
apply subcode_sss_progress with (P := (3+i,mm_div2 tmp1 src tmp2 (3 + i))); auto.
apply mm_div2_progress_1 with (k := stack_enc s); auto; rew vec.
rewrite div2_2p1; auto.
f_equal.
apply vec_pos_ext; intros p.
dest p tmp2; dest p src; dest p tmp1.
destruct (stack_enc_S s) as (q & Hq).
mm sss DEC S with src (13+i) q; rew vec.
mm sss INC with src; rew vec.
mm sss DEC S with tmp2 j 0; rew vec.
mm sss DEC 0 with tmp1 k; rew vec.
mm sss stop; f_equal.
apply vec_pos_ext; intros p.
dest p src; dest p tmp2; dest p tmp1.
End pop.
End Minsky_Machine_utils.
Hint Rewrite mm_push_Zero_length mm_push_One_length mm_pop_length : length_db.

Fact mm_push_Zero_length : length mm_push_Zero = 7.
Proof.
reflexivity.
