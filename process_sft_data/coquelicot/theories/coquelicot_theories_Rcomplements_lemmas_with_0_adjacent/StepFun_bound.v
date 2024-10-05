Ltac evar_last := match goal with | |- ?f ?x => let tx := type of x in let tx := eval simpl in tx in let tmp := fresh "tmp" in evar (tmp : tx) ; refine (@eq_ind tx tmp f _ x _) ; unfold tmp ; clear tmp end.
Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.
Module MyNat.
End MyNat.
Require Import Even Div2.
Require Import mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool.
Open Scope R_scope.
Definition floor x := proj1_sig (floor_ex x).
Definition floor1 x := proj1_sig (floor1_ex x).
Definition nfloor x pr := proj1_sig (nfloor_ex x pr).
Definition nfloor1 x pr := proj1_sig (nfloor1_ex x pr).
Fixpoint pow2 (n : nat) : nat := match n with | O => 1%nat | S n => (2 * pow2 n)%nat end.
Definition pos_div_2 (eps : posreal) := mkposreal _ (is_pos_div_2 eps).
Definition sign (x : R) := match total_order_T 0 x with | inleft (left _) => 1 | inleft (right _) => 0 | inright _ => -1 end.
Definition belast {T : Type} (s : seq T) := match s with | [::] => [::] | h :: s => belast h s end.

Lemma StepFun_bound {a b : R} (f : StepFun a b) : exists s : R, forall x, Rmin a b <= x <= Rmax a b -> f x <= s.
Proof.
case: f => /= f [lx [ly [Hsort [Hhead [Hlast [Hsize Hval]]]]]]; rename a into a0 ; rename b into b0 ; set a := Rmin a0 b0 ; set b := Rmax a0 b0 ; set Rl_max := fun x0 => fix f l := match l with | RList.nil => x0 | RList.cons h t => Rmax h (f t) end ; set f_lx := (fix app l := match l with | RList.nil => RList.nil | RList.cons h t => RList.cons (f h) (app t) end) lx ; set M_f_lx := Rl_max (f 0) f_lx ; set M_ly := Rl_max 0 ly.
exists (Rmax M_f_lx M_ly) => x [Hx Hx'].
rewrite /M_f_lx /f_lx ; case: lx Hsort Hhead Hlast Hsize Hval {f_lx M_f_lx}.
move => _ _ _ H ; contradict H ; apply O_S.
move => h l ; case: l h.
move => h _ Ha Hb _ _ ; simpl in Ha, Hb.
rewrite /a -Ha in Hx ; rewrite /b -Hb in Hx'.
rewrite (Rle_antisym _ _ Hx Hx') /= ; apply Rle_trans with (2 := RmaxLess1 _ _) ; apply RmaxLess1.
move => h l h' Hsort Hhead Hlast Hsize Hval.
apply Rle_lt_or_eq_dec in Hx' ; case: Hx' => Hx'.
have H : exists i : nat, (i < S (Rlength l))%nat /\ (pos_Rl (RList.cons h' (RList.cons h l)) i) <= x < (pos_Rl (RList.cons h' (RList.cons h l)) (S i)).
rewrite /a -Hhead in Hx ; rewrite /b -Hlast in Hx'.
elim: l h' h Hx Hx' Hsort {Hhead Hlast Hsize Hval} => [| h'' l IH] h' h Hx Hx' Hsort ; simpl in Hx, Hsort.
case: (Rlt_le_dec x h) => H.
exists O ; intuition.
exists O => /= ; intuition.
case: (Rlt_le_dec x h) => H.
exists O => /= ; intuition.
have H0 : ordered_Rlist (RList.cons h (RList.cons h'' l)).
move => i Hi ; apply (Hsort (S i)) => /= ; apply lt_n_S, Hi.
case: (IH _ _ H Hx' H0) => {IH} i Hi.
exists (S i) ; split.
simpl ; apply lt_n_S, Hi => /=.
apply Hi.
case: H => i [Hi [Ht Ht']].
apply Rle_lt_or_eq_dec in Ht ; case: Ht => Ht.
rewrite (Hval i Hi x).
apply Rle_trans with (2 := RmaxLess2 _ _).
rewrite /M_ly ; case: (ly).
apply Rle_refl.
move => y ly' ; elim: ly' (i) y.
move => i0 y ; case: i0 => //=.
apply RmaxLess1.
move => _; apply RmaxLess2.
move => y ly' IH i0 y' ; case: i0.
apply RmaxLess1.
move => n ; apply Rle_trans with (1 := IH n y) ; apply RmaxLess2.
split => //.
rewrite -Ht ; apply Rle_trans with (2 := RmaxLess1 _ _).
case: (i).
apply RmaxLess1.
move => n ; elim: n (h) (h') (l).
move => h0 h'0 l0 ; apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess1.
move => n IH h0 h'0 l0.
case: l0.
apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess2.
move => h''0 l0 ; apply Rle_trans with (1 := IH h''0 h0 l0), RmaxLess2.
rewrite Hx' /b -Hlast.
apply Rle_trans with (2 := RmaxLess1 _ _).
elim: (l) (h') (h) => [| h''0 l0 IH] h'0 h0.
apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess1.
apply Rle_trans with (1 := IH h0 h''0), RmaxLess2.
