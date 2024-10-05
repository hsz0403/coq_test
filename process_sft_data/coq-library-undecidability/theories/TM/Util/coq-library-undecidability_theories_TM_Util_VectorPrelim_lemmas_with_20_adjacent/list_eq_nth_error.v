From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.
Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X := match v with | Vector.nil _ => List.nil | Vector.cons _ x n v' => x :: vector_to_list v' end.

Lemma vector_to_list_correct (X : Type) (n : nat) (v : Vector.t X n) : vector_to_list v = Vector.to_list v.
Proof.
induction v.
-
cbn.
auto.
-
cbn.
f_equal.
Admitted.

Lemma vector_to_list_length (X : Type) (n : nat) (v : Vector.t X n) : length (vector_to_list v) = n.
Proof.
induction v.
-
cbn.
auto.
-
cbn.
f_equal.
Admitted.

Lemma vector_to_list_map (X Y : Type) (f : X -> Y) (n : nat) (v : Vector.t X n) : map f (vector_to_list v) = vector_to_list (Vector.map f v).
Proof.
induction v.
-
cbn.
auto.
-
cbn.
f_equal.
Admitted.

Lemma vector_to_list_cast (X : Type) (n1 n2 : nat) (H : n1 = n2) (v : Vector.t X n1) : vector_to_list (Vector.cast v H) = vector_to_list v.
Proof.
subst.
rename n2 into n.
Admitted.

Lemma vector_to_list_eta (X : Type) (n : nat) (v : Vector.t X (S n)) : Vector.hd v :: vector_to_list (Vector.tl v) = vector_to_list v.
Proof.
destruct_vector.
cbn.
Admitted.

Lemma vector_to_list_map2_eta (X Y Z : Type) (n : nat) (f : X -> Y -> Z) (xs : Vector.t X (S n)) (ys : Vector.t Y (S n)) : f (Vector.hd xs) (Vector.hd ys) :: vector_to_list (Vector.map2 f (Vector.tl xs) (Vector.tl ys)) = vector_to_list (Vector.map2 f xs ys).
Proof.
Admitted.

Lemma fold_left_vector_to_list (X Y : Type) (n : nat) (f : Y -> X -> Y) (v : Vector.t X n) (a : Y) : Vector.fold_left f a v = fold_left f (vector_to_list v) a.
Proof.
revert a.
Admitted.

Lemma vector_to_list_In (X : Type) (n : nat) (xs : Vector.t X n) (x : X) : In x (vector_to_list xs) <-> Vector.In x xs.
Proof.
split.
-
induction xs as [ | y n xs IH]; intros; cbn in *.
+
auto.
+
destruct H as [ <- | H].
*
now constructor.
*
now constructor; auto.
-
induction xs as [ | y n xs IH]; intros; cbn in *.
+
inv H.
+
apply In_cons in H as [<- | H].
*
now constructor.
*
Admitted.

Lemma vector_nth_error_nat X n' i (xs : Vector.t X n') : nth_error (Vector.to_list xs) i = match lt_dec i n' with Specif.left H => Some (Vector.nth xs (Fin.of_nat_lt H)) | _ => None end.
Proof.
clear.
rewrite <- vector_to_list_correct.
induction xs in i|-*.
now destruct i.
cbn in *.
destruct i;cbn.
easy.
rewrite IHxs.
do 2 destruct lt_dec.
4:easy.
now symmetry;erewrite Fin.of_nat_ext.
Admitted.

Lemma vector_nth_error_fin X n' i (xs : Vector.t X n') : nth_error (Vector.to_list xs) (proj1_sig (Fin.to_nat i)) = Some (Vector.nth xs i).
Proof.
clear.
rewrite <- vector_to_list_correct.
induction xs in i|-*.
now inv i.
cbn;rewrite vector_to_list_correct in *.
cbn in *.
edestruct (fin_destruct_S) as [ (i'&->)| -> ].
2:now cbn.
unshelve erewrite (_ : Fin.FS = Fin.R 1).
reflexivity.
setoid_rewrite (Fin.R_sanity 1 i').
cbn.
Admitted.

Lemma vector_app_to_list X k k' (xs : Vector.t X k) (ys : Vector.t X k'): vector_to_list (Vector.append xs ys) = vector_to_list xs ++ vector_to_list ys.
Proof.
induction xs.
easy.
cbn.
Admitted.

Lemma list_eq_nth_error X (xs ys : list X) : (forall n, nth_error xs n = nth_error ys n) -> xs = ys.
Proof.
induction xs in ys|-*;destruct ys;cbn;intros H.
1:easy.
1-2:now specialize (H 0).
generalize (H 0).
intros [= ->].
erewrite IHxs.
easy.
intros n'.
now specialize (H (S n')).
