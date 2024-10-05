From Undecidability.Shared.Libs.PSL Require Import Prelim Tactics.Tactics EqDec.
From Coq.Vectors Require Import Fin Vector.
From Undecidability.Shared.Libs.PSL Require Import Vectors.FinNotation.
From Undecidability.Shared.Libs.PSL Require Export Vectors.Fin.
Arguments Vector.nth {A} {m} (v') !p.
Arguments Vector.map {A B} f {n} !v /.
Arguments Vector.map2 {A B C} g {n} !v1 !v2 /.
Tactic Notation "dependent" "destruct" constr(V) := match type of V with | Vector.t ?Z (S ?n) => revert all except V; pattern V; revert n V; eapply caseS; intros | Vector.t ?Z 0 => revert all except V; pattern V; revert V; eapply case0; intros | Fin.t 0 => inv V | Fin.t (S ?n) => let pos := V in revert all except pos; pattern pos; revert n pos; eapply Fin.caseS; intros | _ => fail "Wrong type" end.
Delimit Scope vector_scope with vector.
Local Open Scope vector.
Module VectorNotations2.
Notation "[ | | ]" := (nil _) (format "[ | | ]"): vector_scope.
Notation "h ':::' t" := (cons _ h _ t) (at level 60, right associativity) : vector_scope.
Notation "[ | x | ]" := (x ::: [| |]) : vector_scope.
Notation "[ | x ; y ; .. ; z | ] " := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) (format "[ | x ; y ; .. ; z | ] ") : vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.
End VectorNotations2.
Import VectorNotations2.
Ltac existT_eq := match goal with | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] => apply EqdepFacts.eq_sigT_iff_eq_dep in H; inv H end.
Ltac existT_eq' := match goal with | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] => apply EqdepFacts.eq_sigT_iff_eq_dep in H; induction H end.
Ltac destruct_vector_in := lazymatch goal with | [ H: Vector.In _ [| |] |- _ ] => solve [exfalso;simple apply In_nil in H;exact H] | [ H: Vector.In _ (?x ::: _) |- _ ] => simple apply In_cons in H as [H| H] ; try (is_var x;move H at bottom;subst x) end.
Section In_Dec.
Variable X : Type.
Hypothesis X_dec : eq_dec X.
Fixpoint in_dec (n : nat) (x : X) (xs : Vector.t X n) { struct xs } : bool := match xs with | [| |] => false | y ::: xs' => if Dec (x = y) then true else in_dec x xs' end.
Global Instance In_dec (n : nat) (x : X) (xs : Vector.t X n) : dec (In x xs).
Proof.
eapply dec_transfer.
eapply in_dec_correct.
auto.
Defined.
End In_Dec.
Ltac destruct_vector := repeat match goal with | [ v : Vector.t ?X 0 |- _ ] => let H := fresh "Hvect" in pose proof (@destruct_vector_nil X v) as H; subst v | [ v : Vector.t ?X (S ?n) |- _ ] => let h := fresh "h" in let v' := fresh "v'" in let H := fresh "Hvect" in pose proof (@destruct_vector_cons X n v) as (h&v'&H); subst v; rename v' into v end.
Section In_nth.
Variable (A : Type) (n : nat).
End In_nth.
Section tabulate_vec.
Variable X : Type.
Fixpoint tabulate (n : nat) (f : Fin.t n -> X) {struct n} : Vector.t X n.
Proof.
destruct n.
-
apply Vector.nil.
-
apply Vector.cons.
+
apply f, Fin.F1.
+
apply tabulate.
intros m.
apply f, Fin.FS, m.
Defined.
End tabulate_vec.
Instance Vector_eq_dec n A: eq_dec A -> eq_dec (Vector.t A n).
Proof.
intros H x y.
eapply VectorEq.eq_dec with (A_beq := fun x y => proj1_sig (Sumbool.bool_of_sumbool (H x y))).
intros ? ?.
destruct (Sumbool.bool_of_sumbool).
cbn.
destruct x1;intuition.
Defined.
Instance Fin_eq_dec n : eq_dec (Fin.t n).
Proof.
intros; hnf.
destruct (Fin.eqb x y) eqn:E.
-
left.
now eapply Fin.eqb_eq.
-
right.
intros H.
eapply Fin.eqb_eq in H.
congruence.
Defined.
Import VectorNotations.
Ltac simpl_vector_inv := repeat match goal with | [ H : [| |] = (_ ::: _) |- _ ] => solve [discriminate H] | [ H : (_ ::: _) = [| |] |- _ ] => solve [discriminate H] | [ H : Fin.F1 = Fin.FS _ |- _] => solve [discriminate H] | [ H : Fin.FS _ = Fin.F1 |- _] => solve [discriminate H] | [ H : Fin.FS ?i = Fin.FS ?j |- _] => simple apply Fin.FS_inj in H; first [is_var i;move H at bottom;subst i | is_var j;move H at bottom;subst j | idtac] end.
Ltac simpl_vector_in := repeat match goal with | _ => first [ progress destruct_vector_in | progress simpl_vector_inv | progress auto | congruence ] | [ H : Vector.In _ (Vector.map _ _) |- _] => let x := fresh "x" in eapply vect_in_map_iff in H as (x&<-&H) | [ H : Vector.In _ (Vector.map _ _) |- _] => let x := fresh "x" in let H' := fresh H in eapply vect_in_map_iff in H as (x&H&H') | [ H : Vector.In _ (tabulate _) |- _ ] => let i := fresh "i" in apply in_tabulate in H as (i&->) | [ H : Vector.In _ (tabulate _) |- _ ] => let i := fresh "i" in let H := fresh "H" in apply in_tabulate in H as (i&H) end.
Ltac vector_not_in := let H := fresh "H" in intros H; simpl_vector_in.
Goal Vector.In (Fin.F1 (n := 10)) [|Fin1; Fin2; Fin3 |] -> False.
Proof.
intros H.
simpl_vector_in.
Goal Vector.In (Fin.F1 (n := 10)) (map (Fin.FS) [|Fin0; Fin1; Fin2|]) -> False.
Proof.
intros H.
simpl_vector_in.
Module VecToListCoercion.
Coercion Vector.to_list : Vector.t >-> list.
End VecToListCoercion.
Import VecToListCoercion.
Arguments Vector.eqb {_} _ {_ _}.
Require Import Equations.Type.DepElim.
Local Arguments Fin.of_nat_lt _ {_} _.

Instance Fin_eq_dec n : eq_dec (Fin.t n).
Proof.
intros; hnf.
destruct (Fin.eqb x y) eqn:E.
-
left.
now eapply Fin.eqb_eq.
-
right.
intros H.
eapply Fin.eqb_eq in H.
Admitted.

Lemma Vector_map_app {X Y k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) (f : X -> Y) : Vector.map f (v1 ++ v2)%vector = Vector.map f v1 ++ Vector.map f v2.
Proof.
Admitted.

Lemma Vector_in_app {X n1 n2} (x : X) (v1 : Vector.t X n1) (v2 : Vector.t X n2): Vector.In x (v1 ++ v2) <-> Vector.In x v1 \/ Vector.In x v2.
Proof.
induction v1; cbn.
-
firstorder.
inversion H.
-
split.
+
intros [-> | H] % In_cons.
*
left.
econstructor.
*
eapply IHv1 in H as [ | ]; eauto.
left.
now econstructor.
+
Admitted.

Lemma vect_in_map (X Y : Type) (n : nat) (f : X -> Y) (V : Vector.t X n) (x : X) : In x V -> In (f x) (map f V).
Proof.
Admitted.

Lemma vect_in_map_iff (X Y : Type) (n : nat) (f : X -> Y) (V : Vector.t X n) (y : Y) : In y (map f V) <-> (exists x : X, f x = y /\ In x V).
Proof.
split.
-
intros H.
induction V; cbn in *.
+
inv H.
+
apply In_cons in H as [ <- | H].
*
exists h.
split; auto.
now constructor 1.
*
specialize (IHV H) as (x&Hx1&Hx2).
exists x.
split; auto.
now constructor 2.
-
intros (x&<-&H).
Admitted.

Lemma In_replace (X : Type) (n : nat) (xs : Vector.t X n) (i : Fin.t n) (x y : X) : In y (replace xs i x) -> (x = y \/ In y xs).
Proof.
revert i x y.
induction xs; intros; cbn in *.
-
inv i.
-
dependent destruct i; cbn in *; apply In_cons in H as [-> | H]; auto; try now (right; constructor).
Admitted.

Lemma In_replace' (X : Type) (n : nat) (xs : Vector.t X n) (i : Fin.t n) (x y : X) : In y (replace xs i x) -> x = y \/ exists j, i <> j /\ xs[@j] = y.
Proof.
revert i x y.
induction xs; intros; cbn -[nth] in *.
-
inv i.
-
dependent destruct i; cbn -[nth] in *.
+
apply In_cons in H as [->|H].
*
tauto.
*
apply vect_nth_In' in H as (j&H).
right.
exists (Fin.FS j).
split.
discriminate.
cbn.
assumption.
+
apply In_cons in H as [->|H].
*
right.
exists Fin.F1.
split.
discriminate.
cbn.
reflexivity.
*
specialize (IHxs _ _ _ H) as [-> | (j&IH1&IH2)]; [ tauto | ].
right.
exists (Fin.FS j).
split.
now intros -> % Fin.FS_inj.
cbn.
Admitted.

Goal Vector.In (Fin.F1 (n := 10)) [|Fin1; Fin2; Fin3 |] -> False.
Proof.
intros H.
Admitted.

Goal Vector.In (Fin.F1 (n := 10)) (map (Fin.FS) [|Fin0; Fin1; Fin2|]) -> False.
Proof.
intros H.
Admitted.

Lemma tolist_In (X : Type) (n : nat) (xs : Vector.t X n) (x : X) : Vector.In x xs <-> List.In x xs.
Proof.
split; intros H.
-
induction H; cbn; auto.
-
induction xs; cbn in *; auto.
Admitted.

Lemma vector_to_list_inj (X : Type) (n : nat) (xs ys : Vector.t X n) : Vector.to_list xs = Vector.to_list ys -> xs = ys.
Proof.
revert ys.
induction xs as [ | x n xs IH]; intros; cbn in *.
-
destruct_vector.
reflexivity.
-
destruct_vector.
cbn in *.
inv H.
f_equal.
Admitted.

Lemma vector_to_list_length (X : Type) (n : nat) (xs : Vector.t X n) : length(Vector.to_list xs) = n.
Proof.
induction xs as [ | x n xs IH].
-
now cbn.
-
change (S (length xs) = S n).
Admitted.

Lemma vector_rev_append_tail_to_list A (n m: nat) (v : Vector.t A n) (w : Vector.t A m): Vector.to_list (Vector.rev_append_tail v w) = (List.rev (Vector.to_list v) ++ Vector.to_list w)%list.
Proof.
unfold Vector.to_list.
revert v m w.
induction n;intros v;dependent destruct v;cbn.
reflexivity.
intros.
specialize IHn with (w:=h:::w).
cbn in *.
rewrite IHn.
autorewrite with list.
Admitted.

Lemma vector_rev_to_list A (n : nat) (v : Vector.t A n): Vector.to_list (Vector.rev v) = List.rev (Vector.to_list v).
Proof.
unfold Vector.rev,Vector.rev_append.
specialize (vector_rev_append_tail_to_list v [| |]) as H'.
cbn in H'.
autorewrite with list in H'.
rewrite <- H'.
generalize (Vector.rev_append_tail v [| |]).
generalize (Plus.plus_tail_plus n 0).
generalize (Plus.tail_plus n 0).
generalize (plus_n_O n).
intros -> ? <-.
rewrite <- plus_n_O.
Admitted.

Lemma vector_map_to_list A B (f : A -> B)(n : nat) (v : Vector.t A n): Vector.to_list (Vector.map f v) = List.map f (Vector.to_list v).
Proof.
unfold Vector.map, Vector.to_list.
revert v;induction n;intros v;dependent destruct v;cbn.
easy.
Admitted.

Lemma eq_nth_iff' X n (v w : Vector.t X n): (forall i : Fin.t n, v[@i] = w[@i]) -> v = w.
Proof.
intros.
eapply Vector.eq_nth_iff.
Admitted.

Lemma vector_fold_right_to_list (A B : Type) (f : A -> B -> B) (n : nat) (v : Vector.t A n) (a : B): Vector.fold_right f v a = List.fold_right f a (Vector.to_list v).
Proof.
unfold Vector.to_list.
induction n.
all:destruct_vector.
Admitted.

Lemma vector_fold_left_to_list (A B : Type) (f : A -> B -> A) (n : nat) (v : VectorDef.t B n) (a : A): VectorDef.fold_left f a v = List.fold_left f (Vector.to_list v) a.
Proof.
unfold Vector.to_list.
induction n in v,a|-*.
all:destruct_vector.
Admitted.

Lemma vector_fold_left_right (A B : Type) (f : A -> B -> A) (n : nat) (v : VectorDef.t B n) (a : A): Vector.fold_left f a v = Vector.fold_right (fun x y => f y x) (Vector.rev v) a.
Proof.
rewrite vector_fold_right_to_list, vector_fold_left_to_list.
setoid_rewrite <- List.rev_involutive at 2.
rewrite List.fold_left_rev_right.
f_equal.
rewrite vector_rev_to_list,List.rev_involutive.
Admitted.

Lemma vector_nth_rev_append_tail_r' X n n' (v : Vector.t X n) (v' : Vector.t X n') i (i':=proj1_sig (Fin.to_nat i)) j (H: i' = n + j) H': (Vector.rev_append_tail v v') [@ i] = v'[@ Fin.of_nat_lt j H'].
Proof.
revert dependent n'.
revert j.
depind v;cbn;intros.
{
f_equal.
subst j.
erewrite Fin.of_nat_ext, Fin.of_nat_to_nat_inv.
easy.
}
erewrite IHv with (v':=h::v') (j:=S j).
2:nia.
cbn.
f_equal.
eapply Fin.of_nat_ext.
Unshelve.
Admitted.

Lemma vector_eqb_spec X n eqb: (forall (x1 x2 : X) , reflect (x1 = x2) (eqb x1 x2)) -> forall x y , reflect (x=y) (Vector.eqb (n:=n) eqb x y).
Proof with try (constructor;congruence).
intros Hf x y.
apply iff_reflect.
symmetry.
apply Vector.eqb_eq.
symmetry.
apply reflect_iff.
eauto.
