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

Lemma vect_map_injective X Y n (f : X -> Y) (v1 v2 : Vector.t X n) : (forall x y, f x = f y -> x = y) -> map f v1 = map f v2 -> v1 = v2.
Proof.
intros Inj Eq.
induction n; cbn in *.
-
dependent destruct v1.
dependent destruct v2; reflexivity.
-
dependent destruct v1.
dependent destruct v2.
cbn in *.
eapply cons_inj in Eq as (-> % Inj &?).
f_equal.
Admitted.

Lemma replace_nth X n (v : Vector.t X n) i (x : X) : (Vector.replace v i x) [@i] = x.
Proof.
Admitted.

Lemma replace_nth2 X n (v : Vector.t X n) i j (x : X) : i <> j -> (Vector.replace v i x) [@j] = v[@j].
Proof.
revert v.
pattern i, j.
revert n i j.
eapply Fin.rect2; intros; try congruence.
-
revert f H.
pattern v.
revert n v.
eapply Vector.caseS.
cbn.
reflexivity.
-
revert f H.
pattern v.
revert n v.
eapply Vector.caseS.
cbn.
reflexivity.
-
revert g f H H0.
pattern v.
revert n v.
eapply Vector.caseS.
Admitted.

Lemma destruct_vector_nil (X : Type) : forall v : Vector.t X 0, v = [| |].
Proof.
Admitted.

Lemma In_nil (X : Type) (x : X) : ~ In x [| |].
Proof.
intros H.
Admitted.

Lemma In_cons (X : Type) (n : nat) (x y : X) (xs : Vector.t X n) : In y (x ::: xs) -> x = y \/ In y xs.
Proof.
intros H.
Admitted.

Lemma in_dec_correct (n : nat) (x : X) (xs : Vector.t X n) : in_dec x xs = true <-> In x xs.
Proof.
split; intros.
{
induction xs; cbn in *.
-
congruence.
-
decide (x = h) as [ -> | D].
+
constructor.
+
constructor.
now apply IHxs.
}
{
induction H; cbn.
-
have (x = x).
-
decide (x = x0).
+
reflexivity.
+
apply IHIn.
Admitted.

Lemma vect_nth_In (v : Vector.t A n) (i : Fin.t n) (x : A) : Vector.nth v i = x -> Vector.In x v.
Proof.
induction n; cbn in *.
-
inv i.
-
dependent destruct v.
Admitted.

Lemma vect_nth_In' (v : Vector.t A n) (x : A) : Vector.In x v -> exists i : Fin.t n, Vector.nth v i = x.
Proof.
induction n; cbn in *.
-
inversion 1.
-
dependent destruct v.
destruct_vector_in.
+
exists Fin.F1.
auto.
+
specialize (IHn0 _ H) as (i&<-).
exists (Fin.FS i).
Admitted.

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
Admitted.

Lemma nth_tabulate n (f : Fin.t n -> X) (m : Fin.t n) : Vector.nth (tabulate f) m = f m.
Proof.
induction m.
-
cbn.
reflexivity.
-
cbn.
rewrite IHm.
Admitted.

Lemma in_tabulate n (f : Fin.t n -> X) (x : X) : In x (tabulate (n := n) f) <-> exists i : Fin.t n, x = f i.
Proof.
split.
{
revert f x.
induction n; intros f x H.
-
cbn in *.
inv H.
-
cbn in *.
apply In_cons in H as [ <- | H ].
+
eauto.
+
specialize (IHn (fun m => f (Fin.FS m)) _ H) as (i&IH).
eauto.
}
{
intros (i&Hi).
induction i; cbn in *; subst; econstructor; eauto.
Admitted.

Lemma Vector_tabulate_const {n} (c : X) f : (forall n, f n = c) -> tabulate f = Vector.const c n.
Proof.
induction n; cbn.
-
reflexivity.
-
intros.
rewrite H.
f_equal.
eapply IHn.
intros.
Admitted.

Lemma Vector_map_tabulate {X Y n} (f : X -> Y) g : Vector.map (n:=n) f (tabulate g) = tabulate (fun x => f (g x)).
Proof.
induction n; cbn.
-
reflexivity.
-
f_equal.
Admitted.

Lemma destruct_vector_cons (X : Type) (n : nat) : forall v : Vector.t X (S n), { h : X & { v' : Vector.t X n | v = h ::: v' }}.
Proof.
revert n.
apply caseS.
eauto.
