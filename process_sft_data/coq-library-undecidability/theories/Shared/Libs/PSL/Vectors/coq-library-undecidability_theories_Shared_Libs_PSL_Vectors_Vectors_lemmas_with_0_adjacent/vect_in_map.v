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

Lemma vect_in_map (X Y : Type) (n : nat) (f : X -> Y) (V : Vector.t X n) (x : X) : In x V -> In (f x) (map f V).
Proof.
induction 1; cbn; constructor; auto.
