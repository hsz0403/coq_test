Require Import Equations.Equations.
From Undecidability.Shared.Libs.PSL Require Import Vectors.
From Coq Require Import Vector List.
From Undecidability.L Require Import L LTactics L_facts Functions.Eval Functions.Decoding Functions.Encoding.
From Undecidability.L.Datatypes Require Import LBool Lists LVector List.List_fold.
From Undecidability.L.Complexity.LinDecode Require Import LTDbool LTDlist LTDnat.
From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec NaryApp.
Import ListNotations.
Import VectorNotations.
Import L_Notations.
Definition L_computable_closed {k} (R : Vector.t nat k -> nat -> Prop) := exists s, closed s /\ forall v : Vector.t nat k, (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encNatL n)) s v) (encNatL m)) /\ (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encNatL n)) s v) o -> exists m, o = encNatL m).
Definition L_bool_computable_closed {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := exists s, closed s /\ forall v : Vector.t (list bool) k, (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) (encBoolsL m)) /\ (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) o -> exists m, o = encBoolsL m).
Local Instance vector_enc_bool {n} : computable (@enc (Vector.t (list bool) n) _).
Proof.
unfold enc.
cbn.
unfold enc.
cbn.
extract.
Definition apply_to (s : L.term) {k} {X : Type} `{registered X} (v : Vector.t X k) := many_app s (Vector.map enc v).
Section lemma.
Context {X : Type}.
Context {Hr : registered X}.
Context {Hcmp : computable (@enc X _)}.
Definition apply_encs_to (s : term) k := ((Vector.fold_left (fun s n => ext L.app s (ext (@enc X _) (var n))) s (many_vars k))).
End lemma.

Lemma L_computable_can_closed k R: L_computable_closed R <-> L_computable (k:=k) R.
Proof.
split.
-
intros (s & _ & H).
exists s.
exact H.
-
intros (s & H).
unshelve edestruct (@total_decodable_closed_new nat _ _ k s nat _ ) as (s' & Hcl & Hs'); try exact _.
+
intros v o.
rewrite <- eval_iff.
intros.
eapply (H v).
unfold apply_to in H0.
revert H0.
now rewrite many_app_eq_nat.
+
unfold apply_to in Hs'.
exists s'.
split.
Lproc.
intros v.
split.
*
intros m.
specialize (H v) as [H1 H2].
rewrite H1.
rewrite !eval_iff.
rewrite <- !many_app_eq_nat.
now rewrite Hs'.
*
intros o.
rewrite eval_iff.
rewrite <- many_app_eq_nat.
rewrite Hs'.
rewrite <- eval_iff.
rewrite many_app_eq_nat.
eapply H.
