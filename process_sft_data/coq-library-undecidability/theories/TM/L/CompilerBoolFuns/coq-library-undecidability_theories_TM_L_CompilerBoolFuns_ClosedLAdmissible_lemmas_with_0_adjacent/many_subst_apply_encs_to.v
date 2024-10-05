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

Lemma many_subst_apply_encs_to s n (u : Vector.t term n) : closed s -> (forall x, Vector.In x u -> closed x) -> many_subst (apply_encs_to s n) 0 u = ((Vector.fold_left (fun s n => ext L.app s (ext (@enc X _) n)) s u)).
Proof.
induction u in s |- *; intros Hs Hu; cbn -[many_vars].
-
reflexivity.
-
unfold apply_encs_to.
rewrite many_vars_S.
cbn.
unfold apply_encs_to in IHu.
rewrite <- IHu.
fold (apply_encs_to (ext L.app s (ext (@enc X _) n)) n).
rewrite subst_apply_encs_to.
2:lia.
unfold apply_encs_to.
repeat f_equal.
cbn.
repeat (rewrite subst_closed; [| now Lproc]).
now rewrite Nat.eqb_refl.
assert (closed h) as Hh.
eapply Hu.
econstructor.
Lproc.
intros.
eapply Hu.
now econstructor.
