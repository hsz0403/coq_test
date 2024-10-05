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

Lemma total_decodable_closed_new k (s : L.term) { Y} `{linTimeDecodable Y} : (forall v : Vector.t X k, forall o : L.term, L_facts.eval (apply_to s v) o -> exists l : Y, o = enc l) -> exists s', closed s' /\ forall v : Vector.t X k, forall o, L_facts.eval (apply_to s' v) o <-> L_facts.eval (apply_to s v) o.
Proof using Hcmp.
intros Htot.
assert (closed Eval) as He.
{
unfold Eval.
Lproc.
}
exists (many_lam k (ext (decode Y) (Eval (apply_encs_to (enc s) k)) (lam 0) (ext false))).
split.
{
intros n u.
rewrite subst_many_lam.
cbn -[Eval].
repeat (rewrite subst_closed; [| now Lproc]).
rewrite subst_apply_encs_to.
2:lia.
now repeat (rewrite subst_closed; [| now Lproc]).
}
intros v.
revert s Htot.
depind v; intros s Htot o.
-
cbn.
specialize (Htot (Vector.nil _)).
cbn in Htot.
eapply logical; clear o.
+
intros o Hl.
pose proof Hl as [y ->] % Htot.
eapply eval_Eval in Hl.
rewrite Hl.
split.
2: Lproc.
Lsimpl.
rewrite decode_correct.
now Lsimpl.
+
intros Hrev o Heval.
match type of Heval with L_facts.eval ?l _ => assert (Hc : converges l) by eauto end.
eapply app_converges in Hc as [[[_ Hc]%app_converges _] % app_converges _].
eapply Eval_converges in Hc as [o' [Hc Hl]].
rewrite Hc.
enough (o = o').
subst.
now econstructor; eauto.
eapply eval_unique.
eapply Heval.
eapply Hrev.
rewrite Hc.
split; eauto.
reflexivity.
-
cbn -[apply_to tabulate many_vars].
rewrite !apply_to_cons.
specialize (IHv (s (enc h))).
rewrite <- IHv.
+
unfold apply_encs_to.
cbn -[many_vars].
rewrite many_vars_S.
cbn.
eapply equiv_eval_equiv.
etransitivity.
eapply apply_to_equiv'.
eapply beta_red.
Lproc.
reflexivity.
rewrite subst_many_lam.
cbn [subst].
replace (n + 0) with n by lia.
rewrite He.
assert (closed (ext (decode Y))) as H2 by Lproc.
unfold closed in H2.
rewrite H2.
clear H2.
cbn.
assert (closed (ext false)) as H2 by Lproc.
unfold closed in H2.
rewrite H2.
clear H2.
unfold apply_to.
rewrite many_beta.
rewrite !many_subst_app.
repeat (rewrite many_subst_closed; [ | now Lproc]).
symmetry.
rewrite many_beta.
rewrite !many_subst_app.
repeat (rewrite many_subst_closed; [ | now Lproc]).
2:{
clear.
induction v; cbn; intros ? Hi.
inversion Hi.
inv Hi.
Lproc.
eapply IHv.
eapply Eqdep_dec.inj_pair2_eq_dec in H2.
subst.
eauto.
eapply nat_eq_dec.
}
2:{
clear.
induction v; cbn; intros ? Hi.
inversion Hi.
inv Hi.
Lproc.
eapply IHv.
eapply Eqdep_dec.inj_pair2_eq_dec in H2.
subst.
eauto.
eapply nat_eq_dec.
}
repeat (eapply equiv_app_proper; try reflexivity).
clear.
fold (@apply_encs_to (enc (s (enc h))) n).
fold (apply_encs_to (ext L.app (enc s) (ext (@enc X _) n)) n).
rewrite subst_apply_encs_to.
cbn.
repeat (rewrite subst_closed; [ | now Lproc]).
rewrite Nat.eqb_refl.
rewrite !many_subst_apply_encs_to.
*
rewrite equiv_fold_left.
reflexivity.
now Lsimpl.
*
Lproc.
*
clear.
induction v; cbn; intros ? Hi.
inversion Hi.
inv Hi.
Lproc.
eapply IHv.
eapply Eqdep_dec.inj_pair2_eq_dec in H2.
subst.
eauto.
eapply nat_eq_dec.
*
Lproc.
*
clear.
induction v; cbn; intros ? Hi.
inversion Hi.
inv Hi.
Lproc.
eapply IHv.
eapply Eqdep_dec.inj_pair2_eq_dec in H2.
subst.
eauto.
eapply nat_eq_dec.
*
lia.
+
intros.
now apply (Htot (h :: v0)).
