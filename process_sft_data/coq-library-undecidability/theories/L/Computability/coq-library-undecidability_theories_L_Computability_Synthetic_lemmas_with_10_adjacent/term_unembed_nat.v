From Undecidability.L Require Import Computability.MuRec.
From Undecidability.L.Datatypes Require Import LNat LOptions LProd Lists.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
Require Import Datatypes.
Inductive is_computable {A} {t : TT A} (a : A) : Prop := C : computable a -> is_computable a.
Notation enumerates f p := (forall x, p x <-> exists n : nat, f n = Some x).
Definition L_decidable {X} `{registered X} (P : X -> Prop) := exists f : X -> bool, is_computable f /\ forall x, P x <-> f x = true.
Definition L_enumerable {X} `{registered X} (p : X -> Prop) := exists f : nat -> option X, is_computable f /\ (enumerates f p).
Definition L_recognisable {X} `{registered X} (p : X -> Prop) := exists f : X -> nat -> bool, is_computable f /\ forall x, p x <-> exists n, f x n = true.
Definition L_recognisable' {X} `{registered X} (p : X -> Prop) := exists s : term, forall x, p x <-> converges (L.app s (enc x)).
Section L_enum_rec.
Variable X : Type.
Context `{registered X}.
Variable (p : X -> Prop).
Hypotheses (f : nat -> option X) (c_f : computable f) (H_f : enumerates f p).
Hypotheses (d : X -> X -> bool) (c_d : computable d) (H_d : forall x y, reflect (x = y) (d x y)).
Definition test := (fun x n => match f n with Some y => d x y | None => false end).
Instance term_test : computable test.
Proof using c_f c_d.
extract.
Import HOAS_Notations.
End L_enum_rec.
Definition opt_to_list n := match nat_enum n with Some x => [x] | None => [] end.
Instance term_opt_to_list : computable opt_to_list.
Proof.
extract.
Definition L_nat := cumul (opt_to_list).
Instance term_L_nat : computable L_nat.
Proof.
unfold L_nat.
unfold cumul.
extract.
Require Import Undecidability.Shared.embed_nat Nat.
Definition F' := (fix F (n : nat) : nat := match n with | 0 => 0 | S n0 => S n0 + F n0 end).
Instance term_F' : computable F'.
Proof.
extract.
Definition F'' := (fix F (n0 : nat) : nat * nat := match n0 with | 0 => (0, 0) | S n1 => match F n1 with | (0, y) => (S y, 0) | (S x0, y) => (x0, S y) end end).
Instance term_F'' : computable F''.
Proof.
extract.
Instance term_embed_nat : computable embed.
Proof.
change (computable (fun '(x, y) => y + F' (y + x))).
extract.
Instance term_unembed_nat : computable unembed.
Proof.
unfold unembed.
change (computable F'').
exact term_F''.
Definition lenumerates {X} L (p : X -> Prop) := cumulative L /\ (forall x : X, p x <-> (exists m : nat, x el L m)).
Definition L_enum {X} `{registered X} (p : X -> Prop) := exists L, is_computable L /\ lenumerates L p.
Definition F1 {X} (T : nat -> list X) := (fun n => let (n, m) := unembed n in nth_error (T n) m).
Instance term_F1 {X} {H : registered X} : @computable ((nat -> list X) -> nat -> option X) ((! nat ~> ! list X) ~> ! nat ~> ! option X) (@F1 X).
Proof.
extract.
Import L_Notations.

Instance term_test : computable test.
Proof using c_f c_d.
Admitted.

Lemma proc_test (x : X) : proc [L_HOAS λ y, !!(ext test) !!(enc x) y].
Proof.
cbn.
Admitted.

Lemma L_enumerable_recognisable : L_recognisable' p.
Proof using c_f c_d H_f H_d.
exists [L_HOAS λ x, !!mu (λ y, !!(ext test) x y)].
intros.
split; intros.
-
eapply H_f in H0 as [n H0].
edestruct (mu_complete (proc_test x)) with (n := n).
+
intros.
exists (test x n0).
cbn.
now Lsimpl.
+
cbn.
Lsimpl.
unfold test.
rewrite H0.
destruct (H_d x x); intuition.
+
exists (ext x0).
split; try Lproc.
cbn.
Lsimpl.
now rewrite H1.
-
destruct H0 as (v & ? & ?).
edestruct (mu_sound (proc_test x)) with (v := v) as (n & ? & ? & _).
+
intros.
exists (test x n).
cbn.
now Lsimpl.
+
Lproc.
+
rewrite <- H0.
symmetry.
cbn.
now Lsimpl.
+
subst.
eapply H_f.
exists n.
assert ([L_HOAS (λ y, !! (ext test) !! (enc x) y) !!(ext n)] == ext (test x n)).
cbn.
now Lsimpl.
cbn in *.
rewrite H2 in *.
eapply unique_normal_forms in H3;[|Lproc..].
eapply inj_enc in H3.
unfold test in H3.
destruct (f n); inv H3.
Admitted.

Instance term_opt_to_list : computable opt_to_list.
Proof.
Admitted.

Instance term_L_nat : computable L_nat.
Proof.
unfold L_nat.
unfold cumul.
Admitted.

Instance term_F' : computable F'.
Proof.
Admitted.

Instance term_F'' : computable F''.
Proof.
Admitted.

Instance term_embed_nat : computable embed.
Proof.
change (computable (fun '(x, y) => y + F' (y + x))).
Admitted.

Lemma projection X Y {HX : registered X} {HY : registered Y} (p : X * Y -> Prop) : L_enumerable p -> L_enumerable (fun x => exists y, p (x,y)).
Proof.
intros (f & [cf] & ?).
exists (fun n => match f n with Some (x, y) => Some x | None => None end).
split.
-
econstructor.
extract.
-
intros; split.
+
intros [y ?].
eapply H in H0 as [n].
exists n.
now rewrite H0.
+
intros [n ?].
destruct (f n) as [ [] | ] eqn:E; inv H0.
exists y.
eapply H.
Admitted.

Lemma L_enumerable_ext X `{registered X} p q : L_enumerable p -> (forall x : X, p x <-> q x) -> L_enumerable q.
Proof.
intros (f & cf & Hf) He.
exists f; split; eauto.
intros ?.
rewrite <- He.
Admitted.

Instance term_F1 {X} {H : registered X} : @computable ((nat -> list X) -> nat -> option X) ((! nat ~> ! list X) ~> ! nat ~> ! option X) (@F1 X).
Proof.
Admitted.

Lemma L_enumerable_enum {X} `{registered X} (p : X -> Prop) : L_enum p -> L_enumerable p.
Proof.
intros (f & [cf] & Hf).
exists (F1 f).
split.
-
econstructor.
extract.
-
destruct Hf as [CX HX].
intros x.
unfold F1.
Admitted.

Lemma L_enumerable_halt {X} `{registered X} (p : X -> Prop) : L_decidable (X := X * X) (fun '(x,y) => x = y) -> L_enumerable p -> p ⪯ converges.
Proof.
intros (d & [c_d] & H_d) (f & [c_f] & H_f).
edestruct L_enumerable_recognisable with (p := p) (d := fun x y => d (x,y)) (f := f); eauto.
-
extract.
-
intros.
specialize (H_d (x,y)).
destruct (d (x,y)); intuition.
-
Admitted.

Lemma L_recognisable'_recognisable {X} `{registered X} (p : X -> Prop) : L_recognisable p -> L_recognisable' p.
Proof.
intros (f & [c_f] & H_f).
exists (lam (mu (lam (ext f 1 0)))).
intros.
assert (((lam (mu (lam ((ext f 1) 0)))) (enc x)) >* mu (lam (ext f (enc x) 0))) by now Lsimpl.
rewrite H0.
rewrite mu_spec.
-
rewrite H_f.
split; intros [n]; exists n.
Lsimpl.
now rewrite H1.
eapply enc_extinj.
now assert ((lam (((ext f) (enc x)) 0)) (ext n) == enc (f x n)) as <- by now Lsimpl.
-
Lproc.
-
intros.
exists (f x n).
Admitted.

Lemma L_recognisable_halt {X} `{registered X} (p : X -> Prop) : L_recognisable p -> p ⪯ converges.
Proof.
intros.
eapply L_recognisable'_recognisable in H0 as (f & H_f).
Admitted.

Instance term_unembed_nat : computable unembed.
Proof.
unfold unembed.
change (computable F'').
exact term_F''.
