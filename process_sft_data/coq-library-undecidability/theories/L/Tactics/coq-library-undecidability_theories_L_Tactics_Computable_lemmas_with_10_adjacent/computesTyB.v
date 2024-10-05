From Undecidability.L Require Export Util.L_facts Tactics.Extract.
Require Import Undecidability.Shared.Libs.PSL.Bijection String.
Class registered (X : Type) := mk_registered { enc :> encodable X ; (* the encoding function for X *) proc_enc : forall x, proc (enc x) ; (* encodings need to be a procedure *) inj_enc : injective enc (* encoding is injective *) }.
Hint Mode registered + : typeclass_instances.
Arguments enc : simpl never.
Inductive TT : Type -> Type := TyB t (R : registered t) : TT t | TyArr t1 t2 (tt1 : TT t1) (tt2 : TT t2) : TT (t1 -> t2).
Existing Class TT.
Existing Instance TyB.
Existing Instance TyArr.
Arguments TyB _ {_}.
Arguments TyArr {_} {_} _ _.
Hint Mode TT + : typeclass_instances.
Notation "! X" := (TyB X) (at level 69).
Notation "X ~> Y" := (TyArr X Y) (right associativity, at level 70).
Fixpoint computes {A} (tau : TT A) {struct tau}: A -> L.term -> Type := match tau with !_ => fun x xInt => (xInt = enc x) | @TyArr A B tau1 tau2 => fun f t_f => proc t_f * forall (a : A) t_a, computes tau1 a t_a -> {v : term & (app t_f t_a >* v) * computes tau2 (f a) v} end%type.
Class computable X {ty : TT X} (x : X) : Type := { ext : extracted x; extCorrect : computes ty x ext; }.
Global Arguments computable {X} {ty} x.
Global Arguments extCorrect {X} ty x {computable} : simpl never.
Global Arguments ext {X} {ty} x {computable} : simpl never.
Hint Mode computable + - +: typeclass_instances.
Hint Extern 4 (@extracted ?t ?f) => let ty := constr:(_ : TT t) in notypeclasses refine (ext (ty:=ty) f) : typeclass_instances.
Typeclasses Opaque ext.
Instance reg_is_ext ty (R : registered ty) (x : ty) : computable x.
Proof.
exists (enc x).
reflexivity.
Defined.
Instance extApp' t1 t2 {tt1:TT t1} {tt2 : TT t2} (f: t1 -> t2) (x:t1) (Hf : computable f) (Hx : computable x) : computable (f x).
Proof.
destruct Hf, Hx.
edestruct extCorrect0 as [? H].
edestruct H as (?&?&?).
eassumption.
now eapply (@Build_computable _ _ _ x0).
Defined.
Fixpoint extEq t {tt:TT t} : t -> t -> Prop:= match tt with TyB _ _ => eq | @TyArr t1 t2 tt1 tt2 => fun f f' => forall (x : t1), extEq (f x) (f' x) end.
Instance extEq_refl t (tt:TT t): Reflexive (extEq (tt:=tt)).
Proof.
unfold Reflexive.
induction tt;cbn.
-
reflexivity.
-
intros f x.
eauto.
Opaque computes.

Lemma computesProc t (ty : TT t) (f : t) fInt: computes ty f fInt -> proc fInt.
Proof.
destruct ty.
-
intros ->.
unfold enc.
now destruct R.
-
Admitted.

Lemma proc_ext X (ty : TT X) (x : X) ( H : computable x) : proc (ext x).
Proof.
unfold ext.
destruct H.
Admitted.

Instance reg_is_ext ty (R : registered ty) (x : ty) : computable x.
Proof.
exists (enc x).
Admitted.

Instance extApp' t1 t2 {tt1:TT t1} {tt2 : TT t2} (f: t1 -> t2) (x:t1) (Hf : computable f) (Hx : computable x) : computable (f x).
Proof.
destruct Hf, Hx.
edestruct extCorrect0 as [? H].
edestruct H as (?&?&?).
eassumption.
Admitted.

Lemma extApp t1 t2 {tt1:TT t1} {tt2 : TT t2} (f: t1 -> t2) (x:t1) (Hf : computable f) (Hx : computable x) : app (ext f) (ext x) >* ext (f x).
Proof.
unfold ext, extApp'.
destruct Hf, Hx.
destruct extCorrect0 as (? & correct0).
destruct correct0 as (?&?&?).
Admitted.

Lemma ext_is_enc t1 (R:registered t1) (x: t1) (Hf : computable x) : @ext _ _ x Hf = enc x.
Proof.
Admitted.

Lemma computesExpStart t1 (tt1 : TT t1) (f : t1) (fExt : term): proc fExt -> {v :term & computesExp tt1 f fExt v} -> computes tt1 f fExt.
Proof.
intros ? (?&?&?).
replace fExt with x.
tauto.
apply unique_normal_forms.
eapply e.
eapply H.
destruct e as [e ?].
Admitted.

Lemma computesExpStep t1 t2 (tt1 : TT t1) (tt2 : TT t2) (f : t1 -> t2) (s:term) (fExt : term): eval s fExt -> closed s -> (forall (y : t1) (yExt : term), computes tt1 y yExt -> {v : term & computesExp tt2 (f y) (app s yExt) v}%type) -> computesExp (tt1 ~> tt2) f s fExt.
Proof.
intros ? ? H.
split.
assumption.
split.
split.
now rewrite <-H0.
now destruct H0.
intros ? ? exted.
edestruct H as (v&?&?).
eassumption.
eexists v.
split.
rewrite H0 in e.
now rewrite e.
Admitted.

Lemma computesTyArr t1 t2 (tt1 : TT t1) (tt2 : TT t2) f fExt : proc fExt -> (forall (y : t1) (yExt : term), computes tt1 y yExt -> {v : term & eval (app fExt yExt) v * (proc v -> computes tt2 (f y) v)}%type) -> computes (tt1 ~> tt2) f fExt.
Proof.
intros ? H'.
split;[assumption|].
intros y yExt yCorrect.
edestruct H' as (?&(R&?) & H'').
eassumption.
eexists.
split.
eassumption.
eapply H''.
split.
2:assumption.
rewrite <- R.
apply app_closed.
now destruct H.
specialize (computesProc yCorrect) as [].
Admitted.

Instance extEq_refl t (tt:TT t): Reflexive (extEq (tt:=tt)).
Proof.
unfold Reflexive.
induction tt;cbn.
-
reflexivity.
-
intros f x.
Admitted.

Lemma computesExt X (tt : TT X) (x x' : X) s: extEq x x' -> computes tt x s -> computes tt x' s.
Proof.
induction tt in x,x',s |-*;intros eq.
-
inv eq.
tauto.
-
cbn in eq|-*.
intros [H1 H2].
split.
1:tauto.
intros y t exts.
specialize (H2 y t exts) as (v&R&H2).
exists v.
split.
1:assumption.
eapply IHtt2.
2:now eassumption.
Admitted.

Lemma computableExt X (tt : TT X) (x x' : X): extEq x x' -> computable x -> computable x'.
Proof.
intros ? (s&?).
exists s.
Admitted.

Lemma registerAs X Y `{registered X} (f:Y -> X) : injective f -> registered Y.
Proof.
intros Hf.
eexists (fun x => enc (f x)).
now destruct H.
intros ? ? ?.
Admitted.

Lemma computesTyB (t:Type) (x:t) `{registered t}: computes (TyB t) x (ext x).
Proof.
unfold ext.
now destruct R.
