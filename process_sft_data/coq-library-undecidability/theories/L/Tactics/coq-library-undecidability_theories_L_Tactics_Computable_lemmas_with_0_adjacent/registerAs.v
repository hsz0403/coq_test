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

Lemma registerAs X Y `{registered X} (f:Y -> X) : injective f -> registered Y.
Proof.
intros Hf.
eexists (fun x => enc (f x)).
now destruct H.
intros ? ? ?.
now eapply H, Hf in H0.
