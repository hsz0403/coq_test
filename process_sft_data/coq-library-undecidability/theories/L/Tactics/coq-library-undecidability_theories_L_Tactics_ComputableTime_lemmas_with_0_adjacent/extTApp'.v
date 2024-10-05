From Undecidability.L Require Export Tactics.Computable.
Fixpoint timeComplexity t (tt: TT t) : Type := match tt with ! _ => unit | @TyArr t1 t2 tt1 tt2 => t1 -> timeComplexity tt1 -> (nat*timeComplexity tt2) end.
Arguments timeComplexity : clear implicits.
Arguments timeComplexity _ {_}.
Fixpoint computesTime {t} (ty : TT t) : forall (x:t) (xInt :term) (xTime :timeComplexity t), Type := match ty with !_ => fun x xInt _=> xInt = enc x | @TyArr t1 t2 tt1 tt2 => fun f fInt fTime => proc fInt * forall (y : t1) yInt (yTime:timeComplexity t1), computesTime y yInt yTime -> let fyTime := fTime y yTime in {v : term & (redLe (fst fyTime) (app fInt yInt) v) * computesTime (f y) v (snd fyTime)} end%type.
Arguments computesTime {_} _ _ _ _.
Class computableTime {X : Type} (ty : TT X) (x : X) evalTime: Type := { extT : extracted x; extTCorrect : computesTime ty x extT evalTime }.
Global Arguments computableTime {X} {ty} x.
Global Arguments extT {X} {ty} x {_ computableTime} : simpl never.
Global Arguments extTCorrect {X} ty x {_ computableTime} : simpl never.
Definition evalTime X ty x evalTime (computableTime : @computableTime X ty x evalTime):=evalTime.
Global Arguments evalTime {X} {ty} x {evalTime computableTime}.
Hint Extern 3 (@extracted ?t ?f) => let ty := constr:(_ : TT t) in notypeclasses refine (extT (ty:=ty) f) : typeclass_instances.
Hint Mode computableTime + - + -: typeclass_instances.
Notation "'computableTime'' f" := (@computableTime _ ltac:(let t:=type of f in refine (_ : TT t);exact _) f) (at level 0,only parsing).
Local Fixpoint notHigherOrder t (ty : TT t) := match ty with TyArr _ _ (TyB _ _) ty2 => notHigherOrder ty2 | TyB _ _ => True | _ => False end.
Local Lemma computesTime_computes_intern s t (ty: TT t) f evalTime: notHigherOrder ty -> computesTime ty f s evalTime -> computes ty f s.
Proof.
revert s f.
induction ty;intros s f H int.
-
exact int.
-
destruct ty1; cbn in H.
2:tauto.
clear IHty1.
cbn.
destruct int as [ps ints].
cbn in ints.
split.
tauto.
intros.
subst.
edestruct (ints a _ tt eq_refl) as(v&R'&?).
exists v.
split.
eapply redLe_star_subrelation.
all:eauto.
Defined.
Instance reg_is_extT ty (R : registered ty) (x : ty): computableTime x tt.
Proof.
exists (enc x).
split;constructor.
Defined.
Instance extTApp' t1 t2 {tt1:TT t1} {tt2 : TT t2} (f: t1 -> t2) (x:t1) fT xT (Hf : computableTime f fT) (Hx : computableTime x xT) : computableTime (f x) (snd (fT x xT)).
Proof.
destruct Hf as [fInt H], Hx as [xInt xInts].
eexists (projT1 ((snd H) x xInt xT xInts)).
destruct H as [p fInts].
cbn in *.
destruct (fInts x xInt xT xInts) as (v&E&fxInts).
eassumption.
Defined.
Definition computesTimeIf {t} (ty : TT t) (f:t) (fInt : term) (P:timeComplexity t-> Prop) : Type := forall fT, P fT -> computesTime ty f fInt fT.
Arguments computesTimeIf {_} _ _ _ _.
Definition computesTimeExp {t} (ty : TT t) (f:t) (s:term) (i:nat) (fInt : term) (fT:timeComplexity t) : Type := evalLe i s fInt * computesTime ty f fInt fT.
Arguments computesTimeExp {_} _ _ _ _ _ _.
Definition cnst {X} (x:X):nat.
Proof.
exact 0.
Definition callTime X (fT : X -> unit -> nat * unit) x: nat := fst (fT x tt).
Arguments callTime / {_}.
Definition callTime2 X Y (fT : X -> unit -> nat * (Y -> unit -> nat * unit)) x y : nat := let '(k,f):= fT x tt in k + fst (f y tt).
Arguments callTime2 / {_ _}.
Fixpoint timeComplexity_leq (t : Type) (tt : TT t) {struct tt} : timeComplexity t -> timeComplexity t -> Prop := match tt in (TT t) return timeComplexity t -> timeComplexity t -> Prop with | ! t0 => fun _ _ => True | @TyArr t1 t2 _ tt2 => fun f f' : timeComplexity (_ -> _) => forall (x:t1) xT, (fst (f x xT)) <= (fst (f' x xT)) /\ timeComplexity_leq (snd (f x xT)) (snd (f' x xT)) end.

Instance extTApp' t1 t2 {tt1:TT t1} {tt2 : TT t2} (f: t1 -> t2) (x:t1) fT xT (Hf : computableTime f fT) (Hx : computableTime x xT) : computableTime (f x) (snd (fT x xT)).
Proof.
destruct Hf as [fInt H], Hx as [xInt xInts].
eexists (projT1 ((snd H) x xInt xT xInts)).
destruct H as [p fInts].
cbn in *.
destruct (fInts x xInt xT xInts) as (v&E&fxInts).
eassumption.
