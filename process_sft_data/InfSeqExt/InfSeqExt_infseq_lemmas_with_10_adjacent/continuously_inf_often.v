Ltac genclear H := generalize H; clear H.
Ltac clearall := repeat match goal with [H : _ |- _ ] => clear H end || match goal with [H : _ |- _ ] => genclear H end.
Section sec_infseq.
Variable T: Type.
CoInductive infseq : Type := Cons : T -> infseq -> infseq.
Definition hd (s:infseq) : T := match s with Cons x _ => x end.
Definition tl (s:infseq) : infseq := match s with Cons _ s => s end.
End sec_infseq.
Arguments Cons [T] _ _.
Arguments hd [T] _.
Arguments tl [T] _.
Arguments recons [T] _.
Section sec_modal_op_defn.
Variable T : Type.
Definition now (P: T->Prop) (s: infseq T) : Prop := match s with Cons x s => P x end.
Definition next (P: infseq T -> Prop) (s: infseq T) : Prop := match s with Cons x s => P s end.
Definition consecutive (R: T -> T -> Prop) (s: infseq T) : Prop := match s with Cons x1 (Cons x2 s) => R x1 x2 end.
CoInductive always1 (P: T->Prop) : infseq T -> Prop := | Always1 : forall x s, P x -> always1 P s -> always1 P (Cons x s).
CoInductive always (P: infseq T->Prop) : infseq T -> Prop := | Always : forall s, P s -> always P (tl s) -> always P s.
CoInductive weak_until (J P: infseq T->Prop) : infseq T -> Prop := | W0 : forall s, P s -> weak_until J P s | W_tl : forall s, J s -> weak_until J P (tl s) -> weak_until J P s.
Inductive until (J P: infseq T->Prop) : infseq T -> Prop := | U0 : forall s, P s -> until J P s | U_next : forall x s, J (Cons x s) -> until J P s -> until J P (Cons x s).
CoInductive release (J P: infseq T->Prop) : infseq T -> Prop := | R0 : forall s, P s -> J s -> release J P s | R_tl : forall s, P s -> release J P (tl s) -> release J P s.
Inductive eventually (P: infseq T->Prop) : infseq T -> Prop := | E0 : forall s, P s -> eventually P s | E_next : forall x s, eventually P s -> eventually P (Cons x s).
Definition inf_often (P: infseq T->Prop) (s: infseq T) : Prop := always (eventually P) s.
Definition continuously (P: infseq T->Prop) (s: infseq T) : Prop := eventually (always P) s.
Definition impl_tl (P Q: infseq T -> Prop) : infseq T -> Prop := fun s => P s -> Q s.
Definition and_tl (P Q: infseq T -> Prop) : infseq T -> Prop := fun s => P s /\ Q s.
Definition or_tl (P Q: infseq T -> Prop) : infseq T -> Prop := fun s => P s \/ Q s.
Definition not_tl (P : infseq T -> Prop) : infseq T -> Prop := fun s => ~ P s.
Definition True_tl : infseq T -> Prop := fun _ => True.
Definition False_tl : infseq T -> Prop := fun _ => False.
End sec_modal_op_defn.
Hint Unfold True_tl False_tl : core.
Arguments now [T] _ _.
Arguments next [T] _ _.
Arguments consecutive [T] _ _.
Arguments always [T] _ _.
Arguments always1 [T] _ _.
Arguments eventually [T] _ _.
Arguments weak_until [T] _ _ _.
Arguments until [T] _ _ _.
Arguments release [T] _ _ _.
Arguments inf_often [T] _ _.
Arguments continuously [T] _ _.
Arguments impl_tl [T] _ _ _.
Arguments and_tl [T] _ _ _.
Arguments or_tl [T] _ _ _.
Arguments not_tl [T] _ _.
Arguments True_tl {T} _.
Arguments False_tl {T} _.
Notation "A ->_ B" := (impl_tl A B) (right associativity, at level 90).
Notation "A /\_ B" := (and_tl A B) (right associativity, at level 80).
Notation "A \/_ B" := (or_tl A B) (right associativity, at level 85).
Notation "~_ A" := (not_tl A) (right associativity, at level 75).
Section sec_modal_op_lemmas.
Variable T : Type.
End sec_modal_op_lemmas.
Arguments always_inv [T inv] _ [s] _.
Arguments always_Cons [T x s P] _.
Arguments always_now [T x s P] _.
Arguments always_invar [T x s P] _.
Arguments always_tl [T s P] _.
Arguments always_not_false {T s}.
Arguments always_true {T s}.
Arguments always_and_tl [T P Q s] _ _.
Arguments always_always1 [T P s] _.
Arguments always1_always [T P s] _.
Arguments always_weak_until [T J P s] _.
Arguments always_release [T J P s] _.
Arguments always_inf_often [T P s] _.
Arguments always_continuously [T P s] _.
Arguments weak_until_Cons [T x s J P] _.
Arguments weak_until_always [T J J' P s] _ _.
Arguments until_weak_until [T J P s] _.
Arguments eventually_Cons [T x s P] _.
Arguments eventually_trans [T P Q inv] _ _ [s] _ _.
Arguments not_eventually [T P x s] _ _.
Arguments eventually_next [T s P] _.
Arguments eventually_always_cumul [T s P Q] _ _.
Arguments eventually_weak_until_cumul [T s P J] _ _.
Arguments weak_until_eventually [T P Q J] _ [s] _ _ _.
Arguments until_Cons [T x s J P] _.
Arguments until_eventually [T J P s] _.
Arguments release_Cons [T x s J P] _.
Arguments inf_often_invar [T x s P] _.
Arguments continuously_invar [T x s P] _.
Arguments continuously_and_tl [T P Q s] _ _.
Arguments continuously_inf_often [T P s] _.
Arguments now_monotonic [T P Q] _ [s] _.
Arguments next_monotonic [T P Q] _ [s] _.
Arguments consecutive_monotonic [T P Q] _ [s] _.
Arguments always_monotonic [T P Q] _ [s] _.
Arguments weak_until_monotonic [T P Q J K] _ _ [s] _.
Arguments until_monotonic [T P Q J K] _ _ [s] _.
Arguments release_monotonic [T P Q J K] _ _ [s] _.
Arguments eventually_monotonic [T P Q] _ _ _ [s] _ _.
Arguments eventually_monotonic_simple [T P Q] _ [s] _.
Arguments inf_often_monotonic [T P Q] _ [s] _.
Arguments continuously_monotonic [T P Q] _ [s] _.
Arguments not_eventually_always_not [T P s] _.
Arguments always_not_eventually [T P s] _ _.
Arguments eventually_not_always [T P s] _ _.
Arguments weak_until_always_not_always [T J P s] _ _.
Arguments always_not_eventually_not [T P s] _ _.
Arguments continuously_not_inf_often [T P s] _ _.
Arguments inf_often_not_continuously [T P s] _ _.
Arguments release_not_until [T J P s] _ _.
Arguments until_not_release [T J P s] _ _.
Arguments weak_until_not_until [T J P s] _ _.
Arguments until_not_weak_until [T J P s] _ _.
Arguments and_tl_comm {T P Q s}.
Arguments and_tl_assoc {T P Q R s}.
Arguments or_tl_comm {T P Q s}.
Arguments or_tl_assoc {T P Q R s}.
Arguments not_tl_or_tl {T P Q s}.
Arguments not_tl_or_tl_and_tl [T P Q s] _ _.
Ltac monotony := match goal with | [ |- now ?P ?s -> now ?Q ?s ] => apply now_monotonic | [ |- next ?P ?s -> next ?Q ?s ] => apply next_monotonic | [ |- consecutive ?P ?s -> consecutive ?Q ?s ] => apply consecutive_monotonic | [ |- always ?P ?s -> always ?Q ?s ] => apply always_monotonic | [ |- weak_until ?J ?P ?s -> weak_until ?K ?Q ?s ] => apply weak_until_monotonic | [ |- until ?J ?P ?s -> until ?K ?Q ?s ] => apply until_monotonic | [ |- release ?J ?P ?s -> release ?K ?Q ?s ] => apply release_monotonic | [ |- ?J ?s -> eventually ?P ?s -> eventually ?Q ?s ] => apply eventually_monotonic | [ |- continuously ?P ?s -> continuously ?Q ?s ] => apply continuously_monotonic | [ |- inf_often ?P ?s -> inf_often ?Q ?s ] => apply inf_often_monotonic end.

Lemma weak_until_eventually : forall (P Q J: infseq T -> Prop), (forall s, J s -> P s -> Q s) -> forall s, J s -> weak_until J Q s -> eventually P s -> eventually Q s.
Proof using.
intros P Q J impl s Js J_weak_until_Q ev.
genclear J_weak_until_Q; genclear Js.
induction ev as [s Ps | x s ev induc_hyp].
-
intros Js J_weak_until_Q.
constructor 1.
apply impl; assumption.
-
intros _ J_weak_until_Q.
cut (s = tl (Cons x s)); [idtac | reflexivity].
case J_weak_until_Q; clear J_weak_until_Q x.
*
constructor 1; assumption.
*
intros (x, s1) _ J_weak_until_Q e; simpl in *.
constructor 2.
generalize e J_weak_until_Q; clear e x.
case J_weak_until_Q; clear J_weak_until_Q s1.
+
clearall.
constructor 1; assumption.
+
intros s2 Js2 _ e J_weak_until_Q2.
rewrite e in induc_hyp; clear e.
Admitted.

Lemma eventually_or_tl_intror : forall (P Q : infseq T -> Prop) s, eventually Q s -> eventually (P \/_ Q) s.
Proof using.
Admitted.

Lemma eventually_or_tl_introl : forall (P Q : infseq T -> Prop) s, eventually P s -> eventually (P \/_ Q) s.
Proof using.
Admitted.

Lemma eventually_or_tl_or : forall (P Q : infseq T -> Prop) s, eventually (P \/_ Q) s -> eventually P s \/ eventually Q s.
Proof using.
Admitted.

Lemma until_Cons : forall (x: T) (s: infseq T) J P, until J P (Cons x s) -> P (Cons x s) \/ (J (Cons x s) /\ until J P s).
Proof using.
intros x s J P ul.
change (P (Cons x s) \/ (J (Cons x s) /\ until J P (tl (Cons x s)))).
Admitted.

Lemma until_eventually : forall (J P : infseq T -> Prop), forall s, until J P s -> eventually P s.
Proof using.
intros P J s unP.
induction unP.
-
apply E0; assumption.
-
Admitted.

Lemma release_Cons : forall (x: T) (s: infseq T) J P, release J P (Cons x s) -> P (Cons x s) /\ (J (Cons x s) \/ release J P s).
Proof using.
intros x s J P rl.
change (P (Cons x s) /\ (J (Cons x s) \/ release J P (tl (Cons x s)))).
Admitted.

Lemma inf_often_invar : forall (x: T) (s: infseq T) P, inf_often P (Cons x s) -> inf_often P s.
Proof using.
Admitted.

Lemma continuously_invar : forall (x: T) (s: infseq T) P, continuously P (Cons x s) -> continuously P s.
Proof using.
intros x s P cny.
apply eventually_Cons in cny.
case cny; trivial.
intro alP.
apply E0.
Admitted.

Lemma continuously_and_tl : forall (P Q : infseq T -> Prop) (s : infseq T), continuously P s -> continuously Q s -> continuously (P /\_ Q) s.
Proof using.
intros P Q s cnyP.
induction cnyP as [s alP|].
-
intro cnyQ.
induction cnyQ.
apply E0.
apply always_and_tl; trivial.
apply E_next.
apply IHcnyQ.
apply always_invar in alP; assumption.
-
intro cnyQ.
apply E_next.
apply IHcnyP.
Admitted.

Lemma now_monotonic : forall (P Q: T -> Prop), (forall x, P x -> Q x) -> forall s, now P s -> now Q s.
Proof using.
intros P Q PQ (x, s) nP; simpl.
apply PQ.
Admitted.

Lemma next_monotonic : forall (P Q: infseq T -> Prop), (forall s, P s -> Q s) -> forall s, next P s -> next Q s.
Proof using.
Admitted.

Lemma consecutive_monotonic : forall (P Q: T -> T -> Prop), (forall x y, P x y -> Q x y) -> forall s, consecutive P s -> consecutive Q s.
Proof using.
intros P Q PQ (x, (y, s)) nP; simpl.
apply PQ.
Admitted.

Lemma always_monotonic : forall (P Q: infseq T -> Prop), (forall s, P s -> Q s) -> forall s, always P s -> always Q s.
Proof using.
intros P Q PQ.
cofix cf.
intros(x, s) a.
generalize (always_Cons x s P a); simpl; intros (a1, a2).
constructor; simpl.
-
apply PQ.
assumption.
-
apply cf.
Admitted.

Lemma weak_until_monotonic : forall (P Q J K: infseq T -> Prop), (forall s, P s -> Q s) -> (forall s, J s -> K s) -> forall s, weak_until J P s -> weak_until K Q s.
Proof using.
intros P Q J K PQ JK.
cofix cf.
intros(x, s) un.
generalize (weak_until_Cons x s J P un); simpl.
intros [Pxs | (Jxs, uns)].
-
constructor 1; simpl; auto.
-
Admitted.

Lemma until_monotonic : forall (P Q J K: infseq T -> Prop), (forall s, P s -> Q s) -> (forall s, J s -> K s) -> forall s, until J P s -> until K Q s.
Proof using.
intros P Q J K PQ JK s unJP.
induction unJP.
-
apply U0, PQ; assumption.
-
apply U_next.
*
apply JK; assumption.
*
Admitted.

Lemma release_monotonic : forall (P Q J K: infseq T -> Prop), (forall s, P s -> Q s) -> (forall s, J s -> K s) -> forall s, release J P s -> release K Q s.
Proof using.
intros P Q J K PQ JK.
cofix cf.
intros [x s] rl.
generalize (release_Cons x s J P rl); simpl.
intros [Pxs rlCJP].
case rlCJP; intros rlJP.
-
apply R0.
*
apply PQ; assumption.
*
apply JK; assumption.
-
apply R_tl.
*
apply PQ; assumption.
*
simpl.
apply cf.
Admitted.

Lemma eventually_monotonic : forall (P Q J: infseq T -> Prop), (forall x s, J (Cons x s) -> J s) -> (forall s, J s -> P s -> Q s) -> forall s, J s -> eventually P s -> eventually Q s.
Proof using.
intros P Q J is_inv JPQ s Js ev.
apply (eventually_trans P Q J is_inv); try assumption.
intros; constructor 1.
Admitted.

Lemma eventually_monotonic_simple : forall (P Q: infseq T -> Prop), (forall s, P s -> Q s) -> forall s, eventually P s -> eventually Q s.
Proof using.
intros P Q PQ s.
Admitted.

Lemma inf_often_monotonic : forall (P Q : infseq T -> Prop), (forall s, P s -> Q s) -> forall s, inf_often P s -> inf_often Q s.
Proof using.
intros P Q impl.
apply always_monotonic.
apply eventually_monotonic_simple.
Admitted.

Lemma continuously_inf_often : forall (P : infseq T -> Prop) (s : infseq T), continuously P s -> inf_often P s.
Proof using.
intros P.
cofix c.
intros s cnyP.
induction cnyP.
-
apply always_inf_often.
assumption.
-
apply Always.
*
apply E_next.
destruct s as [s x'].
apply always_now in IHcnyP.
assumption.
*
apply IHcnyP.
