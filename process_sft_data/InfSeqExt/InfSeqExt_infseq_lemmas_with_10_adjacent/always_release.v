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

Lemma always_now' : forall (P : infseq T -> Prop) ex, always P ex -> P ex.
Proof using.
destruct ex.
Admitted.

Lemma always_invar : forall (x: T) (s: infseq T) P, always P (Cons x s) -> always P s.
Proof using.
intros x s P al.
Admitted.

Lemma always_tl : forall (s: infseq T) P, always P s -> always P (tl s).
Proof using.
intros (x, s).
simpl.
Admitted.

Lemma always_not_false : forall s : infseq T, always (~_ False_tl) s.
Proof using.
cofix c.
intros [x s].
apply Always.
-
unfold not_tl, False_tl; auto.
-
Admitted.

Lemma always_true : forall s : infseq T, always True_tl s.
Proof using.
cofix c.
intros [x s].
apply Always.
-
unfold True_tl; trivial.
-
Admitted.

Lemma always_and_tl : forall (P Q : infseq T -> Prop), forall s, always P s -> always Q s -> always (P /\_ Q) s.
Proof using.
intros P Q.
cofix c.
intros s alP alQ.
destruct alP.
destruct alQ.
apply Always.
-
split; assumption.
-
Admitted.

Lemma always_always : forall (P : infseq T -> Prop) s, always P s -> always (always P) s.
Proof using.
intro P.
cofix c.
constructor.
-
auto.
-
do 2 destruct s.
Admitted.

Lemma always_always1 : forall P (s: infseq T), always (now P) s -> always1 P s.
Proof using.
intros P.
cofix alwn.
intros s a; case a; clear a s.
intros (x, s); simpl.
constructor.
-
assumption.
-
Admitted.

Lemma always1_always : forall P (s: infseq T), always1 P s -> always (now P) s.
Proof using.
intros P.
cofix alwn.
destruct 1.
constructor; simpl.
-
assumption.
-
Admitted.

Lemma always_weak_until : forall (J P : infseq T -> Prop) (s : infseq T), always J s -> weak_until J P s.
Proof using.
intros J P.
cofix c.
intros [x s] alJ.
apply W_tl.
-
apply always_now in alJ.
assumption.
-
apply c.
apply always_invar in alJ.
Admitted.

Lemma always_inf_often : forall (P: infseq T -> Prop) (s : infseq T), always P s -> inf_often P s.
Proof using.
intros P.
cofix f.
intros s a.
destruct a.
constructor.
-
constructor 1.
assumption.
-
apply f.
Admitted.

Lemma always_continuously : forall (P: infseq T -> Prop) (s : infseq T), always P s -> continuously P s.
Proof using.
intros P s alP.
apply E0.
Admitted.

Lemma weak_until_Cons : forall (x: T) (s: infseq T) J P, weak_until J P (Cons x s) -> P (Cons x s) \/ (J (Cons x s) /\ weak_until J P s).
Proof using.
intros x s J P un.
change (P (Cons x s) \/ (J (Cons x s) /\ weak_until J P (tl (Cons x s)))).
Admitted.

Lemma weak_until_always : forall (J J' P : infseq T -> Prop) s, weak_until J P s -> always J' s -> weak_until (J' /\_ J) P s.
Proof using.
cofix cf.
intros J J' P s Hweak Halways.
destruct s.
inversion Hweak.
-
now eauto using W0.
-
inversion Halways.
eapply W_tl.
+
now unfold and_tl.
+
simpl.
Admitted.

Lemma until_weak_until : forall (J P : infseq T -> Prop) (s : infseq T), until J P s -> weak_until J P s.
Proof using.
intros J P s un.
induction un.
-
apply W0.
assumption.
-
Admitted.

Lemma eventually_Cons : forall (x: T) (s: infseq T) P, eventually P (Cons x s) -> P (Cons x s) \/ eventually P s.
Proof using.
intros x s P al.
change (P (Cons x s) \/ eventually P (tl (Cons x s))).
Admitted.

Lemma eventually_trans : forall (P Q inv: infseq T -> Prop), (forall x s, inv (Cons x s) -> inv s) -> (forall s, inv s -> P s -> eventually Q s) -> forall s, inv s -> eventually P s -> eventually Q s.
Proof using.
intros P Q inv is_inv PeQ s invs ev.
induction ev as [s Ps | x s ev IHev].
-
apply PeQ; assumption.
-
constructor 2.
apply IHev.
Admitted.

Lemma not_eventually : forall (P : infseq T -> Prop), forall x s, ~ eventually P (Cons x s) -> ~ eventually P s.
Proof using.
intros P x s evCP evP.
contradict evCP.
apply E_next.
Admitted.

Lemma eventually_next : forall (s: infseq T) P, eventually (next P) s -> eventually P s.
Proof using.
intros e P ev.
induction ev as [(x, s) Ps | x s ev induc_hyp].
-
constructor 2; constructor 1; exact Ps.
-
constructor 2.
Admitted.

Lemma eventually_always_cumul : forall (s: infseq T) P Q, eventually P s -> always Q s -> eventually (P /\_ always Q) s.
Proof using.
induction 1 as [s Ps | x s evPs induc_hyp]; intro al.
-
constructor 1.
split; assumption.
-
constructor 2.
apply induc_hyp.
Admitted.

Lemma always_release : forall (J P : infseq T -> Prop) (s : infseq T), always P s -> release J P s.
Proof using.
intros J P.
cofix c.
intros [x s] al.
apply R_tl.
-
apply always_now in al.
assumption.
-
simpl.
apply c.
apply always_invar in al.
assumption.
