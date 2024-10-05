Set Implicit Arguments.
Hint Extern 4 => exact _ : core.
Ltac inv H := inversion H; subst; clear H.
Definition dec (X: Prop) : Type := {X} + {~ X}.
Coercion dec2bool P (d: dec P) := if d then true else false.
Definition is_true (b : bool) := b = true.
Existing Class dec.
Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.
Hint Extern 4 => (* Improves type class inference *) match goal with | [ |- dec ((fun _ => _) _) ] => cbn end : typeclass_instances.
Tactic Notation "decide" constr(p) := destruct (Dec p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := destruct (Dec p) as i.
Tactic Notation "decide" "_" := destruct (Dec _).
Hint Extern 4 => match goal with [ H : dec2bool (Dec ?P) = true |- _ ] => apply Dec_true in H | [ H : dec2bool (Dec ?P) = true |- _ ] => apply Dec_false in H end : core.
Fact dec_transfer P Q : P <-> Q -> dec P -> dec Q.
Proof.
unfold dec.
tauto.
Instance True_dec : dec True.
Proof.
unfold dec; tauto.
Instance False_dec : dec False.
Proof.
unfold dec; tauto.
Instance impl_dec (X Y : Prop) : dec X -> dec Y -> dec (X -> Y).
Proof.
unfold dec; tauto.
Instance and_dec (X Y : Prop) : dec X -> dec Y -> dec (X /\ Y).
Proof.
unfold dec; tauto.
Instance or_dec (X Y : Prop) : dec X -> dec Y -> dec (X \/ Y).
Proof.
unfold dec; tauto.
Instance not_dec (X : Prop) : dec X -> dec (~ X).
Proof.
unfold not.
auto.
Instance iff_dec (X Y : Prop) : dec X -> dec Y -> dec (X <-> Y).
Proof.
unfold iff.
auto.
Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).
Structure eqType := EqType { eqType_X :> Type; eqType_dec : eq_dec eqType_X }.
Arguments EqType X {_} : rename.
Canonical Structure eqType_CS X (A: eq_dec X) := EqType X.
Existing Instance eqType_dec.
Instance unit_eq_dec : eq_dec unit.
Proof.
unfold dec.
decide equality.
Instance bool_eq_dec : eq_dec bool.
Proof.
unfold dec.
decide equality.
Defined.
Instance nat_eq_dec : eq_dec nat.
Proof.
unfold dec.
decide equality.
Defined.
Instance prod_eq_dec X Y : eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
unfold dec.
decide equality.
Defined.
Instance list_eq_dec X : eq_dec X -> eq_dec (list X).
Proof.
unfold dec.
decide equality.
Defined.
Instance sum_eq_dec X Y : eq_dec X -> eq_dec Y -> eq_dec (X + Y).
Proof.
unfold dec.
decide equality.
Defined.
Instance option_eq_dec X : eq_dec X -> eq_dec (option X).
Proof.
unfold dec.
decide equality.
Defined.
Instance Empty_set_eq_dec: eq_dec Empty_set.
Proof.
unfold dec.
decide equality.
Instance True_eq_dec: eq_dec True.
Proof.
intros x y.
destruct x,y.
now left.
Instance False_eq_dec: eq_dec False.
Proof.
intros [].

Lemma Dec_true P {H : dec P} : dec2bool (Dec P) = true -> P.
Proof.
decide P; cbv in *; firstorder.
Admitted.

Lemma Dec_false P {H : dec P} : dec2bool (Dec P) = false -> ~P.
Proof.
decide P; cbv in *; firstorder.
Admitted.

Lemma dec_DN X : dec X -> ~~ X -> X.
Proof.
Admitted.

Lemma dec_DM_and X Y : dec X -> dec Y -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof.
Admitted.

Lemma dec_DM_impl X Y : dec X -> dec Y -> ~ (X -> Y) -> X /\ ~ Y.
Proof.
Admitted.

Fact dec_transfer P Q : P <-> Q -> dec P -> dec Q.
Proof.
unfold dec.
Admitted.

Instance True_dec : dec True.
Proof.
Admitted.

Instance False_dec : dec False.
Proof.
Admitted.

Instance impl_dec (X Y : Prop) : dec X -> dec Y -> dec (X -> Y).
Proof.
Admitted.

Instance and_dec (X Y : Prop) : dec X -> dec Y -> dec (X /\ Y).
Proof.
Admitted.

Instance or_dec (X Y : Prop) : dec X -> dec Y -> dec (X \/ Y).
Proof.
Admitted.

Instance not_dec (X : Prop) : dec X -> dec (~ X).
Proof.
unfold not.
Admitted.

Instance iff_dec (X Y : Prop) : dec X -> dec Y -> dec (X <-> Y).
Proof.
unfold iff.
Admitted.

Instance unit_eq_dec : eq_dec unit.
Proof.
unfold dec.
Admitted.

Instance bool_eq_dec : eq_dec bool.
Proof.
unfold dec.
Admitted.

Instance nat_eq_dec : eq_dec nat.
Proof.
unfold dec.
Admitted.

Instance prod_eq_dec X Y : eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
unfold dec.
Admitted.

Instance list_eq_dec X : eq_dec X -> eq_dec (list X).
Proof.
unfold dec.
Admitted.

Instance sum_eq_dec X Y : eq_dec X -> eq_dec Y -> eq_dec (X + Y).
Proof.
unfold dec.
Admitted.

Instance option_eq_dec X : eq_dec X -> eq_dec (option X).
Proof.
unfold dec.
Admitted.

Instance True_eq_dec: eq_dec True.
Proof.
intros x y.
destruct x,y.
Admitted.

Instance False_eq_dec: eq_dec False.
Proof.
Admitted.

Instance Empty_set_eq_dec: eq_dec Empty_set.
Proof.
unfold dec.
decide equality.
