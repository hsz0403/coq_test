From Undecidability.TM Require Export Util.Prelim Util.TM_facts Code.Code.
From Undecidability.TM Require Export Lifting.Lifting.
From Undecidability.TM Require Export Combinators.Combinators.
Section isVoid.
Definition isVoid (sig : Type) (t : tape sig) := exists x rs, t = midtape rs x nil.
Definition isVoid_size (sig : Type) (t : tape sig) (s : nat) := exists x rs, t = midtape rs x nil /\ |rs| <= s.
End isVoid.
Ltac isVoid_mono := once lazymatch goal with | [ H : isVoid_size ?t ?s1 |- isVoid_size ?t ?s2 ] => apply isVoid_size_monotone with (1 := H); eauto; simpl_comp; try lia | [ H : isVoid_size ?t ?s1 |- isVoid ?t ] => apply isVoid_size_isVoid with (1 := H) | [ H : isVoid ?t |- isVoid_size ?t ?s2 ] => eapply isVoid_size_monotone; [ apply (isVoid_isVoid_size H) | eauto; simpl_comp; try lia ] | [ H : isVoid ?t |- isVoid ?t ] => apply H end.
Hint Extern 10 => isVoid_mono : core.
Inductive boundary : Type := | START : boundary | STOP : boundary | UNKNOWN : boundary.
Instance boundary_eq : eq_dec boundary.
Proof.
unfold dec.
decide equality.
Defined.
Instance boundary_fin : finTypeC (EqType boundary).
Proof.
split with (enum := [START; STOP; UNKNOWN]).
cbn.
intros []; cbn; reflexivity.
Defined.
Section Fix_Sig.
Variable (sig : Type).
Notation "sig '^+'" := ((boundary + sig) % type) (at level 0) : type_scope.
Section Tape_Contains.
Variable (sigX : Type) (X : Type) (cX : codable sigX X) (I : Retract sigX sig).
Definition tape_contains (t: tape sig^+) (x : X) := exists r1, t = midtape r1 (inl START) (map inr (Encode_map _ _ x) ++ [inl STOP]).
Definition tape_contains_size (t: tape sig^+) (x : X) (s : nat) := exists r1, t = midtape r1 (inl START) (map inr (Encode_map _ _ x) ++ [inl STOP]) /\ length r1 <= s.
Definition tape_contains_rev (t: tape sig^+) (x : X) := exists r1, t = midtape (map inr (rev (Encode_map _ _ x)) ++ inl START :: r1) (inl STOP) nil.
Definition tape_contains_rev_size (t: tape sig^+) (x : X) (s : nat) := exists r1, t = midtape (map inr (rev (Encode_map _ _ x)) ++ inl START :: r1) (inl STOP) nil /\ length r1 <= s.
End Tape_Contains.
Arguments tape_contains {sigX X cX} (I t x) : simpl never.
Arguments tape_contains_rev {sigX X cX} (I t x) : simpl never.
Arguments tape_contains_size {sigX X cX} (I t x s) : simpl never.
Arguments tape_contains_rev_size {sigX X cX} (I t x s) : simpl never.
Notation "t ≃( I ) x" := (tape_contains I t x) (at level 70, no associativity).
Notation "t ≃ x" := (t ≃(_) x) (at level 70, no associativity, only parsing).
Notation "t ≃( I ';' s ) x" := (tape_contains_size I t x s) (at level 70, no associativity).
Notation "t ≃( ';' s ) x" := (t ≃(_;s) x) (at level 70, only parsing).
Notation "t ≂( I ) x" := (tape_contains_rev I t x) (at level 70, no associativity).
Notation "t ≂ x" := (t ≃(_) x) (at level 70, no associativity, only parsing).
Notation "t ≂( I ';' s ) x" := (tape_contains_rev_size I t x s) (at level 70, no associativity).
Notation "t ≃( ';' s ) x" := (t ≃(_;s) x) (at level 70, no associativity, only parsing).
Section Encodes_Ext.
Variable (X Y sigX sigY : Type) (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig).
Implicit Type x : X.
Implicit Type y : Y.
End Encodes_Ext.
Section InitTape.
Variable (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig).
Definition initValue (x : X) := midtape nil (inl START) (map inr (Encode_map _ I x) ++ [inl STOP]).
Definition initRight : tape sig^+ := midtape nil (inl STOP) nil.
End InitTape.
End Fix_Sig.
Arguments tape_contains {sig sigX X cX} (I t x) : simpl never.
Arguments tape_contains_rev {sig sigX X cX} (I t x) : simpl never.
Arguments tape_contains_size {sig sigX X cX} (I t x s) : simpl never.
Arguments tape_contains_rev_size {sig sigX X cX} (I t x s) : simpl never.
Notation "t ≃( cX ) x" := (tape_contains cX t x) (at level 70, no associativity, format "t ≃( cX ) x").
Notation "t ≃ x" := (t ≃(_) x) (at level 70, no associativity, only parsing).
Notation "t ≃( cX ';' s ) x" := (tape_contains_size cX t x s) (at level 70, no associativity, format "t ≃( cX ';' s ) x").
Notation "t ≃( ';' s ) x" := (t ≃(_;s) x) (at level 70, only parsing).
Notation "t ≂( cX ) x" := (tape_contains_rev cX t x) (at level 70, no associativity, format "t ≂( cX ) x").
Notation "t ≂ x" := (t ≂(_) x) (at level 70, no associativity, only parsing).
Notation "t ≂( cX ';' s ) x" := (tape_contains_rev_size cX t x s) (at level 70, no associativity, format "t ≂( cX ';' s ) x").
Notation "t ≂( ';' s ) x" := (t ≂(_;s) x) (at level 70, no associativity, only parsing).
Ltac contains_solve_le := try now (cbn; solve [lia]).
Local Ltac eUnify I1 I2 := ((is_evar I1 || is_evar I2);unify I1 I2).
Ltac contains_ext := once lazymatch goal with | [H : ?t ≃(?I1;?s1) ?x |- ?t ≃(?I2;?s2) ?y] => apply tape_contains_size_ext with (1 := H); try eUnify I1 I2;simpl_comp; try reflexivity; try contains_solve_le | [H : ?t ≃(_;?s1) ?x |- ?t ≃(_) ?y] => eapply tape_contains_size_contains; contains_ext | [H : ?t ≃(_) ?x |- ?t ≃(_;?s2) ?y] => eapply tape_contains_contains_size; contains_ext | [H : ?t ≃(?I1) ?x |- ?t ≃(?I2) ?y] => apply tape_contains_ext with (1 := H); try eUnify I1 I2; simpl_comp; try reflexivity (* [≂] is only used "internally"! *) | [H : ?t ≂(_;?s1) ?x |- ?t ≂(_;?s2) ?y] => apply tape_contains_rev_size_ext with (1 := H); simpl_comp; try reflexivity; contains_solve_le | [H : ?t ≂(_;?s1) ?x |- ?t ≂(_) ?y] => eapply tape_contains_rev_size_contains; contains_ext | [H : ?t ≂(_) ?x |- ?t ≂(_;?s2) ?y] => eapply tape_contains_rev_contains_rev_size; contains_ext | [H : ?t ≂(_) ?x |- ?t ≂(_) ?y] => apply tape_contains_rev_ext with (1 := H); simpl_comp; try reflexivity end.
Hint Extern 10 => contains_ext : core.
Notation "sig '^+'" := (FinType (EqType (boundary + sig) % type)) (at level 0) : type_scope.
Definition compSizeFun (n : nat) (f1 f2 : Vector.t (nat -> nat) n) : Vector.t (nat -> nat) n := tabulate (fun i => f1[@i] >> f2[@i]).
Notation "f >>> g" := (compSizeFun f g) (at level 40).
Notation "s '@>' i" := (s[@i]) (at level 10, only parsing).
Definition injectSizeFun {m n : nat} (f : Vector.t (nat->nat) m) (I : Vector.t (Fin.t n) m) : Vector.t (nat->nat) n := LiftTapes.fill I (Vector.const id _) f.
Notation "f '@>>' I" := (injectSizeFun f I) (at level 41).

Lemma initValue_contains_size (x : X) : initValue x ≃(;0) x.
Proof.
unfold initValue.
repeat econstructor.
