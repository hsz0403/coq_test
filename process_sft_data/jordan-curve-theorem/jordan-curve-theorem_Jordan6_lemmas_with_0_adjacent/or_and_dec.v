Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma or_and_dec : forall (A B C D:Prop), dec A -> dec B -> dec C -> dec D -> {A /\ B \/ C /\ D} + {~A /\ ~C \/ ~B /\ ~C \/ ~A /\ ~D \/ ~B /\ ~D}.
Proof.
unfold dec in |- *.
intros.
tauto.
