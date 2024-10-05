Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma and_not : forall (A B : Prop), dec A -> dec B -> {A /\ ~ B } + {~ A \/ B}.
Proof.
unfold dec in |- *.
intros.
tauto.
