Require Import ZArith.
Definition var := nat.
Inductive expr: Type := | impp : expr -> expr -> expr | varp : var -> expr.
Declare Scope syntax.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
Local Open Scope syntax.
Inductive provable: expr -> Prop := | modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y | axiom1: forall x y, provable (x --> (y --> x)) | axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z)).
Module NaiveLang.
Definition expr := expr.
Definition impp := impp.
Definition provable := provable.
End NaiveLang.