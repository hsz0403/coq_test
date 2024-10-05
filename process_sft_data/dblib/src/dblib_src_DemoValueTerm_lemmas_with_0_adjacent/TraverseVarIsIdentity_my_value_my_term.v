Set Implicit Arguments.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.
Inductive my_term := | MyTValue: my_value -> my_term | MyTApp: my_term -> my_term -> my_term with my_value := | MyVVar: nat -> my_value | MyVAbs: my_term -> my_value.
Instance Var_my_value : Var my_value := { var := MyVVar }.
Fixpoint traverse_my_term (f : nat -> nat -> my_value) l t := match t with | MyTValue v => MyTValue (traverse_my_value f l v) | MyTApp t1 t2 => MyTApp (traverse_my_term f l t1) (traverse_my_term f l t2) end with traverse_my_value f l v := match v with | MyVVar x => f l x | MyVAbs t => MyVAbs (traverse_my_term f (1 + l) t) end.
Instance Traverse_my_value_my_value : Traverse my_value my_value := { traverse := traverse_my_value }.
Instance Traverse_my_value_my_term : Traverse my_value my_term := { traverse := traverse_my_term }.
Instance TraverseVarInjective_my_value_my_value : @TraverseVarInjective my_value _ my_value _.
Proof.
constructor.
apply traverse_my_value_injective.
Instance TraverseVarInjective_my_value_my_term : @TraverseVarInjective my_value _ my_term _.
Proof.
constructor.
apply traverse_my_term_injective.
Instance TraverseFunctorial_my_value_my_value : @TraverseFunctorial my_value _ my_value _.
Proof.
constructor.
apply traverse_functorial_value_value.
Instance TraverseFunctorial_my_term_my_term : @TraverseFunctorial my_value _ my_term _.
Proof.
constructor.
apply traverse_functorial_value_term.
Instance TraverseIdentifiesVar_my_value : TraverseIdentifiesVar.
Proof.
constructor.
prove_traverse_identifies_var.
Instance TraverseRelative_my_value_my_value : @TraverseRelative my_value my_value _.
Proof.
constructor.
apply traverse_relative_my_value_my_value.
Instance TraverseRelative_my_value_my_term : @TraverseRelative my_value my_term _.
Proof.
constructor.
apply traverse_relative_my_value_my_term.
Instance TraverseVarIsIdentity_my_value_my_value : @TraverseVarIsIdentity my_value _ my_value _.
Proof.
constructor.
apply traverse_my_value_var_is_identity.
Instance TraverseVarIsIdentity_my_value_my_term : @TraverseVarIsIdentity my_value _ my_term _.
Proof.
constructor.
apply traverse_my_term_var_is_identity.

Instance TraverseVarIsIdentity_my_value_my_term : @TraverseVarIsIdentity my_value _ my_term _.
Proof.
constructor.
apply traverse_my_term_var_is_identity.
