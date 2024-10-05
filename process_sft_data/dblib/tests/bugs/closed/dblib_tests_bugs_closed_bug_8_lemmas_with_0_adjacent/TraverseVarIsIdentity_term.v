From Dblib Require Import DeBruijn DblibTactics.
Module named_traverse.
Inductive term : Set := | TAbs : term -> term | TApp : term -> term -> term | TVar : nat -> term.
Instance Var_term : Var term := {var := TVar}.
Fixpoint traverse_term (f : nat -> nat -> term) (l : nat) (e : term) : term := match e with | TAbs e => TAbs (traverse_term f (1 + l) e) | TApp e1 e2 => TApp (traverse_term f l e1) (traverse_term f l e2) | TVar x => f l x end.
Instance Traverse_term : Traverse term term := {traverse := traverse_term}.
Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
constructor.
prove_traverse_var_injective.
Instance TraverseRelative_term : @TraverseRelative term term _.
constructor.
prove_traverse_relative.
Instance TraverseIdentifiesVar_term : @TraverseIdentifiesVar term _ _.
constructor.
prove_traverse_identifies_var.
Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
constructor.
prove_traverse_var_is_identity.
End named_traverse.
Module anonymous_traverse.
Inductive term : Set := | TAbs : term -> term | TApp : term -> term -> term | TVar : nat -> term.
Instance Var_term : Var term := {var := TVar}.
Instance Traverse_term : Traverse term term := {traverse := fix traverse_term (f : nat -> nat -> term) (l : nat) (e : term) : term := match e with | TAbs e => TAbs (traverse_term f (1 + l) e) | TApp e1 e2 => TApp (traverse_term f l e1) (traverse_term f l e2) | TVar x => f l x end }.
Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
constructor.
prove_traverse_var_injective.
Instance Traverse_term_functorial : @TraverseFunctorial term _ term _.
constructor.
prove_traverse_functorial.
Instance TraverseRelative_term : @TraverseRelative term term _.
constructor.
prove_traverse_relative.
Instance TraverseIdentifiesVar_term : @TraverseIdentifiesVar term _ _.
constructor.
prove_traverse_identifies_var.
Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
constructor.
prove_traverse_var_is_identity.
End anonymous_traverse.

Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
constructor.
prove_traverse_var_is_identity.
