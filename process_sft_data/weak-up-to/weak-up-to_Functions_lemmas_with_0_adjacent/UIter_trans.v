Require Export Relations.
Set Implicit Arguments.
Section Global.
Section Def.
Variables X Y X' Y': Type.
Definition function2 := relation2 X Y -> relation2 X' Y'.
Definition function := relation2 X Y -> relation2 X Y.
Definition increasing (F: function) := forall R S, incl R S -> incl (F R) (F S).
Definition contains (F G: function2) := forall R, incl (F R) (G R).
Definition constant S: function2 := fun _ => S.
Definition identity: function := fun R => R.
Definition Union2 F G: function2 := fun R => union2 (F R) (G R).
Definition Union I H: function2 := fun R => union (fun i: I => H i R).
End Def.
Section Def'.
Variables X Y Z X' Y' Z' X'' Y'': Type.
Definition transparent (B: relation X) (F: function2 X Y X Y') := forall R, incl (F (comp (star B) R)) (comp (star B) (F R)).
Definition chaining_l (S: relation2 X Y): function2 Y Z X Z := comp S.
Definition chaining_r (S: relation2 Y Z): function2 X Y X Z := fun R => comp R S.
Definition Chain (F: function2 X Y X' Y') (G: function2 X Y Y' Z') := fun R => comp (F R) (G R).
Definition Comp (G: function2 X' Y' X'' Y'') (F: function2 X Y X' Y') := fun R => G (F R).
Variable F: function X Y.
Variable R: relation2 X Y.
Fixpoint Exp(n: nat): relation2 X Y := match n with | O => R | S n => F (Exp n) end.
Definition Iter := union Exp.
Fixpoint UExp(n: nat): relation2 X Y := match n with | O => R | S n => union2 (UExp n) (F (UExp n)) end.
Definition UIter := union UExp.
End Def'.
Section UIter.
Variables X Y: Type.
Variable F: function X Y.
Hypothesis HF: increasing F.
Hypothesis HF0: forall R, incl R (F R).
Hypothesis HF2: forall R, incl (F (F R)) (F R).
End UIter.
Section UIter'.
Variable X: Type.
Variable F: function X X.
Hypothesis HF: forall R, eeq (trans (F R)) (F (trans R)) .
Hypothesis HF': increasing F.
End UIter'.
End Global.
Hint Immediate UExp_incl.
Hint Immediate UIter_incl.

Lemma UIter_trans: forall R, eeq (trans (UIter F R)) (UIter F (trans R)).
intro R; split; intros x y H; destruct H as [ i H ]; exists i.
exact (proj1 (UExp_trans i R) _ _ H).
exact (proj2 (UExp_trans i R) _ _ H).
