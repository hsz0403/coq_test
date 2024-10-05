Inductive Z : Set := | OZ : Z | pos : nat -> Z | neg : nat -> Z.
Definition IZ := pos 0.
Definition is_posn (x z : Z) := match x, z with | pos n, pos m => n = m :>nat | _, _ => False end.
Definition posOZ (n : nat) := match n return Z with | O => (* O *) OZ (* S n' *) | S n' => pos n' end.
Definition negOZ (n : nat) := match n return Z with | O => (* O *) OZ (* S n' *) | S n' => neg n' end.
Definition absZ (x : Z) := match x return Z with | OZ => (* OZ *) OZ (* pos n *) | pos n => pos n (* neg n *) | neg n => pos n end.
Definition sgnZ (x : Z) := match x return Z with | OZ => (* OZ *) OZ (* pos n *) | pos n => pos 0 (* neg n *) | neg n => neg 0 end.

Lemma eq_OZ_dec : forall x : Z, {x = OZ} + {x <> OZ}.
intros; elim x.
left; reflexivity.
intros; right; discriminate.
Admitted.

Lemma tech_pos_not_posZ : forall n m : nat, n <> m -> pos n <> pos m.
unfold not in |- *; intros.
cut (is_posn (pos n) (pos m)).
simpl in |- *; exact H.
rewrite H0; simpl in |- *; reflexivity.
