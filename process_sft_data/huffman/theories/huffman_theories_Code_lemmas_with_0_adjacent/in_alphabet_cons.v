Require Bool.Bool.
From Huffman Require Export AuxLib.
From Huffman Require Export Permutation.
From Huffman Require Export UniqueKey.
From Huffman Require Export Frequency.
Section Code.
Variable A : Type.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Definition code := list (A * list bool).
Definition in_alphabet (m : list A) (c : code) := forall a : A, In a m -> exists l : list bool, In (a, l) c.
Hint Resolve in_alphabet_nil : core.
Hint Resolve in_alphabet_cons : core.
Definition code_dec : forall (c : code) a, {(exists l : list bool, In (a, l) c)} + {(forall l : list bool, ~ In (a, l) c)}.
Proof.
intros c a; elim c; simpl in |- *; auto.
intros (a1, l1) l H; case (eqA_dec a1 a); intros H1.
left; exists l1; rewrite H1; auto.
case H.
intros e; left; case e; intros l2 H2; exists l2; auto.
intros n; right; intros l0; red in |- *; intros [H0| H0]; [ case H1 | case (n l0) ]; auto.
injection H0; auto.
Defined.
Definition in_alphabet_dec : forall m c, {in_alphabet m c} + {~ in_alphabet m c}.
Proof.
intros m; elim m; simpl in |- *; auto.
intros a l H c; case (H c); intros H1.
case (code_dec c a); intros H2.
left; red in |- *; simpl in |- *.
intros a1 [H3| H3]; [ case H2; intros l1 Hl1; exists l1; rewrite <- H3 | idtac ]; auto.
right; red in |- *; intros H3; case (H3 a); simpl in |- *; auto.
right; contradict H1; auto; red in |- *.
intros a0 H0; case (H1 a0); simpl in |- *; auto.
intros x H2; exists x; auto.
Defined.
Definition not_null (c : code) := forall a : A, ~ In (a, []) c.
Hint Resolve not_null_cons : core.
Hint Resolve not_null_app : core.
Hint Resolve not_null_map : core.
Inductive is_prefix : list bool -> list bool -> Prop := | prefixNull : forall l, is_prefix [] l | prefixCons : forall (b : bool) l1 l2, is_prefix l1 l2 -> is_prefix (b :: l1) (b :: l2).
Hint Constructors is_prefix : core.
Hint Resolve is_prefix_refl : core.
Definition unique_prefix (l : code) := (forall (a1 a2 : A) (lb1 lb2 : list bool), In (a1, lb1) l -> In (a2, lb2) l -> is_prefix lb1 lb2 -> a1 = a2) /\ unique_key l.
Hint Resolve unique_prefix_nil : core.
Fixpoint find_code (a : A) (l : code) {struct l} : list bool := match l with | [] => [] | (b, c) :: l1 => match eqA_dec a b with | left _ => c | right _ => find_code a l1 end end.
Fixpoint find_val (a : list bool) (l : code) {struct l} : option A := match l with | [] => None | (b, c) :: l1 => match list_eq_dec Bool.bool_dec a c with | left _ => Some b | right _ => find_val a l1 end end.
Opaque list_eq_dec.
Fixpoint encode (c : code) (m : list A) {struct m} : list bool := match m with | [] => [] | a :: b => find_code a c ++ encode c b end.
Fixpoint decode_aux (c : code) (head m : list bool) {struct m} : list A := match m with | [] => match find_val head c with | Some a => a :: [] | None => [] end | a :: m1 => match find_val head c with | Some a1 => a1 :: decode_aux c (a :: []) m1 | None => decode_aux c (head ++ a :: []) m1 end end.
Definition decode (c : list (A * list bool)) (m : list bool) := decode_aux c [] m.
End Code.
Arguments encode [A].
Arguments decode [A].
Arguments find_code [A].
Arguments find_val [A].
Arguments in_alphabet [A].
Arguments unique_prefix [A].
Arguments not_null [A].
Hint Constructors is_prefix : core.
Hint Resolve is_prefix_refl : core.
Hint Resolve not_null_map : core.
Hint Resolve unique_prefix_nil : core.
Hint Resolve in_alphabet_nil in_alphabet_cons : core.
Hint Resolve not_null_app : core.

Theorem in_alphabet_cons : forall (m : list A) c a ca, In (a, ca) c -> in_alphabet m c -> in_alphabet (a :: m) c.
Proof using.
intros m c a ca H H0; red in |- *; simpl in |- *.
intros a1 [H1| H1].
exists ca; rewrite <- H1; auto.
case (H0 a1); auto.
