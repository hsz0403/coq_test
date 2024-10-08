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

Theorem in_alphabet_incl : forall m1 m2 c, incl m1 m2 -> in_alphabet m2 c -> in_alphabet m1 c.
Proof using.
intros m1 m2 c H H0; red in |- *.
Admitted.

Theorem in_alphabet_nil : forall c, in_alphabet [] c.
Proof using.
Admitted.

Theorem in_alphabet_cons : forall (m : list A) c a ca, In (a, ca) c -> in_alphabet m c -> in_alphabet (a :: m) c.
Proof using.
intros m c a ca H H0; red in |- *; simpl in |- *.
intros a1 [H1| H1].
exists ca; rewrite <- H1; auto.
Admitted.

Theorem in_alphabet_inv : forall (c : code) (a : A) (l : list A), in_alphabet (a :: l) c -> in_alphabet l c.
Proof using.
intros c a l H; red in |- *.
Admitted.

Definition code_dec : forall (c : code) a, {(exists l : list bool, In (a, l) c)} + {(forall l : list bool, ~ In (a, l) c)}.
Proof.
intros c a; elim c; simpl in |- *; auto.
intros (a1, l1) l H; case (eqA_dec a1 a); intros H1.
left; exists l1; rewrite H1; auto.
case H.
intros e; left; case e; intros l2 H2; exists l2; auto.
intros n; right; intros l0; red in |- *; intros [H0| H0]; [ case H1 | case (n l0) ]; auto.
Admitted.

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
Admitted.

Theorem not_null_inv : forall (a : A * list bool) l, not_null (a :: l) -> not_null l.
Proof using.
intros a l H; red in |- *.
Admitted.

Theorem not_null_app : forall l1 l2 : list (A * list bool), not_null l1 -> not_null l2 -> not_null (l1 ++ l2).
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros (a2, l2); case l2; auto.
intros l H l0 H0 H1; case (H0 a2); simpl in |- *; auto.
intros b l l0 H l3 H0 H1; apply not_null_cons; auto.
red in |- *; intros H2; discriminate.
apply H; auto.
Admitted.

Theorem not_null_map : forall (l : list (A * list bool)) b, not_null (map (fun v => match v with | (a1, b1) => (a1, b :: b1) end) l).
Proof using.
intros l; elim l; simpl in |- *; auto.
intros b; red in |- *; intros a; red in |- *; intros H; inversion H.
intros (a1, l1) l0 H b; apply not_null_cons; auto.
Admitted.

Theorem is_prefix_refl : forall l, is_prefix l l.
Proof using.
Admitted.

Theorem unique_prefix_nil : unique_prefix [].
Proof using.
split; auto.
Admitted.

Theorem unique_prefix1 : forall (c : code) (a1 a2 : A) (lb1 lb2 : list bool), unique_prefix c -> In (a1, lb1) c -> In (a2, lb2) c -> is_prefix lb1 lb2 -> a1 = a2.
Proof using.
Admitted.

Theorem unique_prefix2 : forall c : code, unique_prefix c -> unique_key c.
Proof using.
Admitted.

Theorem unique_prefix_inv : forall (c : code) (a : A) (l : list bool), unique_prefix ((a, l) :: c) -> unique_prefix c.
Proof using.
intros c a l (H1, H2); split.
intros a1 a2 lb1 lb2 H H0 H3; apply (H1 a1 a2 lb1 lb2); simpl in |- *; auto.
Admitted.

Theorem unique_prefix_not_null : forall (c : code) (a b : A), a <> b -> in_alphabet (a :: b :: []) c -> unique_prefix c -> not_null c.
Proof using.
intros c a b H H0 H1.
unfold not_null in |- *; intros a1; red in |- *; intros Ha1.
case (H0 a); simpl in |- *; auto; intros l1 Hl1.
case (H0 b); simpl in |- *; auto; intros l2 Hl2.
case H; apply trans_equal with a1.
apply sym_equal; apply unique_prefix1 with (3 := Hl1) (2 := Ha1); auto.
Admitted.

Theorem unique_prefix_permutation : forall c1 c2 : code, permutation c1 c2 -> unique_prefix c1 -> unique_prefix c2.
Proof using.
intros c1 c2 H (H1, H2).
cut (permutation c2 c1); [ intros HP; split | apply permutation_sym; auto ].
intros a1 a2 lb1 lb2 H0 H3 H4.
apply (H1 a1 a2 lb1 lb2); auto.
apply permutation_in with (2 := H0); auto.
apply permutation_in with (2 := H3); auto.
Admitted.

Theorem find_code_correct1 : forall (c : code) (a : A) (b : bool) (l : list bool), find_code a c = b :: l -> In (a, b :: l) c.
Proof using.
intros c a b l; elim c; simpl in |- *; auto.
intros; discriminate.
intros a0; case a0.
intros a1; case (eqA_dec a a1); simpl in |- *; auto.
Admitted.

Theorem find_code_correct2 : forall (c : code) (a : A) (l : list bool), unique_key c -> In (a, l) c -> find_code a c = l.
Proof using.
intros c a l; generalize a l; elim c; clear a l c; simpl in |- *; auto.
intros a l H H0; case H0.
intros a; case a.
intros a0 l l0 H a1 l1 H0 H1; case (eqA_dec a1 a0).
intros H2; case H1; intros H3.
injection H3; auto.
apply unique_key_in_inv with (l := (a0, l) :: l0) (a := a0); simpl in |- *; auto.
rewrite <- H2; auto.
intros H2; case H1; auto.
intros H3; case H2; injection H3; auto.
intros; apply H; auto.
Admitted.

Theorem not_in_find_code : forall a l, (forall p, ~ In (a, p) l) -> find_code a l = [].
Proof using.
intros a l; elim l; simpl in |- *; auto.
intros (a1, l1) l0 H H0.
case (eqA_dec a a1); auto.
intros H1; case (H0 l1); rewrite H1; auto.
Admitted.

Theorem find_code_app : forall a l1 l2, not_null l1 -> find_code a (l1 ++ l2) = match find_code a l1 with | [] => find_code a l2 | b1 :: l3 => b1 :: l3 end.
Proof using.
intros a l1; generalize a; elim l1; simpl in |- *; auto; clear a l1.
intros (a1, l1) l H a l2 H1; case (eqA_dec a a1); auto.
generalize H1; case l1; auto.
intros H0; case (H0 a1); simpl in |- *; auto.
cut (not_null l); simpl in |- *; auto.
Admitted.

Theorem find_code_permutation : forall (a : A) (c1 c2 : code), permutation c1 c2 -> unique_prefix c1 -> find_code a c1 = find_code a c2.
Proof using.
intros a c1 c2 H; elim H; simpl in |- *; auto.
intros a0; case a0.
intros a1; case (eqA_dec a a1); auto.
intros n l L1 L2 H0 H1 H2; apply H1.
apply unique_prefix_inv with (1 := H2).
intros a0; case a0.
intros a1 l1.
case (eqA_dec a a1).
intros Ha1 b; case b; auto.
intros a2 l2 L HL; case (eqA_dec a a2); auto.
intros e.
case unique_key_in with (1 := unique_prefix2 _ HL) (b2 := l2); auto.
rewrite <- Ha1; rewrite e; simpl in |- *; auto.
intros Ha1 b; case b; auto.
intros L1 L2 L3 H0 H1 H2 H3 H4; apply trans_equal with (find_code a L2); auto.
apply H3.
Admitted.

Theorem in_find_map : forall p a l b, In (a, l) p -> find_code a (map (fun v : A * list bool => match v with | (a1, b1) => (a1, b :: b1) end) p) = b :: find_code a p.
Proof using.
intros p; elim p; simpl in |- *; auto.
intros a l b H; case H.
intros (a1, l1) l H a0 l0 b [H0| H0]; auto.
case (eqA_dec a0 a1); auto.
intros HH; case HH; injection H0; auto.
case (eqA_dec a0 a1); auto.
Admitted.

Theorem not_in_find_map : forall p a b, (forall l, ~ In (a, l) p) -> find_code a (map (fun v : A * list bool => match v with | (a1, b1) => (a1, b :: b1) end) p) = [].
Proof using.
intros p; elim p; simpl in |- *; auto.
intros (a1, l1) l H a0 b H0; case (eqA_dec a0 a1); auto.
intros e; case (H0 l1); rewrite e; auto.
intros n; apply (H a0 b); auto.
Admitted.

Theorem find_val_correct1 : forall (c : code) (a : A) (l : list bool), find_val l c = Some a -> In (a, l) c.
Proof using.
intros c a l; elim c; simpl in |- *; auto.
intros; discriminate.
intros a0; case a0.
intros a1 l0 l1; case (list_eq_dec Bool.bool_dec l l0); auto.
intros e H H0; injection H0.
Admitted.

Theorem find_val_correct2 : forall (c : code) (a : A) (l : list bool), unique_prefix c -> In (a, l) c -> find_val l c = Some a.
Proof using.
intros c a l; generalize a l; elim c; clear a l c; simpl in |- *; auto.
intros a l H H0; case H0.
intros a; case a.
intros a0 l l0 H a1 l1 H0 H1; case (list_eq_dec Bool.bool_dec l1 l).
intros H2; apply f_equal with (f := Some (A:=A)).
case H1; intros H3.
injection H3; auto.
apply unique_prefix1 with (1 := H0) (lb1 := l) (lb2 := l1); simpl in |- *; auto.
rewrite H2; auto.
intros H2; case H1; auto.
intros H3; case H2; injection H3; auto.
intros; apply H; auto.
Admitted.

Theorem not_null_find_val : forall c : code, not_null c -> find_val [] c = None.
Proof using.
intros c; elim c; simpl; auto.
intros a; case a.
intros a1 l; case (list_eq_dec Bool.bool_dec [] l); auto.
intros e l0 H H0; case (H0 a1); rewrite e; simpl in |- *; auto.
intros n l0 H H0; apply H.
unfold not_null in |- *; intros a2; red in |- *; intros H1.
Admitted.

Theorem encode_app : forall l1 l2 c, encode c (l1 ++ l2) = encode c l1 ++ encode c l2.
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros a l H l2 c; rewrite H; auto.
Admitted.

Theorem not_null_cons : forall a b (l : list (A * list bool)), b <> [] -> not_null l -> not_null ((a, b) :: l).
Proof using.
intros a b l H H0; red in |- *.
intros a1; simpl in |- *; red in |- *; intros [H1| H1]; auto.
case H; injection H1; auto.
case (H0 a1); simpl in |- *; auto.
