Require Import LogicalRelations.
Require Import Coq.Lists.List.
Require Import OptionRel.
Local Open Scope rel_scope.
Goal forall P Q : Prop, P -> P /\ Q.
Proof.
Fail delay.
delayed (intros; split; auto; delay); [idtac].
Abort.
Goal forall A (a: A), a = a.
Proof.
intros.
rauto.
Goal forall A (a: A), exists b, b = a.
Proof.
intros; eexists.
monotonicity.
Goal forall A (a b: A) `(HR: Equivalence A) (H: R a b), sum_rel R R (inl a) (inl b).
Proof.
intros.
rewrite H.
rewrite <- H.
reflexivity.
Goal forall A (a b: A) (R: rel A A) (f: A -> A) (p: A -> Prop), Monotonic f (R ++> R) -> Monotonic p (R --> impl) -> R a b -> p (f b) -> p (f a).
Proof.
intros A a b R f p Hf Hp Hab H.
rewrite <- Hab in H.
assumption.
Goal forall A B (RA: rel A A) (x y: A) (RB: rel B B) (z t: B), RA x y -> RB z t -> RA x y.
Proof.
intros.
rauto.
Goal forall A (a b: A) (R: rel A A) (H: R a b), let f (x y: A * A) := (@pair (A+A) (A+A) (inr (fst x)) (inl (snd y))) in Monotonic f (R * ⊤ ++> ⊤ * R ++> (⊥ + R) * (R + ⊥))%rel.
Proof.
intros; unfold f.
rauto.
Goal forall {A1 A2 B1 B2} (R1 R1': rel A1 A2) (R2 R2': rel B1 B2), subrel R1' R1 -> subrel R2 R2' -> subrel (R1 ++> R2) (R1' ++> R2').
Proof.
do 10 intro.
rauto.
Goal forall {A B} (R: rel A A) (op: A -> B) (Hop: (R ++> eq) op op) (x y: A) (Hxy: R x y), op x = op y.
Proof.
intros.
rauto.
Goal forall {A B} (RA: rel A A) (RB: rel B B) (m n: (A -> B) * B) (x: A), ((- ==> RB) * RB)%rel m n -> RB (fst m x) (fst n x).
Proof.
intros A B RA RB m n x Hmn.
try monotonicity.
try rauto.
Abort.
Goal forall {A B} (RA: rel A A) (RB: rel B B) (x y: A) (f: A -> A + B), RA x y -> (RA ++> RA + RB) f f -> RA (match f x with inl a => a | inr b => x end) (match f y with inl a => a | inr b => y end).
Proof.
intros.
rauto.
Goal forall {A B} (RA: rel A A) (RB: rel B B) (x y: A * B) (z: A), RA z z -> prod_rel RA RB x y -> RA (let (a, b) := x in z) (let (a, b) := y in z).
Proof.
intros.
rauto.
Goal forall {A} (R: rel A A), Monotonic (fun (b: bool) x y => if b then x else y) (- ==> R ++> R ++> R).
Proof.
intros.
rauto.
Goal forall {A} (R : rel A A) (b : bool) (x y : A), b = b -> R x x -> R y y -> R (if b then x else y) (if b then x else y).
Proof.
intros.
rauto.
Goal forall {A B C} R R' S (f: A -> B -> B -> C) (x1 y1: A) (x2 y2: B), Monotonic f (rel_curry (R ++> R' ++> S)) -> S (f x1 x2 x2) (f y1 y2 y2).
Proof.
intros A B C R R' S f x1 y1 x2 y2 Hf.
monotonicity.
Abort.
Goal forall {A} (R: rel A A) (f: A -> A) (C: A -> Prop) x y, Monotonic f (R ++> eq) -> R x y -> C (f x) -> C (f y).
Proof.
intros A R f C x y Hf Hxy.
Fail rauto.
pose proof @f_equal_relim.
rauto.
Goal forall {A} (R: rel A A) (x y: A), R x y -> eq y y -> R x y.
Proof.
intros A R x y Hxy Hyy.
monotonicity.
Goal forall {A} (R: rel A A) (x y: A), R x y -> eq x y -> R x y.
Proof.
intros A R x y Hxy Hyy.
try monotonicity.
Abort.
Goal forall {A} (R: rel A A) (f : A -> A), Monotonic f (R ++> R) -> (flip R ++> flip R) f f.
Proof.
intros A R f Hf.
rauto.
Goal forall {A} (R R': rel A A) (f: A -> A), Monotonic f (R ++> R) -> Related R' (flip R) subrel -> (R' ++> flip R) f f.
Proof.
intros A R R' f Hf HR.
rauto.
Goal forall A, exists R1 R2: relation (option A), (eqrel ==> R1 ==> R2 ==> flip impl)%signature option_le option_le.
Proof.
intros A.
eexists.
eexists.
rauto.
Goal forall A B C (R: rel A A) (f: A -> rel B C) a1 a2 b c, Monotonic f (R ++> subrel) -> R a1 a2 -> impl (f a1 b c) (f a2 b c).
Proof.
intros A B C R f a1 a2 b c Hf Ha.
monotonicity; rauto.
Goal forall A1 A2 B1 B2 (R1 R2: rel A1 A2) (R: rel B1 B2), subrel R1 R2 -> forall x y, (R2 ++> R) x y -> (R1 ++> R) x y.
Proof.
intros A1 A2 B1 B2 R1 R2 R HR12 x y.
rauto.
Goal forall A B (x1 x2 : A) (y1 y2 : B), x1 = x2 -> y1 = y2 -> (x1, y1) = (x2, y2).
Proof.
intros.
rauto.
Goal forall A1 A2 B1 B2 C1 C2 (R1 R2: rel A1 A2) (R1': rel B1 B2) (R: rel C1 C2), subrel R1 R2 -> forall x y, (R2 ++> R) x y -> (R1 ++> R) x y.
Proof.
intros A1 A2 B1 B2 C1 C2 R1 R2 R1' R HR12 x y H.
rewrite HR12.
assumption.
Goal forall A B (xa1 xa2 ya1 ya2 : A) (xb1 xb2 yb1 yb2 : B) (opA: A -> A -> A) (opB: B -> B -> B) (RA: rel A A) (RB: rel B B) (HopA: Monotonic opA (RA ++> RA ++> RA)) (HopB: Monotonic opB (RB ++> RB ++> RB)) (Hxa: RA xa1 xa2) (Hxb: RB xb1 xb2) (Hya: RA ya1 ya2) (Hyb: RB yb1 yb2), (RA * RB)%rel (opA xa1 ya1, opB xb1 yb1) (opA xa2 ya2, opB xb2 yb2).
Proof.
intros.
rauto.
Goal forall A1 A2 B1 B2 C1 C2 (R1 R2: rel A1 A2) (R1': rel B1 B2) (R: rel C1 C2), subrel R1 R2 -> forall x y, (R2 * R1' ++> R) x y -> (R1 * R1' ++> R) x y.
Proof.
intros A1 A2 B1 B2 C1 C2 R1 R2 R1' R HR12 x y H.
rewrite HR12.
assumption.
Goal forall {A} (R S T: rel A A), subrel R S -> subrel S R -> subrel S T -> subrel R T.
Proof.
intros.
rstep.
Goal forall `(PER) (x y z t : A), R x y -> R z y -> R z t -> R t x.
Proof.
intros.
rstep.
Goal forall A B (R : relation B) (f g : A -> B), exists X : relation (A -> B), X f g -> (- ==> R) f g.
Proof.
intros.
eexists.
intros.
Fail rauto.
monotonicity.
Abort.
Goal forall W acc A B C (R1: W -> rel A A) (R2: W -> rel B B) (R3: W -> rel C C), forall f g a b x w, Monotonic f (rforall w, R1 w ++> R2 w) -> Monotonic g (rforall w, R2 w ++> option_rel (rel_incr acc R3 w)) -> R1 w a b -> g (f a) = Some x -> exists y, rel_incr acc R3 w x y.
Proof.
intros.
transport H2.
eexists.
rauto.
Goal forall A B (R R': rel A B) l1 l2 x y, subrel R R' -> list_rel R l1 l2 -> R' x y -> list_rel R' (x :: l1) (y :: l2).
Proof.
intros.
rauto.
Goal forall A B (f: A -> B) (R: rel B B) x y, R (f x) (f y) -> (R @@ f) x y.
Proof.
intros.
rauto.

Goal forall {A} (R : rel A A) (b : bool) (x y : A), b = b -> R x x -> R y y -> R (if b then x else y) (if b then x else y).
Proof.
intros.
rauto.
