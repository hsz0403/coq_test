Require Export Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes Undecidability.Shared.Libs.PSL.FiniteTypes.BasicFinTypes Undecidability.Shared.Libs.PSL.FiniteTypes.CompoundFinTypes Undecidability.Shared.Libs.PSL.FiniteTypes.VectorFin.
Require Export Undecidability.Shared.Libs.PSL.Vectors.FinNotation.
Require Export Undecidability.Shared.Libs.PSL.Retracts.
Require Export Undecidability.Shared.Libs.PSL.Inhabited.
Require Export Undecidability.Shared.Libs.PSL.Base.
Require Export Undecidability.Shared.Libs.PSL.Vectors.Vectors Undecidability.Shared.Libs.PSL.Vectors.VectorDupfree.
Require Export smpl.Smpl Lia.
Global Open Scope vector_scope.
Section Loop.
Variable (A : Type) (f : A -> A) (p : A -> bool).
Fixpoint loop (a : A) (k : nat) {struct k} := if p a then Some a else match k with | O => None | S k' => loop (f a) k' end.
End Loop.
Section LoopLift.
Variable A B : Type.
Variable lift : A -> B.
Variable (f : A -> A) (f' : B -> B).
Variable (h : A -> bool) (h' : B -> bool).
Hypothesis halt_lift_comp : forall x:A, h' (lift x) = h x.
Hypothesis step_lift_comp : forall x:A, h x = false -> f' (lift x) = lift (f x).
End LoopLift.
Section LoopMerge.
Variable A : Type.
Variable f : A -> A.
Variable (h h' : A -> bool).
Hypothesis halt_comp : forall a, h a = false -> h' a = false.
End LoopMerge.
Section Map.
Variable X Y Z : Type.
Definition map_opt : (X -> Y) -> option X -> option Y := fun f a => match a with | Some x => Some (f x) | None => None end.
Definition map_inl : (X -> Y) -> X + Z -> Y + Z := fun f a => match a with | inl x => inl (f x) | inr y => inr y end.
Definition map_inr : (Y -> Z) -> X + Y -> X + Z := fun f a => match a with | inl y => inl y | inr x => inr (f x) end.
Definition map_fst : (X -> Z) -> X * Y -> Z * Y := fun f '(x,y) => (f x, y).
Definition map_snd : (Y -> Z) -> X * Y -> X * Z := fun f '(x,y) => (x, f y).
End Map.
Definition funcomp {X Y Z : Type} (g : Y -> Z) (f : X -> Y) : X -> Z := fun x => g (f x).
Arguments funcomp {X Y Z} (g f) x/.
Notation "g >> f" := (funcomp f g) (at level 40).
Fixpoint plus' (n m : nat) { struct n } : nat := match n with | 0 => m | S p => S (plus' p m) end.
Fixpoint FinR {m} n (p : Fin.t m) : Fin.t (plus' n m) := match n with | 0 => p | S n' => Fin.FS (FinR n' p) end.
Definition fold_opt (X Y : Type) : (X -> Y) -> Y -> option X -> Y := fun f def o => match o with | Some o' => f o' | None => def end.

Lemma map_opt_fold (X Y : Type) (f : X -> Y) (x : option X) : map_opt f x = fold_opt (fun x => Some (f x)) None x.
Proof.
intros.
destruct x; cbn; reflexivity.
