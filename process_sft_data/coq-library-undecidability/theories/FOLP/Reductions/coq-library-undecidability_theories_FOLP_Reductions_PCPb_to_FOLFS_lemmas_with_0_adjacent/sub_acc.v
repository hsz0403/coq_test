Require Import Equations.Equations.
Require Import Lia Arith.
Require Import Undecidability.PCP.PCP.
From Undecidability Require Import FOLP.FOLFS.
Require Import Undecidability.Shared.ListAutomation.
Import ListAutomationNotations.
Derive Signature for le.
Local Notation "| s |" := (length s) (at level 100).
Definition bstring n := { s : string bool | | s | <= n}.
Definition bnil n : bstring n.
Proof.
exists nil.
cbn.
lia.
Defined.
Definition bcons n (b : bool) : bstring n -> bstring (S n).
Proof.
intros [s H].
exists (b::s).
cbn.
lia.
Defined.
Definition bstring_step n (L : list (bstring n)) := [bnil (S n)] ++ map (bcons true) L ++ map (bcons false) L.
Definition bcast n s (H : |s| <= n) : bstring n := exist _ _ H.
Inductive what := pred | func.
Definition make_sig (T : what -> nat -> Type) : Signature := {| Funcs := {n & T func n} ; fun_ar := @projT1 _ _ ; Preds := {n & T pred n} ; pred_ar := @projT1 _ _ |}.
Inductive finsat_sig' : what -> nat -> Type := | f : bool -> finsat_sig' func 1 | e : finsat_sig' func 0 | dum : finsat_sig' func 0 | P : finsat_sig' pred 2 | less : finsat_sig' pred 2 | equiv : finsat_sig' pred 2.
Instance finsat_sig : Signature := make_sig finsat_sig'.
Definition i_f domain {I : interp domain} : bool -> domain -> domain := fun b x => (FullTarski.i_f (f := existT _ 1 (f b))) (Vector.cons x Vector.nil).
Definition i_e domain {I : interp domain} : domain := (FullTarski.i_f (f := existT _ 0 e)) Vector.nil.
Definition i_P domain {I : interp domain} : domain -> domain -> Prop := fun x y => (FullTarski.i_P (P := existT _ 2 P)) (Vector.cons x (Vector.cons y Vector.nil)).
Notation i_equiv x y := ((FullTarski.i_P (P := existT _ 2 equiv)) (Vector.cons x (Vector.cons y Vector.nil))).
Fixpoint iprep domain {I : interp domain} (x : list bool) (y : domain) := match x with | nil => y | b::x => i_f b (iprep x y) end.
Definition ienc domain {I : interp domain} (x : list bool) := iprep x i_e.
Local Definition BSRS := list (card bool).
Local Notation "x / y" := (x, y).
Section FIB.
Variable R : BSRS.
Definition obstring n := option (bstring n).
Notation obcast H := (Some (bcast H)).
Definition ccons n b (s : obstring n) : obstring n := match s with | Some (exist _ s _) => match (le_dec (|b::s|) n) with | left H => obcast H | right _ => None end | None => None end.
Definition cdrv n (s t : obstring n) := match s, t with | Some (exist _ s _), Some (exist _ t _) => derivable R s t | _, _ => False end.
Definition sub n (x y : obstring n) := match x, y with | Some (exist _ s _), Some (exist _ t _) => s <> t /\ exists s', t = s'++s | _, _ => False end.
Global Instance FIB n : interp (obstring n).
Proof.
split.
-
intros [k H]; cbn.
inversion H; subst.
+
intros v.
exact (ccons H0 (Vector.hd v)).
+
intros _.
exact (Some (bnil n)).
+
intros _.
exact None.
-
intros [k H]; cbn.
inversion H; subst.
+
intros v.
exact (cdrv (Vector.hd v) (Vector.hd (Vector.tl v))).
+
intros v.
exact (sub (Vector.hd v) (Vector.hd (Vector.tl v))).
+
intros v.
exact (eq (Vector.hd v) (Vector.hd (Vector.tl v))).
Defined.
Definition obembed n (s : obstring n) : obstring (S n) := match s with | Some (exist _ s H) => Some (exist _ s (le_S _ _ H)) | None => None end.
Section Ax.
Variable n : nat.
Implicit Type x y : obstring n.
End Ax.
End FIB.
Section Conv.
Variable R : BSRS.
Variable D : Type.
Hypothesis HD : listable D.
Variable I : interp D.
Notation sub x y := ((FullTarski.i_P (P := existT _ 2 less)) (Vector.cons x (Vector.cons y Vector.nil))).
Notation dum := ((FullTarski.i_f (f := existT _ 0 dum)) Vector.nil).
Hypothesis HP : forall x y, i_P x y -> x <> dum /\ y <> dum.
Hypothesis HS1 : forall x, ~ sub x x.
Hypothesis HS2 : forall x y z, sub x y -> sub y z -> sub x z.
Hypothesis HF1 : forall b x, i_f b x <> i_e.
Hypothesis HF2 : forall b1 b2 x y, i_f b1 x <> dum -> i_f b1 x = i_f b2 y -> x = y /\ b1 = b2.
Hypothesis HF3 : forall b x, i_f b x <> dum -> x <> dum.
Hypothesis HI : forall x y, i_P x y -> (exists s t, s/t el R /\ x = ienc s /\ y = ienc t) \/ (exists s t u v, s/t el R /\ x = iprep s u /\ y = iprep t v /\ i_P u v /\ ((sub u x /\ v = y) \/ (sub v y /\ u = x) \/ (sub u x /\ sub v y))).
Definition sub' L x y := sub x y /\ x el L.
Inductive psub : (D * D) -> (D * D) -> Prop := | psub1 x u : sub u x -> forall y, psub (u,y) (x,y) | psub2 y u : sub u y -> forall x, psub (x,u) (x,y) | psub3 x y u v : sub u x -> sub v y -> psub (u,v) (x,y).
End Conv.
Definition finsat phi := exists D (I : interp D) rho, listable D /\ (forall x y, i_equiv x y <-> eq x y) /\ rho ⊨ phi.
Section Reduction.
Notation "# x" := (var_term x) (at level 2).
Definition t_f b x := Func (existT _ 1 (f b)) (Vector.cons x Vector.nil).
Definition t_e := Func (existT _ 0 e) Vector.nil.
Definition t_dum := Func (existT _ 0 dum) Vector.nil.
Definition f_P x y := Pred (existT _ 2 P) (Vector.cons x (Vector.cons y Vector.nil)).
Notation "x ≡ y" := (Pred (existT _ 2 equiv) (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "x ≢ y" := (¬ (x ≡ y)) (at level 20).
Notation "x ≺ y" := (Pred (existT _ 2 less) (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Fixpoint tprep (x : list bool) (y : term) := match x with | nil => y | b::x => t_f b (tprep x y) end.
Definition tenc (x : list bool) := tprep x t_e.
Definition ax_P := ∀ ∀ f_P #1 #0 --> (#1 ≢ t_dum) ∧ (#0 ≢ t_dum).
Definition ax_S1 := ∀ ¬ (#0 ≺ #0).
Definition ax_S2 := ∀ ∀ ∀ #2 ≺ #1 --> #1 ≺ #0 --> #2 ≺ #0.
Definition ax_HF1_true := ∀ t_f true #0 ≢ t_e.
Definition ax_HF1_false := ∀ t_f false #0 ≢ t_e.
Definition ax_HF2_true := ∀ ∀ t_f true #1 ≢ t_dum --> t_f true #1 ≡ t_f true #0 --> #1 ≡ #0.
Definition ax_HF2_false := ∀ ∀ t_f false #1 ≢ t_dum --> t_f false #1 ≡ t_f false #0 --> #1 ≡ #0.
Definition ax_HF2 := ∀ ∀ t_f true #1 ≡ t_f false #0 --> (t_f true #1 ≡ t_dum ∧ t_f false #0 ≡ t_dum).
Definition ax_HF3_true := ∀ t_f true #0 ≢ t_dum --> #0 ≢ t_dum.
Definition ax_HF3_false := ∀ t_f false #0 ≢ t_dum --> #0 ≢ t_dum.
Definition ax_HI' c := (#1 ≡ tenc (fst c) ∧ #0 ≡ tenc (snd c)) ∨ (∃ ∃ #3 ≡ tprep (fst c) #1 ∧ #2 ≡ tprep (snd c) #0 ∧ f_P #1 #0 ∧ ((#1 ≺ #3 ∧ #0 ≡ #2) ∨ (#0 ≺ #2 ∧ #1 ≡ #3) ∨ (#1 ≺ #3 ∧ #0 ≺ #2))).
Definition ax_HI (R : BSRS) := ∀ ∀ f_P #1 #0 --> list_or (map ax_HI' R).
Definition finsat_formula (R : BSRS) := ax_P ∧ ax_S1 ∧ ax_S2 ∧ ax_HF1_true ∧ ax_HF1_false ∧ ax_HF2_true ∧ ax_HF2_false ∧ ax_HF2 ∧ ax_HF3_true ∧ ax_HF3_false ∧ ax_HI R ∧ ∃ f_P #0 #0.
End Reduction.

Lemma sub_acc x : Acc (fun a b => sub a b) x.
Proof.
destruct HD as [L HL].
induction (sub_acc' L x) as [x _ IH].
constructor.
intros y H.
now apply IH.
