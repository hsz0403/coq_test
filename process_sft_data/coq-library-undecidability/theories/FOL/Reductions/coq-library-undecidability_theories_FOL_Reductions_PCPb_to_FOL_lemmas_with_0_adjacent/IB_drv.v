From Undecidability.PCP Require Import PCP Util.PCP_facts.
From Undecidability.FOL Require Import Util.Deduction Util.Tarski Util.Syntax_facts FOL.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
Require Import Undecidability.PCP.Reductions.PCPb_iff_dPCPb.
Local Definition BSRS := list(card bool).
Local Notation "x / y" := (x, y).
Notation t_f b t := (func (s_f b) (Vector.cons _ t _ (Vector.nil _))).
Notation t_e := (func s_e (Vector.nil _)).
Notation Pr t t' := (@atom _ sig_pred _ _ sPr (Vector.cons _ t _ (Vector.cons _ t' _ (Vector.nil _)))).
Notation Q := (atom sQ (Vector.nil _)).
Notation i_f b i := (@i_func _ _ _ _ (s_f b) (Vector.cons _ i _ (Vector.nil _))).
Notation i_Pr i i' := (@i_atom _ _ _ _ sPr (Vector.cons _ i _ (Vector.cons _ i' _ (Vector.nil _)))).
Section validity.
Context {ff : falsity_flag}.
Variable R : BSRS.
Fixpoint prep (x : string bool) (t : term) : term := match x with | nil => t | b::x => t_f b (prep x t) end.
Definition enc s := (prep s t_e).
Fixpoint iprep {domain} {I : interp domain} (x : list bool) (y : domain) := match x with | nil => y | b::x => i_f b (iprep x y) end.
Definition F1 := map (fun '(x,y) => Pr (enc x) (enc y)) R.
Definition F2 := map (fun '(x, y) => ∀ ∀ Pr $1 $0 --> Pr (prep x $1) (prep y $0)) R.
Definition F3 := (∀ Pr $0 $0 --> Q).
Definition F : form := F1 ==> F2 ==> F3 --> Q.
Global Instance IB : interp (string bool).
Proof.
split; intros [] v.
-
exact (b :: Vector.hd v).
-
exact nil.
-
exact (derivable R (Vector.hd v) (Vector.hd (Vector.tl v))).
-
exact (dPCPb R).
Defined.
Definition ctx_S := F3 :: rev F2 ++ rev F1.
End validity.
Hint Resolve stack_enum form_discrete : core.
Definition UA := ~ enumerable (complement PCPb).
Module NonStan.
Section Nonstan.
Variable R : BSRS.
Context {ff : falsity_flag}.
Instance IB : interp (option (string bool)).
Proof.
split; intros [] v.
-
exact (match Vector.hd v with Some u => Some (b :: u) | None => None end).
-
exact (Some nil).
-
exact (match Vector.hd v, Vector.hd (Vector.tl v) with Some u, Some v => derivable R u v | _, _ => True end).
-
exact False.
Defined.
End Nonstan.
End NonStan.

Lemma IB_drv rho t1 t2 : rho ⊨ (Pr t1 t2) <-> derivable R (eval rho t1) (eval rho t2).
Proof.
cbn.
reflexivity.
