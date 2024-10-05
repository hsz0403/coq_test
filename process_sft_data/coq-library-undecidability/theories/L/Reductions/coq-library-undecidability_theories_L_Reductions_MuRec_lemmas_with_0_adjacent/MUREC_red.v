Require Import Equations.Equations.
Require Equations.Prop.EqDec.
From Undecidability.H10 Require Import H10 dio_single dio_logic.
From Undecidability.L.Datatypes Require Import LNat Lists LOptions LSum.
From Undecidability.L Require Import Tactics.LTactics Computability.MuRec Computability.Synthetic Tactics.GenEncode.
From Undecidability.Shared Require Import DLW.Utils.finite DLW.Vec.vec DLW.Vec.pos.
From Undecidability.MuRec Require Import recalg ra_bs ra_sem_eq.
Reserved Notation " '[' f ';' v ';' min ';' c ']' '~~>' x " (at level 70).
Inductive ra_bs_c : nat -> nat -> forall k, recalg k -> vec nat k -> nat -> Prop := | in_ra_bs_c_cst : forall min c n v, [ra_cst n; v; min; S c] ~~> n | in_ra_bs_c_zero : forall min c v, [ra_zero; v; min; S c] ~~> 0 | in_ra_bs_c_succ : forall min c v, [ra_succ; v; min; S c] ~~> S (vec_head v) | in_ra_bs_c_proj : forall min c k v j, [@ra_proj k j; v; min; S c] ~~> vec_pos v j | in_ra_bs_c_comp : forall min c k i f (gj : vec (recalg i) k) v w x, (forall j, [vec_pos gj j; v; min; c - pos2nat j] ~~> vec_pos w j) -> [f; w; min; S c] ~~> x -> [ra_comp f gj; v; min; S (S c)] ~~> x | in_ra_bs_c_rec_0 : forall min c k f (g : recalg (S (S k))) v x, [f; v; min; c] ~~> x -> [ra_rec f g; 0##v; min; S c] ~~> x | in_ra_bs_c_rec_S : forall min c k f (g : recalg (S (S k))) v n x y, [ra_rec f g; n##v; min; c] ~~> x -> [g; n##x##v; min; c] ~~> y -> [ra_rec f g; S n##v; min; S c] ~~> y | in_ra_bs_c_min : forall min c k (f : recalg (S k)) v x w , x >= min -> (forall j : pos x, pos2nat j >= min -> [f; pos2nat j##v; 0; c - (pos2nat j - min)] ~~> S (vec_pos w j)) -> [f; x##v; 0; c - (x - min)] ~~> 0 -> [ra_min f; v; min; S c] ~~> x where " [ f ; v ; min ; c ] ~~> x " := (@ra_bs_c min c _ f v x).
Local Hint Resolve ra_bs_from_c ra_bs_to_c : core.
Fact ra_bs_c_correct k (f : recalg k) v x : [|f|] v x <-> exists c, [f ; v ; 0 ; c] ~~> x.
Proof.
rewrite ra_bs_correct; split; auto.
intros (c & H); revert H; apply ra_bs_from_c.
Require Import Undecidability.L.Reductions.MuRec.MuRec_extract.
Definition rec_erase i (erase : forall i, recalg i -> reccode) := (fix rec k (v : vec (recalg i) k) := match v with vec_nil => rc_nil | x ## v => rc_cons (erase _ x) (rec _ v) end).
Fixpoint erase k (f : recalg k) : reccode := match f with | ra_cst n => rc_cst n | ra_zero => rc_zero | ra_succ => rc_succ | ra_proj _ p => rc_proj (pos2nat p) | ra_comp _ _ f g => rc_comp (erase f) (rec_erase erase g) | ra_rec _ f g => rc_rec (erase f) (erase g) | ra_min _ f => rc_min (erase f) end.
Require Import Undecidability.L.Reductions.MuRec.MuRec_extract.
Definition evalfun fuel c v := match eval fuel 0 c v with Some (inl x) => Some x | _ => None end.
Definition UMUREC_HALTING c := exists fuel, evalfun fuel c nil <> None.
Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Local Definition r := (fun c n => match eval n 0 c [] with Some (inl n) => true | _ => false end).

Lemma MUREC_red : MUREC_HALTING ⪯ UMUREC_HALTING.
Proof.
unshelve eexists.
-
intros f.
exact (erase f).
-
unfold UMUREC_HALTING, MUREC_HALTING.
intros f.
split; intros [].
+
rewrite ra_bs_correct in H.
eapply ra_bs_to_c in H as [].
exists x0.
eapply erase_correct in H.
unfold evalfun.
cbn in H.
rewrite H.
congruence.
+
unfold evalfun in H.
destruct eval eqn:E; try congruence.
destruct s; try congruence.
eapply erase_correct with (v := vec_nil) in E.
exists n.
eapply ra_bs_correct.
now eapply ra_bs_from_c.
