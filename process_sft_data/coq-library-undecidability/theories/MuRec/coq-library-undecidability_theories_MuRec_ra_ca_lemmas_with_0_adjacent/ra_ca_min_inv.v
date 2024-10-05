Require Import Arith Eqdep_dec.
From Undecidability.Shared Require Import DLW.Utils.utils DLW.Vec.vec DLW.Vec.pos.
From Undecidability.MuRec Require Import recalg.
Set Implicit Arguments.
Set Default Proof Using "Type".
Reserved Notation " '[' f ';' v ']' '-[' n '>>' x " (at level 70).
Inductive ra_ca : forall k, recalg k -> vec nat k -> nat -> nat -> Prop := | in_ra_ca_cst : forall n v, [ra_cst n; v] -[ 1 >> n | in_ra_ca_zero : forall v, [ra_zero; v] -[ 1 >> 0 | in_ra_ca_succ : forall v, [ra_succ; v] -[ 1 >> S (vec_head v) | in_ra_ca_proj : forall k v j, [@ra_proj k j; v] -[ 1 >> vec_pos v j | in_ra_ca_comp : forall k i f (gj : vec (recalg i) k) v q w p x, (forall j, [vec_pos gj j; v] -[ vec_pos q j >> vec_pos w j) -> [f; w] -[ p >> x -> [ra_comp f gj; v] -[1+p+vec_sum q>> x | in_ra_ca_rec_0 : forall k f (g : recalg (S (S k))) v n x, [f; v] -[ n >> x -> [ra_rec f g; 0##v] -[ S n >> x | in_ra_ca_rec_S : forall k f (g : recalg (S (S k))) v n p x q y, [ra_rec f g; n##v] -[ p >> x -> [g; n##x##v] -[ q >> y -> [ra_rec f g; S n##v] -[ 1+p+q >> y | in_ra_ca_min : forall k (f : recalg (S k)) v x p w q , (forall j : pos x, [f; pos2nat j##v] -[ vec_pos q j >> S (vec_pos w j)) -> [f; x##v] -[ p >> 0 -> [ra_min f; v] -[1+p+vec_sum q>> x where " [ f ; v ] -[ n >> x " := (@ra_ca _ f v n x).
Section inversion_lemmas.
Local Ltac myinv := let H := fresh in intros H; apply ra_ca_inv in H; destruct H as [ (? & ? & ?) | [ (? & ? & ? & ?) | [ (? & ? & ? & ?) | [ (? & ? & ? & ?) | [ (? & ? & ? & w' & q' & m' & ? & ? & ? & ?) | [ (? & ? & ? & ? & m' & ? & ? & ? & ?) | [ (? & ? & ? & y' & ? & ? & p' & q' & ? & ? & ? & ? & ?) | (? & m' & w' & q' & ? & ? & ? & ?) ] ] ] ] ] ] ].
Ltac injc H := injection H; clear H; repeat match goal with |- _ = _ -> _ => intro; subst end.
Ltac eqgoal := match goal with |- ?a -> ?b => replace a with b; auto end.
Ltac inst H := let K := fresh in match goal with | [ G : ?x -> _ |- _ ] => match G with H => assert (x) as K; [ clear H | specialize (H K); clear K ] end end.
Fact eq_gen { X } (P : X -> Type) x : (forall y, y = x -> P y) -> P x.
Proof.
intros H; apply H, eq_refl.
Ltac gen_eq t := apply eq_gen with (x := t).
Fact eq_nat_pirr (n m : nat) (H1 H2 : n = m) : H1 = H2.
Proof.
apply UIP_dec, eq_nat_dec.
Ltac natid := repeat match goal with | [ H: ?x = ?x :> nat |- _ ] => let G := fresh in generalize (@eq_nat_pirr _ _ H eq_refl); intros G; subst H end; simpl eq_rect in * |- *.
Local Ltac natSimpl := repeat match goal with [ H : S _ = S _ |- _ ] => let G := fresh in injection H; intro G; subst; natid end.
Local Ltac mydiscr := repeat match goal with | H : _ = _ :> nat |- _ => discriminate H; fail | H : _ = _ :> recalg _ |- _ => discriminate H; fail end.
Local Ltac myauto := myinv; subst; natid; natSimpl; mydiscr; auto.
Local Ltac ra_inj := match goal with | H : ra_proj _ = ra_proj _ |- _ => apply ra_proj_inj in H | H : ra_comp _ _ = ra_comp _ _ |- _ => apply ra_comp_inj in H; destruct H as (? & ? & ?) | H : ra_rec _ _ = ra_rec _ _ |- _ => apply ra_rec_inj in H; destruct H | H : ra_min _ = ra_min _ |- _ => apply ra_min_inj in H end; subst; simpl in * |- *.
End inversion_lemmas.

Lemma ra_ca_min_inv k f v n x : [@ra_min k f;v] -[n>> x -> exists p w q, n = 1+p+vec_sum q /\ [f;x##v] -[p>> 0 /\ forall j, [f;pos2nat j##v] -[vec_pos q j>> S (@vec_pos _ x w j).
Proof.
myauto; ra_inj.
exists q', w', m'; auto.
