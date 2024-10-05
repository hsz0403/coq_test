Require Import Verdi.Verdi.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Fixpoint distinct_pairs_and {A} (R : A -> A -> Prop) (l : list A) : Prop := match l with | [] => True | x :: xs => (forall y, In y xs -> R x y) /\ distinct_pairs_and R xs end.
Class Decomposition (B : BaseParams) (M : MultiParams B) := { state_invariant : (name -> data) -> Prop; network_invariant : (name -> data) -> packet -> Prop; network_network_invariant : packet -> packet -> Prop; network_network_invariant_sym : forall p1 p2, network_network_invariant p1 p2 -> network_network_invariant p2 p1 ; state_invariant_init : state_invariant init_handlers; state_invariant_maintained_input : forall h inp sigma st' out ps, input_handlers h inp (sigma h) = (out, st', ps) -> state_invariant sigma -> state_invariant (update name_eq_dec sigma h st'); state_invariant_maintained_deliver : forall p sigma st' out ps, net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) -> state_invariant sigma -> network_invariant sigma p -> state_invariant (update name_eq_dec sigma (pDst p) st'); network_invariant_maintained_input_old : forall h inp sigma st' out ps p, input_handlers h inp (sigma h) = (out, st', ps) -> state_invariant sigma -> network_invariant sigma p -> network_invariant (update name_eq_dec sigma h st') p; network_invariant_maintained_input_new : forall h inp sigma st' out ps p, input_handlers h inp (sigma h) = (out, st', ps) -> state_invariant sigma -> In (pDst p, pBody p) ps -> pSrc p = h -> network_invariant (update name_eq_dec sigma h st') p; network_invariant_maintained_deliver_old : forall sigma st' out ps p q, net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) -> state_invariant sigma -> network_invariant sigma p -> network_invariant sigma q -> network_network_invariant p q -> network_invariant (update name_eq_dec sigma (pDst p) st') q; network_invariant_maintained_deliver_new : forall sigma st' out ps p p', net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) -> state_invariant sigma -> network_invariant sigma p -> In (pDst p', pBody p') ps -> pSrc p' = pDst p -> network_invariant (update name_eq_dec sigma (pDst p) st') p'; network_network_invariant_maintained_input_old : forall h inp sigma st' out ps p p', input_handlers h inp (sigma h) = (out, st', ps) -> state_invariant sigma -> network_invariant sigma p -> In (pDst p', pBody p') ps -> pSrc p' = h -> network_network_invariant p p'; network_network_invariant_maintained_input_new : forall h inp sigma st' out ps, input_handlers h inp (sigma h) = (out, st', ps) -> state_invariant sigma -> distinct_pairs_and network_network_invariant (map (fun m => mkPacket h (fst m) (snd m)) ps); network_network_invariant_maintained_deliver_old : forall sigma st' out ps p p' q, net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) -> state_invariant sigma -> network_invariant sigma p -> network_invariant sigma q -> network_network_invariant p q -> In (pDst p', pBody p') ps -> pSrc p' = pDst p -> network_network_invariant p' q; network_network_invariant_maintained_deliver_new : forall sigma st' out ps p, net_handlers (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ps) -> state_invariant sigma -> network_invariant sigma p -> distinct_pairs_and network_network_invariant (map (fun m => mkPacket (pDst p) (fst m) (snd m)) ps) }.
Section Decomposition.
Context `{d : Decomposition}.
Definition packet_eq_dec : forall p1 p2 : packet, {p1 = p2} + {p1 <> p2}.
Proof.
intros.
decide equality; eauto using name_eq_dec,msg_eq_dec.
Defined.
Definition composed_invariant net := (state_invariant (nwState net)) /\ (forall p, In p (nwPackets net) -> network_invariant (nwState net) p) /\ (distinct_pairs_and network_network_invariant (nwPackets net)).
End Decomposition.

Lemma distinct_pairs_and_app_cons : forall A R xs p ys l, l = (xs ++ p :: ys) -> distinct_pairs_and (A:=A) R l -> distinct_pairs_and R (xs ++ ys).
Proof using.
induction xs; intros; subst; simpl in *; intuition eauto.
