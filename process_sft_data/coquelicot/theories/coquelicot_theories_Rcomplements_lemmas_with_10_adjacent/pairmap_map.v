Ltac evar_last := match goal with | |- ?f ?x => let tx := type of x in let tx := eval simpl in tx in let tmp := fresh "tmp" in evar (tmp : tx) ; refine (@eq_ind tx tmp f _ x _) ; unfold tmp ; clear tmp end.
Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.
Module MyNat.
End MyNat.
Require Import Even Div2.
Require Import mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool.
Open Scope R_scope.
Definition floor x := proj1_sig (floor_ex x).
Definition floor1 x := proj1_sig (floor1_ex x).
Definition nfloor x pr := proj1_sig (nfloor_ex x pr).
Definition nfloor1 x pr := proj1_sig (nfloor1_ex x pr).
Fixpoint pow2 (n : nat) : nat := match n with | O => 1%nat | S n => (2 * pow2 n)%nat end.
Definition pos_div_2 (eps : posreal) := mkposreal _ (is_pos_div_2 eps).
Definition sign (x : R) := match total_order_T 0 x with | inleft (left _) => 1 | inleft (right _) => 0 | inright _ => -1 end.
Definition belast {T : Type} (s : seq T) := match s with | [::] => [::] | h :: s => belast h s end.

Lemma rcons_ind {T : Type} (P : seq T -> Type) : P [::] -> (forall (s : seq T) (t : T), P s -> P (rcons s t)) -> forall s, P s.
Proof.
move => H0 Hr s ; move: (refl_equal (size s)).
move: {1}(size s) => n ; elim: n s => // [| n IH] s Hn ; case: s Hn => [| h s] Hn //.
have: ({s0 : _&{ t0 | h::s = rcons s0 t0}}) ; [| case => s0 [t0 H]].
elim: (s) (h) => {s h Hn IH} [| h s IH] h0.
exists [::] ; by exists h0.
case: (IH h) => s0 [t0 H] ; exists (h0::s0) ; exists t0 ; by rewrite rcons_cons -H.
Admitted.

Lemma rcons_dec {T : Type} (P : seq T -> Type) : (P [::]) -> (forall s t, P (rcons s t)) -> forall s, P s.
Proof.
move => H0 Hr ; case => [| h s] //.
have: ({s0 : _&{ t0 | h::s = rcons s0 t0}}) ; [| case => s0 [t0 H]].
elim: s h => [| h s IH] h0.
exists [::] ; by exists h0.
case: (IH h) => s0 [t0 H] ; exists (h0::s0) ; exists t0 ; by rewrite rcons_cons -H.
Admitted.

Lemma size_rcons_pos {T : Type} (s : seq T) (t : T) : (0 < size (rcons s t))%nat.
Proof.
Admitted.

Lemma foldr_rcons {T T0 : Type} : forall (f : T0 -> T -> T) x0 s t, foldr f x0 (rcons s t) = foldr f (f t x0) s.
Proof.
Admitted.

Lemma foldl_rcons {T T0 : Type} : forall (f : T -> T0 -> T) x0 s t, foldl f x0 (rcons s t) = f (foldl f x0 s) t.
Proof.
Admitted.

Lemma head_rcons {T : Type} (x0 : T) (s : seq T) (t : T) : head x0 (rcons s t) = head t s.
Proof.
Admitted.

Lemma behead_rcons {T : Type} (s : seq T) (t : T) : (0 < size s)%nat -> behead (rcons s t) = rcons (behead s) t.
Proof.
Admitted.

Lemma behead_rev {T : Type} (s : seq T) : behead (rev s) = rev (belast s).
Proof.
case: s => // t s ; elim: s t => // t s IHs t0.
Admitted.

Lemma pairmap_rcons {T T0 : Type} (f : T -> T -> T0) (s : seq T) h0 h x0 : pairmap f x0 (rcons (rcons s h0) h) = rcons (pairmap f x0 (rcons s h0)) (f h0 h).
Proof.
Admitted.

Lemma map_pairmap {T T0 T1 : Type} (f : T0 -> T1) (g : T -> T -> T0) (s : seq T) (x0 : T) : map f (pairmap g x0 s) = pairmap (fun x y => f (g x y)) x0 s.
Proof.
elim: s x0 => [| h s IH] x0 //=.
Admitted.

Lemma size_unzip1 {T T0 : Type} (s : seq (T * T0)) : size (unzip1 s) = size s.
Proof.
Admitted.

Lemma size_unzip2 {T T0 : Type} (s : seq (T * T0)) : size (unzip2 s) = size s.
Proof.
Admitted.

Lemma zip_cons {S T : Type} hs ht (s : seq S) (t : seq T) : zip (hs :: s) (ht :: t) = (hs,ht) :: zip s t.
Proof.
Admitted.

Lemma zip_rcons {S T : Type} (s : seq S) (t : seq T) hs ht : size s = size t -> zip (rcons s hs) (rcons t ht) = rcons (zip s t) (hs,ht).
Proof.
elim: s t hs ht => [| hs s IHs] ; case => //= ht t hs' ht' Hs.
Admitted.

Lemma unzip1_rcons {S T : Type} (s : seq (S*T)) (h : S*T) : unzip1 (rcons s h) = rcons (unzip1 s) (fst h).
Proof.
Admitted.

Lemma unzip2_rcons {S T : Type} (s : seq (S*T)) (h : S*T) : unzip2 (rcons s h) = rcons (unzip2 s) (snd h).
Proof.
Admitted.

Lemma unzip1_belast {S T : Type} (s : seq (S*T)) : unzip1 (belast s) = belast (unzip1 s).
Proof.
Admitted.

Lemma unzip2_belast {S T : Type} (s : seq (S*T)) : unzip2 (belast s) = belast (unzip2 s).
Proof.
Admitted.

Lemma unzip1_behead {S T : Type} (s : seq (S*T)) : unzip1 (behead s) = behead (unzip1 s).
Proof.
Admitted.

Lemma unzip2_behead {S T : Type} (s : seq (S*T)) : unzip2 (behead s) = behead (unzip2 s).
Proof.
Admitted.

Lemma pairmap_map {T T0 T1 : Type} (f : T0 -> T0 -> T1) (g : T -> T0) (s : seq T) (x0 : T) : pairmap f (g x0) (map g s) = pairmap (fun x y => f (g x) (g y)) x0 s.
Proof.
elim: s x0 => [| h s IH] x0 //=.
by rewrite IH.
