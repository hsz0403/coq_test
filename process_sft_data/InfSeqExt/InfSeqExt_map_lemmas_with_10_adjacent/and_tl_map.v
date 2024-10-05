Require Import InfSeqExt.infseq.
Require Import InfSeqExt.exteq.
Section sec_map.
Variable A B: Type.
CoFixpoint map (f: A->B) (s: infseq A): infseq B := match s with | Cons x s => Cons (f x) (map f s) end.
End sec_map.
Arguments map [A B] _ _.
Arguments map_Cons [A B] _ _ _.
Section sec_zip.
Variable A B: Type.
CoFixpoint zip (sA: infseq A) (sB: infseq B) : infseq (A*B) := match sA, sB with | Cons a sA0, Cons b sB0 => Cons (a, b) (zip sA0 sB0) end.
End sec_zip.
Arguments zip [A B] _ _.
Arguments zip_Cons [A B] _ _ _ _.
Section sec_map_modalop.
Variable A B: Type.
Definition fstAB := fst (A:=A) (B:=B).
End sec_map_modalop.
Arguments and_tl_map [A B f P P' Q Q'] _ _ [s] _.
Arguments and_tl_map_conv [A B f P P' Q Q'] _ _ [s] _.
Arguments or_tl_map [A B f P P' Q Q'] _ _ [s] _.
Arguments or_tl_map_conv [A B f P P' Q Q'] _ _ [s] _.
Arguments impl_tl_map [A B f P P' Q Q'] _ _ [s] _ _.
Arguments impl_tl_map_conv [A B f P P' Q Q'] _ _ [s] _ _.
Arguments not_tl_map [A B f P Q] _ [s] _ _.
Arguments not_tl_map_conv [A B f P Q] _ [s] _ _.
Arguments now_map [A B f P s] _.
Arguments now_map_conv [A B f P s] _.
Arguments next_map [A B f P Q] _ [s] _.
Arguments next_map_conv [A B f P Q] _ [s] _.
Arguments consecutive_map [A B f P s] _.
Arguments consecutive_map_conv [A B f P s] _.
Arguments always_map [A B f P Q] _ [s] _.
Arguments always_map_conv_ext [A B f P Q J] _ _ [s] _ _.
Arguments always_map_conv [A B f P Q] _ [s] _.
Arguments weak_until_map [A B f J P K Q] _ _ [s] _.
Arguments weak_until_map_conv [A B f J P K Q] _ _ [s] _.
Arguments until_map [A B f J P K Q] _ _ [s] _.
Arguments release_map [A B f J P K Q] _ _ [s] _.
Arguments release_map_conv [A B f J P K Q] _ _ [s] _.
Arguments eventually_map [A B f P Q] _ [s] _.
Arguments eventually_map_conv_ext [A B f P Q J] _ _ _ _ _ [s] _ _.
Arguments eventually_map_conv [A B f P Q] _ _ _ [s] _.
Arguments eventually_map_monotonic [A B f P Q] _ _ _ _ _ [s] _ _ _.
Arguments inf_often_map [A B f P Q] _ [s] _.
Arguments inf_often_map_conv [A B f P Q] _ _ _ [s] _.
Arguments continuously_map [A B f P Q] _ [s] _.
Arguments continuously_map_conv [A B f P Q] _ _ _ [s] _.
Arguments eventually_now_map [A B f P s] _.
Arguments eventually_now_map_conv [A B f P s] _.
Arguments eventually_map_now_eq [A B f a s] _.

Lemma map_Cons: forall (f:A->B) x s, map f (Cons x s) = Cons (f x) (map f s).
Proof using.
intros.
pattern (map f (Cons x s)).
rewrite <- recons.
simpl.
Admitted.

Lemma zip_Cons: forall (a:A) (b:B) sA sB, zip (Cons a sA) (Cons b sB) = Cons (a, b) (zip sA sB).
Proof using.
intros.
pattern (zip (Cons a sA) (Cons b sB)); rewrite <- recons.
simpl.
Admitted.

Lemma and_tl_map_conv : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, Q (map f s) -> P s) -> (forall s, Q' (map f s) -> P' s) -> forall (s: infseq A), (Q /\_ Q') (map f s) -> (P /\_ P') s.
Proof using.
Admitted.

Lemma or_tl_map : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, P s -> Q (map f s)) -> (forall s, P' s -> Q' (map f s)) -> forall (s: infseq A), (P \/_ P') s -> (Q \/_ Q') (map f s).
Proof using.
Admitted.

Lemma or_tl_map_conv : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, Q (map f s) -> P s) -> (forall s, Q' (map f s) -> P' s) -> forall (s: infseq A), (Q \/_ Q') (map f s) -> (P \/_ P') s.
Proof using.
Admitted.

Lemma impl_tl_map : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, Q (map f s) -> P s) -> (forall s, P' s -> Q' (map f s)) -> forall (s: infseq A), (P ->_ P') s -> (Q ->_ Q') (map f s).
Proof using.
Admitted.

Lemma impl_tl_map_conv : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, P s -> Q (map f s)) -> (forall s, Q' (map f s) -> P' s) -> forall (s: infseq A), (Q ->_ Q') (map f s) -> (P ->_ P') s.
Proof using.
Admitted.

Lemma not_tl_map : forall (f: A->B) (P : infseq A->Prop) (Q: infseq B->Prop), (forall s, Q (map f s) -> P s) -> forall (s: infseq A), (~_ P) s -> (~_ Q) (map f s).
Proof using.
Admitted.

Lemma not_tl_map_conv : forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop), (forall s, P s -> Q (map f s)) -> forall (s: infseq A), (~_ Q) (map f s) -> (~_ P) s.
Proof using.
Admitted.

Lemma now_map : forall (f: A->B) (P: B->Prop) (s: infseq A), now (fun x => P (f x)) s -> now P (map f s).
Proof using.
Admitted.

Lemma now_map_conv : forall (f: A->B) (P: B->Prop) (s: infseq A), now P (map f s) -> now (fun x => P (f x)) s.
Proof using.
Admitted.

Lemma next_map : forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop), (forall s, P s -> Q (map f s)) -> forall (s: infseq A), next P s -> next Q (map f s).
Proof using.
Admitted.

Lemma and_tl_map : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, P s -> Q (map f s)) -> (forall s, P' s -> Q' (map f s)) -> forall (s: infseq A), (P /\_ P') s -> (Q /\_ Q') (map f s).
Proof using.
unfold and_tl; intuition.
