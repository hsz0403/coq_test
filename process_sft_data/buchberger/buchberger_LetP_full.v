Definition LetP : forall (A B : Set) (h : A), (forall u : A, u = h -> B) -> B.
intros A B h H'.
apply H' with (u := h).
auto.
Defined.