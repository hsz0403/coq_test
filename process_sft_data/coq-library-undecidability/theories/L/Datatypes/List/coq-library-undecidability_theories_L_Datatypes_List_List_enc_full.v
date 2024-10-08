From Undecidability.L.Tactics Require Import LTactics GenEncode.
Set Default Proof Using "Type".
Section Fix_X.
Variable (X:Type).
Context {intX : registered X}.
MetaCoq Run (tmGenEncode "list_enc" (list X)).
Global Instance termT_cons : computableTime' (@cons X) (fun a aT => (1,fun A AT => (1,tt))).
Proof.
extract constructor.
solverec.
Qed.
End Fix_X.
Hint Resolve list_enc_correct : Lrewrite.