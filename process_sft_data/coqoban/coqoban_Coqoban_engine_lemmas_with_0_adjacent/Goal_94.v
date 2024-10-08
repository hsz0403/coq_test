Set Implicit Arguments.
Unset Strict Implicit.
Inductive fieldtype : Type := | Empty : fieldtype | Wall : fieldtype | Keeper : fieldtype | Box : fieldtype | Dest : fieldtype (* fields to put a box on (destination fields) *) | Full : fieldtype (* a destination field with a box on it *) | KeepOD : fieldtype.
Inductive Direction : Type := | No : Direction | Ea : Direction | So : Direction | We : Direction.
Inductive Row : Type := | Nil : Row | C : fieldtype -> Row -> Row.
Inductive Board : Type := | Nothing : Board | R : Row -> Board -> Board | K : Row -> Board -> Board.
Definition fieldready (x : fieldtype) : Prop := match x with | Box => False | _ => True end.
Fixpoint rowready (r : Row) : Prop := match r with | Nil => True | C x xs => fieldready x /\ rowready xs end.
Fixpoint ready (b : Board) : Prop := match b with | Nothing => True | R row b' => rowready row /\ ready b' | K row b' => rowready row /\ ready b' end.
Record triple : Type := tri {t1 : fieldtype; t2 : fieldtype; t3 : fieldtype}.
Inductive Can : Type := | CAN : triple -> Can | CANT : Can.
Inductive Tri : Type := | TrS : Row -> Row -> Row -> Tri (* S - pushing Succesfully *) | TrF : Row -> Row -> Row -> Tri.
Definition move (tr : triple) : Can := match tr with | tri Keeper Empty x => CAN (tri Empty Keeper x) | tri Keeper Dest x => CAN (tri Empty KeepOD x) | tri Keeper Box Empty => CAN (tri Empty Keeper Box) | tri Keeper Box Dest => CAN (tri Empty Keeper Full) | tri Keeper Full Empty => CAN (tri Empty KeepOD Box) | tri Keeper Full Dest => CAN (tri Empty KeepOD Full) | tri KeepOD Empty x => CAN (tri Dest Keeper x) | tri KeepOD Dest x => CAN (tri Dest KeepOD x) | tri KeepOD Box Empty => CAN (tri Dest Keeper Box) | tri KeepOD Box Dest => CAN (tri Dest Keeper Full) | tri KeepOD Full Empty => CAN (tri Dest KeepOD Box) | tri KeepOD Full Dest => CAN (tri Dest KeepOD Full) | _ => CANT end.
Fixpoint rowstepeast (r : Row) : Row := match r with | C x rs => match rs with | C y (C z rs') => match move (tri x y z) with | CAN (tri x' y' z') => C x' (C y' (C z' rs')) | CANT => C x (rowstepeast rs) end | _ => r end | Nil => Nil end.
Fixpoint rowstepwest (r : Row) : Row := match r with | C x rs => match rs with | C y (C z rs') => match move (tri z y x) with | CAN (tri z' y' x') => C x' (C y' (C z' rs')) | CANT => C x (rowstepwest rs) end | _ => r end | Nil => Nil end.
Fixpoint Tristep' (r1 : Row) : Row -> Row -> Tri := fun r2 r3 => match r1 with | Nil => TrF r1 r2 r3 | C Keeper r1s => match r2, r3 with | C y r2s, C z r3s => match move (tri Keeper y z) with | CAN (tri x' y' z') => TrS (C x' r1s) (C y' r2s) (C z' r3s) | CANT => TrF r1 r2 r3 end | _, _ => TrF r1 r2 r3 end | C KeepOD r1s => match r2, r3 with | C y r2s, C z r3s => match move (tri KeepOD y z) with | CAN (tri x' y' z') => TrS (C x' r1s) (C y' r2s) (C z' r3s) | CANT => TrF r1 r2 r3 end | _, _ => TrF r1 r2 r3 end | C x r1s => match r2, r3 with | C y r2s, C z r3s => match Tristep' r1s r2s r3s with | TrS r1' r2' r3' => TrS (C x r1') (C y r2') (C z r3') | TrF r1' r2' r3' => TrF (C x r1') (C y r2') (C z r3') end | _, _ => TrF r1 r2 r3 end end.
Fixpoint stepnorth (b : Board) : Board := match b with | R l1 (R l2 (K l3 b')) => match Tristep' l3 l2 l1 with | TrS l3' l2' l1' => R l1' (K l2' (R l3' b')) | TrF l3' l2' l1' => R l1' (R l2' (K l3' b')) end | R r b' => R r (stepnorth b') | _ => b end.
Fixpoint stepeast (b : Board) : Board := match b with | K r b' => K (rowstepeast r) b' | R r b' => R r (stepeast b') | Nothing => Nothing end.
Fixpoint stepsouth (b : Board) : Board := match b with | R r b' => R r (stepsouth b') | K l1 (R l2 (R l3 b')) => match Tristep' l1 l2 l3 with | TrS l1' l2' l3' => R l1' (K l2' (R l3' b')) | TrF l1' l2' l3' => K l1' (R l2' (R l3' b')) end | _ => b end.
Fixpoint stepwest (b : Board) : Board := match b with | K r b' => K (rowstepwest r) b' | R r b' => R r (stepwest b') | Nothing => Nothing end.
Definition dostep (r : Direction) (b : Board) : Board := match r with | No => stepnorth b | Ea => stepeast b | So => stepsouth b | We => stepwest b end.
Inductive solvable : Board -> Prop := | OK : forall b : Board, ready b -> solvable b | STEP : forall (b : Board) (d : Direction), solvable (dostep d b) -> solvable b.
Ltac n := apply STEP with No; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac e := apply STEP with Ea; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac s := apply STEP with So; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac w := apply STEP with We; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Notation "'_' a" := (C Empty a) (at level 0, right associativity).
Notation "# a" := (C Wall a) (at level 0, right associativity).
Notation "+ a" := (C Keeper a) (at level 0, right associativity).
Notation "'X' a" := (C Box a) (at level 0, right associativity).
Notation "'O' a" := (C Dest a) (at level 0, right associativity).
Notation "* a" := (C Full a) (at level 0, right associativity).
Notation "'o' a" := (C KeepOD a) (at level 0, right associativity).
Notation "<|" := Nil (at level 0).
Notation "|> a b" := (R a b) (format "'[v' |> a '/' b ']'", at level 0, a, b at level 0).
Notation "+> a b" := (K a b) (format "'[v' +> a '/' b ']'", at level 0, a, b at level 0).
Notation "|><|" := Nothing (format "|><| '//'", at level 0).
Definition b := |> # # # # # # # <| |> # _ _ _ _ _ # <| +> # _ + X _ _ # <| (* Note: the row containing the keeper (+) must be indicated *) |> # _ _ _ _ _ # <| (* by +> instead of |> (constructor K instead of R) *) |> # _ _ _ _ O # <| |> # # # # # # # <| |><| .
Goal solvable b.
unfold b in |- *.
apply STEP with Ea.
unfold dostep in |- *.
unfold stepeast in |- *.
unfold rowstepeast in |- *.
unfold move in |- *.
apply STEP with Ea.
simpl in |- *.
n.
n.
e.
s.
s.
Save solution'_b.
Print solution'_b.
Definition microban_1 := |> # # # # <| |> # _ O # <| |> # _ _ # # # <| +> # * + _ _ # <| |> # _ _ X _ # <| |> # _ _ # # # <| |> # # # # <| |><| .
Goal solvable microban_1.
unfold microban_1 in |- *.
s.
w.
n.
e.
e.
e.
s.
w.
n.
w.
w.
s.
s.
e.
n.
w.
n.
e.
n.
n.
w.
s.
e.
s.
s.
e.
e.
n.
w.
s.
w.
n.
n.
Save microban_1_solution.
Print microban_1_solution.
Definition microban_2 := |> # # # # # # <| |> # _ _ _ _ # <| +> # _ # + _ # <| |> # _ X * (* The amount of whitespace doesn't matter in creating the boards *) _ (* as long as it's there in the proper places *) # <| |> # _ O * _ # <| |> # _ _ _ _ # <| |> # # # # # # <| |><| .
Print microban_2.
Goal solvable microban_2.
unfold microban_2 in |- *.
Abort.

Goal solvable microban_2.
unfold microban_2 in |- *.
