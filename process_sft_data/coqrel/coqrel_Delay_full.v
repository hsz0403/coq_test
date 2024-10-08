Module Delay.
Ltac use_conjunction H := lazymatch type of H with | ?A /\ ?B => use_conjunction (@proj2 A B H) | _ => eapply (proj1 H) end.
Record open_conjunction (P: Prop) := { open_conjunction_proj: P }.
Ltac revert_until_conjunction Hdelayed := match goal with | |- open_conjunction _ -> _ => intro Hdelayed | H : _ |- _ => revert H; revert_until_conjunction Hdelayed end.
Definition delayed_goal (P: Prop) := P.
Definition unpack (P: Prop) := P.
Ltac split_conjunction := let handle_subgoal := intros; match goal with | |- delayed_goal _ => red | |- unpack _ => red; split_conjunction | |- _ => idtac end in match goal with | |- _ /\ _ => split; [handle_subgoal | split_conjunction] | |- True => exact I | |- ?P => is_evar P; exact I | |- _ => handle_subgoal end.
Ltac delay := idtac; lazymatch goal with | _ : open_conjunction ?P |- ?G => change (delayed_goal G); let Hdelayed := fresh "Hdelayed" in revert_until_conjunction Hdelayed; use_conjunction (open_conjunction_proj P Hdelayed) | _ => fail "delay can only be used under the 'delayed' tactical" end.
Ltac delayed_conjunction tac := let Pv := fresh in evar (Pv: Prop); let P := eval red in Pv in clear Pv; let Hdelayed := fresh "Hdelayed" in cut (open_conjunction P); [ intro Hdelayed; tac; clear Hdelayed | eapply Build_open_conjunction ].
Ltac delayed tac := delayed_conjunction tac; [ .. | split_conjunction ].
Ltac undelay := lazymatch goal with | Hdelayed : open_conjunction _ |- _ => clear Hdelayed end.
Ltac nondelayed tac := undelay; tac.
End Delay.
Tactic Notation "delayed" tactic1(tac) := Delay.delayed tac.
Tactic Notation "nondelayed" tactic1(tac) := Delay.nondelayed tac.
Tactic Notation "delayed_conjunction" tactic1(tac) := Delay.delayed_conjunction tac.
Tactic Notation "delay" := Delay.delay.
Definition delay (P: Prop) := P.
Hint Extern 0 (delay _) => delay : core.
Hint Extern 100 => delay : delay.
Class NonDelayed (P: Prop) := nondelayed : P.
Hint Extern 1 (NonDelayed _) => red; try Delay.undelay : typeclass_instances.
Class EApply (HT P Q: Prop) := eapply : HT -> P -> Q.
Hint Extern 1 (EApply ?HT _ _) => let H := fresh in let HP := fresh "HP" in intros H HP; delayed_conjunction solve [eapply H; delay]; eexact HP : typeclass_instances.