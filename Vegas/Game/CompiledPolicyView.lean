/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketForced
import Vegas.Compile.EventGraphBacktranslation

/-! # Compiled decisions read the decoded source view

The compiled policy table of a source policy at an event of its owner walks
the program exactly as the view decoder does at the event's rank. Wherever the
view decoder succeeds there, the compiled law, as a law of encoded actions, is
the policy's source action law at the decoded view, each action encoded at the
event (`Vegas.compilePolicyTable_eq_protocolAction`).
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **The compiled decision is the source decision at the decoded view.** At
an event owned by `who`, wherever the view decoder succeeds at the event's
rank, the compiled policy table gives the law of the source action law at the
decoded view, each action encoded at the event. -/
theorem compilePolicyTable_eq_protocolAction {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} (who : Player) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (policy : BehavioralPolicy who program) (event : Fin (eventCount program))
      (store : EventGraph.Store layout) (history : List (OwnAction Player L))
      (view : ProtocolView who program),
      eventOwner? program event = some who →
      decodeViewPrefix? who program refs outputs event.val store history = some view →
      (compilePolicyTable program refs outputs who policy event store history).map some =
        (policy.protocolAction program view).map
          (fun choice => choice.bind (encodeEventAction? program event))
  | _, _, .ret _, _, _, _, event, _, _, _, _, _ => nomatch event
  | _, _, .sample name fresh law next, refs, outputs, policy, event, store, history, view,
      owned, decoded => by
      cases event using Fin.cases with
      | zero => cases owned
      | succ tail =>
          change decodeViewPrefix? who (.sample name fresh law next) refs outputs
            (tail.val + 1) store history = some view at decoded
          simp only [decodeViewPrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact compilePolicyTable_eq_protocolAction who next _ _ policy tail store history rest
            owned restDecoded
  | _, _, .commit name owner fresh guard next, refs, outputs, policy, event, store, history,
      view, owned, decoded => by
      cases event using Fin.cases with
      | zero =>
          have ownerEq : owner = who := Option.some.inj owned
          subst ownerEq
          change (decodeObservation? owner refs store).map
            (fun observation => ProtocolView.entry owner (.commit name owner fresh guard next)
              (observation, history)) = some view at decoded
          obtain ⟨observation, observed, rfl⟩ := Option.map_eq_some_iff.mp decoded
          change ((if same : owner = owner then
              match decodeObservation? owner refs store with
              | some observation => policy.1 same (observation, history)
              | none => PMF.pure PublicationResult.failure
            else PMF.pure PublicationResult.failure)).map some = _
          simp only [dite_true, observed, BehavioralPolicy.protocolAction, ProtocolView.entry,
            Sum.elim_inl, PMF.map_comp]
          congr 1
          funext choice
          simp [encodeEventAction?]
      | succ tail =>
          change decodeViewPrefix? who (.commit name owner fresh guard next) refs outputs
            (tail.val + 1) store history = some view at decoded
          simp only [decodeViewPrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact compilePolicyTable_eq_protocolAction who next _ _ policy.2 tail store history
            rest owned restDecoded
  | _, _, .reveal published owner name fresh selected unresolved next, refs, outputs, policy,
      event, store, history, view, owned, decoded => by
      cases event using Fin.cases with
      | zero =>
          have ownerEq : owner = who := Option.some.inj owned
          subst ownerEq
          change (decodeObservation? owner refs store).map
            (fun observation => ProtocolView.entry owner
              (.reveal published owner name fresh selected unresolved next)
              (observation, history)) = some view at decoded
          obtain ⟨observation, observed, rfl⟩ := Option.map_eq_some_iff.mp decoded
          change ((if same : owner = owner then
              match decodeObservation? owner refs store with
              | some observation => policy.1 same (observation, history)
              | none => PMF.pure true
            else PMF.pure false)).map some = _
          simp only [dite_true, observed, BehavioralPolicy.protocolAction, ProtocolView.entry,
            Sum.elim_inl, PMF.map_comp]
          congr 1
          funext choice
          simp [encodeEventAction?]
      | succ tail =>
          change decodeViewPrefix? who (.reveal published owner name fresh selected unresolved
            next) refs outputs (tail.val + 1) store history = some view at decoded
          simp only [decodeViewPrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact compilePolicyTable_eq_protocolAction who next _ _ policy.2 tail store history
            rest owned restDecoded

end Vegas
