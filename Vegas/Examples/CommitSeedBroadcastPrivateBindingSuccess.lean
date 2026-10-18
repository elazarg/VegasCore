/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalBindingWord
import Vegas.Examples.CommitSeedBroadcastTailBindingWord

/-! # Exact event-private counted binding success for the concrete seed family -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem binding_layout_coordinate (event : graph.EventId) (owner : Player)
    (payload : simpleExpr.Ty) (binding : graph.outputLayout event = .binding owner payload) :
    event = bindingEvent owner ∧ payload = .bool := by
  fin_cases event
  · change (EventField.binding alice .bool : EventField Player simpleExpr) =
      .binding owner payload at binding
    obtain ⟨sameOwner, samePayload⟩ := EventField.binding.inj binding
    subst owner
    subst payload
    exact ⟨rfl, rfl⟩
  · change (EventField.binding bob .bool : EventField Player simpleExpr) =
      .binding owner payload at binding
    obtain ⟨sameOwner, samePayload⟩ := EventField.binding.inj binding
    subst owner
    subst payload
    exact ⟨rfl, rfl⟩
  · change (EventField.binding carol .bool : EventField Player simpleExpr) =
      .binding owner payload at binding
    obtain ⟨sameOwner, samePayload⟩ := EventField.binding.inj binding
    subst owner
    subst payload
    exact ⟨rfl, rfl⟩
  · change (EventField.publication .bool : EventField Player simpleExpr) =
      .binding owner payload at binding
    cases binding
  · change (EventField.publication .bool : EventField Player simpleExpr) =
      .binding owner payload at binding
    cases binding
  · change (EventField.publication .bool : EventField Player simpleExpr) =
      .binding owner payload at binding
    cases binding

/-- On every pair of genuine resolved counted histories, binding success depends
only on the original coordinate seed and relative emission-clock word. The
histories may differ in private preparation, handles, evidence, foreign traffic,
retired attempts, reset choices and all other original scheduler seeds. -/
theorem family_privateBindingSuccess :
    PhaseService.PrivateBindingSuccess runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon addressedSeedLaw addressedFamily := by
  unfold PhaseService.PrivateBindingSuccess
  rw [← initial_eq_compiled]
  intro firstSeeds _firstSupport secondSeeds _secondSupport first second firstTrace secondTrace
    coordinate owner payload binding firstResolved secondResolved sameSeed sameClocks
  let firstCore := addressedSeedCore firstSeeds
  let secondCore := addressedSeedCore secondSeeds
  change (countedMenu.protocol initial horizon (family firstCore)).Trace (some first)
    at firstTrace
  change (countedMenu.protocol initial horizon (family secondCore)).Trace (some second)
    at secondTrace
  obtain ⟨eventEq, payloadEq⟩ := binding_layout_coordinate coordinate.1.event owner payload binding
  subst payload
  by_cases original : coordinate.1.attempt = originalAttempt
  · have coordinateEq : coordinate.1 = originalCoordinate owner := by
      rcases coordinate with ⟨⟨attempt, event⟩, _bounded⟩
      change attempt = originalAttempt at original
      change event = bindingEvent owner at eventEq
      cases original
      cases eventEq
      rfl
    have addressEq : coordinate = originalAddress owner := Subtype.ext coordinateEq
    rw [coordinateEq] at firstResolved secondResolved sameClocks ⊢
    rw [addressEq] at sameSeed
    have firstLaw := original_binding_accepted_iff_clocks firstCore first firstTrace owner
      firstResolved
    have secondLaw := original_binding_accepted_iff_clocks secondCore second secondTrace owner
      secondResolved
    have ownBit : firstCore.2 owner = secondCore.2 owner := sameSeed
    rw [firstLaw, secondLaw, ownBit, sameClocks]
  · have firstLaw := tail_binding_accepted_iff_emitted firstCore first firstTrace coordinate.1
      owner original binding firstResolved
    have secondLaw := tail_binding_accepted_iff_emitted secondCore second secondTrace coordinate.1
      owner original binding secondResolved
    rw [firstLaw, secondLaw, sameClocks]

end Vegas.Examples.CommitSeedBroadcast
