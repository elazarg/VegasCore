/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingOriginalBindingWord
import Vegas.Examples.CommitSeedSignallingTailBindingWord

/-! # Exact event-private counted binding success for the concrete seed family -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

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
      (setup.initialLaw.map encodeInputs) horizon seedPrior family := by
  intro firstSeeds _firstSupport secondSeeds _secondSupport first second firstTrace secondTrace
    coordinate owner payload binding firstResolved secondResolved sameSeed sameClocks
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
    have firstLaw := original_binding_accepted_iff_clocks firstSeeds first firstTrace owner
      firstResolved
    have secondLaw := original_binding_accepted_iff_clocks secondSeeds second secondTrace owner
      secondResolved
    rw [firstLaw, secondLaw, sameSeed, sameClocks]
  · have firstLaw := tail_binding_accepted_iff_emitted firstSeeds first firstTrace coordinate.1
      owner original binding firstResolved
    have secondLaw := tail_binding_accepted_iff_emitted secondSeeds second secondTrace coordinate.1
      owner original binding secondResolved
    rw [firstLaw, secondLaw, sameClocks]

end Vegas.Examples.CommitSeedSignalling
