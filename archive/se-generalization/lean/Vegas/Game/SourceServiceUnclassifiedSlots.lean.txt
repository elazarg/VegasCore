/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceUnusableBinding

/-! # Counted registrations before a classified response exit

An effective unclassified response uses no commitment, or makes the first
bare commitment at the current owned binding with its fresh counted handle.
This shape and its slot preservation do not depend on a protection gate or a
clear persistent risk flag. Private Option-Raw material remains arbitrary.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Outside the actual packet and recorded-response exits, every commitment
is a first fresh counted binding at the actual owned ready turn. The actual
material may be missing or mistyped; the conclusion makes no value claim. -/
theorem unclassifiedResponse_registration
    (bounds : MessageBounds (graph setup))
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (slots : CanonicalSlotsUsed setup leaks execution who)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who (execution.recall who)
      (execution.observe (application setup leaks) who))
    (notPacket : ¬ auditableServiceResponse setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) response)
    (notRecorded : ¬ recordedServiceResponse setup leaks (execution.recall who) response) :
    (∀ material, response.transmission = some material →
      ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
      ∃ (event : (graph setup).EventId) (payload : L.Ty),
        (graph setup).outputLayout event = .binding who payload ∧
        execution.application.publicView.ownTurn? who = some event ∧
        execution.application.candidates.lookup
          (who, .prepared (execution.application.publicView.bindingCount who)) = .fresh ∧
        ∃ opening, response = ⟨some ⟨⟨.commitment event
          (who, .prepared (execution.application.publicView.bindingCount who)), opening⟩,
            .none⟩⟩ := by
  classical
  by_cases noncommitment : ∀ material, response.transmission = some material →
      ∀ event candidate, material.call.packet ≠ .commitment event candidate
  · exact Or.inl noncommitment
  push Not at noncommitment
  obtain ⟨material, transmitted, event, candidate, called⟩ := noncommitment
  have responseEq : response = ⟨some material⟩ := by
    cases response with
    | mk actual => cases transmitted; rfl
  rw [responseEq] at effective notPacket notRecorded
  obtain ⟨namedEvent, named, owned, _ready, turn, _unrecorded⟩ :=
    unclassifiedSubmission_ready execution who trace material notPacket notRecorded
  rw [called] at named
  cases Option.some.inj named
  have compatible : material.call.packet.MatchesNode := by
    by_contra incompatible
    apply notPacket
    refine ⟨material, rfl, ?_⟩
    rw [localServiceEnvelope_actual setup leaks trace who material]
    exact Or.inr (Or.inr (Or.inl incompatible))
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      rw [nodeView_sample_actor outputEq codeEq] at owned
      cases owned
  | resolve actor payload binding checks outputEq codeEq =>
      simp only [Payload.MatchesNode, called, node] at compatible
  | bind actor payload outputEq codeEq =>
      have sameActor := nodeView_bind_actor outputEq codeEq
      rw [owned] at sameActor
      cases Option.some.inj sameActor
      have shape := unclassifiedBinding_shape bounds execution who trace atTurn slots event
        payload outputEq codeEq node turn material effective notPacket notRecorded
      exact Or.inr ⟨event, payload, outputEq, turn, shape.2.1, material.call.opening,
        responseEq.trans (congrArg (fun material =>
          (⟨some material⟩ : (application setup leaks).Action)) shape.1)⟩

/-- The actual copied unclassified response preserves the unconditional
owner slot and turn invariant. This remains useful after opportunity risk
latches, where the previous conditional-clear resource no longer supplies it. -/
theorem sourceServiceUnclassified_response_slots
    (bounds : MessageBounds (graph setup))
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (slots : CanonicalSlotsUsed setup leaks execution who)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who (execution.recall who)
      (execution.observe (application setup leaks) who))
    (notPacket : ¬ auditableServiceResponse setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) response)
    (notRecorded : ¬ recordedServiceResponse setup leaks (execution.recall who) response) :
    OwnSubmissionsAtTurn setup leaks
        (execution.respond (application setup leaks) who response) who ∧
      CanonicalSlotsUsed setup leaks
        (execution.respond (application setup leaks) who response) who := by
  classical
  constructor
  · apply ownSubmissionsAtTurn_respond_current execution who response atTurn
    intro event submitted
    obtain ⟨material, transmitted⟩ : ∃ material, response.transmission = some material := by
      cases sent : response.transmission with
      | none => simp only [submittedEvent?, sent] at submitted; cases submitted
      | some material => exact ⟨material, rfl⟩
    have responseEq : response = ⟨some material⟩ := by
      cases response with
      | mk actual => cases transmitted; rfl
    rw [responseEq] at notPacket notRecorded submitted
    obtain ⟨namedEvent, named, _owned, _ready, turn, _unrecorded⟩ :=
      unclassifiedSubmission_ready execution who trace material notPacket notRecorded
    have same : namedEvent = event := Option.some.inj (named.symm.trans submitted)
    rwa [same] at turn
  · apply canonicalSlotsUsed_respond_counted execution who response slots
    intro serial slot
    rcases unclassifiedResponse_registration bounds execution who trace atTurn slots response
        effective notPacket notRecorded with noncommitment |
      ⟨event, payload, layout, turn, _fresh, opening, responseEq⟩
    · unfold responseCandidateSlot at slot
      cases sent : response.transmission with
      | none => simp only [sent, reduceCtorEq] at slot
      | some material =>
          simp only [sent] at slot
          cases called : material.call.packet <;>
            simp only [Payload.preparedCommitment?, called, reduceCtorEq] at slot
          exact (noncommitment material sent _ _ called).elim
    · rw [responseEq] at slot
      change some (execution.application.publicView.bindingCount who) = some serial at slot
      cases Option.some.inj slot
      have ready := (execution.application.publicView_eventReady event).mp
        (PublicView.ownTurn?_spec _ who event turn).1
      exact ⟨event, payload, layout, rfl, ready.1, by rw [responseEq]; rfl⟩

end Vegas
