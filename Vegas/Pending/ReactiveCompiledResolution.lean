/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactivePolicyFacts

/-! # Authentic prescribed resolution responses

A prescribed disclosure sends the stored successful binding and its accepted
owned handle, with normalized evidence. The handler evaluates the public guards;
authentic transmission does not assert that the publication succeeds. Withholding,
defaulted owners and unavailable opening material produce silence.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A resolution sends silence or an opening of a stored successful binding at
its accepted owned handle. Its evidence representation is left explicit. -/
theorem serviceDecision_resolution_cases
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (choice : Bool) :
    let response := (serviceDecision timeouts) leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) choice)
    response = ⟨none⟩ ∨ ∃ candidate value evidence,
      binding.get? view.application.observation.store = some (.success value) ∧
      view.application.publicView.accepted binding.field = some candidate ∧
      candidate.1 = who ∧
      response =
        ⟨some ⟨⟨.opening event candidate ⟨payload, value⟩, none⟩, evidence⟩⟩ := by
  let action := cast (congrArg EventField.Action outputEq.symm) choice
  by_cases inactive : who ∈ view.application.publicView.observation.defaulted
  · left
    simp only [serviceDecision, reactiveDecision, ite_eq_left inactive]
    rfl
  have shape : reactiveResolutionPacket who event payload binding checks outputEq action
      view.application = none ∨
      ∃ candidate value, binding.get? view.application.observation.store = some (.success value) ∧
        view.application.publicView.accepted binding.field = some candidate ∧
        candidate.1 = who ∧
        reactiveResolutionPacket who event payload binding checks outputEq action
          view.application = some (.opening event candidate ⟨payload, value⟩) := by
    rcases reactiveResolutionPacket_shape who event payload binding checks outputEq action
      view.application with ⟨candidate, raw, packet⟩ | silent
    · obtain ⟨_active, _discloses, _named, value, stored, associated, owned, rawEq⟩ :=
        reactiveResolutionPacket_opening_spec who event payload binding checks outputEq action
          view.application event candidate raw packet
      subst raw
      exact Or.inr ⟨candidate, value, stored, associated, owned, packet⟩
    · exact Or.inl silent
  change (serviceDecision timeouts) leaks who past view event action = _ ∨ _
  rcases shape with withheld | ⟨candidate, value, result, associated, owned, packet⟩
  · left
    simp only [serviceDecision, reactiveDecision, ite_eq_right inactive, node, withheld,
      Option.map_none]
    rfl
  · let first := WitnessedSubmission.normalizeReactive who view.application []
      (disclosureSubmission (.opening event candidate ⟨payload, value⟩))
    let evidence := (first.normalizeReactive who view.application
        (ReactiveApplication.ResponseMenu.knownPackets past view)).evidence
    refine Or.inr ⟨candidate, value, evidence, result, associated, owned, ?_⟩
    change (serviceDecision timeouts) leaks who past view event action = _
    simp only [serviceDecision, reactiveDecision, ite_eq_right inactive, node, packet,
      Option.map_some,
      disclosureSubmission, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none]
    simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      evidence, first, disclosureSubmission, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none]


end Vegas.EventGraphRuntime
