/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketPrescribedSites

/-! # Genuine debt-free main responses transmit successful canonical calls -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol Interaction EventGraphRuntime
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- Actual own debt-freeness rules out the guard obstruction to canonical
openings; actual one-packet histories provide fresh binding slots. -/
theorem canonicalTransmitsAt_of_debtFree (wellFormed : setup.WellFormed)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (forced : ForcedState setup leaks who (some control))
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (control.execution.recall who,
      control.execution.observe (application setup leaks) who)) = some event) :
    CanonicalTransmitsAt setup leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event := by
  have owned := (pendingEvent_spec pending).2.2.1
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have noActor := nodeView_sample_actor outputEq codeEq
      rw [owned] at noActor
      cases noActor
  | bind owner payload outputEq codeEq =>
      have same : owner = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst owner
      exact canonicalTransmitsAt_of_binding trace who event node
  | resolve owner payload binding checks outputEq codeEq =>
      have same : owner = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst owner
      have resolves := disclosureResolves_of_debtFree wellFormed trace who forced notOwed
      exact canonicalTransmitsAt_of_disclosureResolves setup leaks resolves pending node

/-- A sampled source-main response is an actual transmitting canonical call at a
forced debt-free prefix, with a successful binding action if the event binds.
This derives transmission from the runtime guard/debt invariant. -/
theorem honestResponse_canonical_of_debtFree (wellFormed : setup.WellFormed)
    (source : setup.intendedModel.BehavioralAssessment)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (forced : ForcedState setup leaks who (some control))
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (control.execution.recall who,
      control.execution.observe (application setup leaks) who)) = some event)
    (response : (application setup leaks).Action)
    (supported : response ∈ (honestResponse setup leaks source who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support) :
    ∃ (action : (graph setup).Action event) (material : (application setup leaks).Submission),
      response = (runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event action ∧
      response.transmission = some material ∧
      ∀ owner payload outputEq codeEq,
        nodeView (graph setup) event = .bind owner payload outputEq codeEq →
          ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
            PublicationResult (L.Val payload)) = .success value := by
  have transmits := canonicalTransmitsAt_of_debtFree wellFormed trace who forced notOwed event
    pending
  have turn := (pendingEvent_spec pending).1
  obtain ⟨rank, point, ordered, decoded, _⟩ := forced
  unfold honestResponse at supported
  rw [turn] at supported
  obtain ⟨sourceChoice, chosen, responseEq⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have encodes := asIfHonestProfile_encodes source who control.execution rank ordered point
    decoded (control.execution.recall who) event turn sourceChoice chosen
  rcases sourceChoice with _ | sourceAction
  · simp at encodes
  cases encoded : encodeEventAction? setup.program event sourceAction with
  | none => simp [encoded] at encodes
  | some action =>
      have success := asIfHonestProfile_success source who control.execution rank ordered
        point decoded (control.execution.recall who) sourceAction chosen
      have sends := transmits sourceAction action encoded success.1 success.2
      obtain ⟨material, submits⟩ := Option.ne_none_iff_exists'.mp sends
      have commits : sourceAction.CommitsValue := by
        cases sourceAction with
        | commit owner name payload result =>
            cases result with
            | failure => exact (success.1 owner name payload rfl).elim
            | success value => exact ⟨value, rfl⟩
        | reveal => trivial
      simp only [Option.bind_some, encoded] at responseEq
      subst responseEq
      refine ⟨action, material, rfl, submits, ?_⟩
      intro owner payload outputEq _codeEq _node
      obtain ⟨value, rfl⟩ := encodeEventAction?_commitsValue setup.program event sourceAction
        commits action encoded owner payload outputEq
      exact ⟨value, by simp⟩

/-- Adequate menus retain the actual main response at a timely pending input.
Consequently choice normalization cannot turn that main response into silence. -/
theorem honestChoice_canonical_of_debtFree (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (forced : ForcedState setup leaks who (some control))
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (control.execution.recall who,
      control.execution.observe (application setup leaks) who)) = some event)
    (bound : (graph setup).EventId → Nat)
    (fits : control.execution.application.publicView.InclusionFitsDeadline (runtime setup) bound
      event)
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who)))
    (supported : choice ∈ (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler
      source who (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))).support) :
    ∃ (action : (graph setup).Action event) (material : (application setup leaks).Submission),
      choice.1 = some ((runtime setup).canonicalServiceDecision leaks who
        (control.execution.recall who) (control.execution.observe (application setup leaks) who)
        event action) ∧
      ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event action).transmission =
          some material ∧
      ∀ owner payload outputEq codeEq,
        nodeView (graph setup) event = .bind owner payload outputEq codeEq →
          ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
            PublicationResult (L.Val payload)) = .success value := by
  classical
  obtain ⟨response, responded, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨action, material, responseEq, sends, bindSuccess⟩ :=
    honestResponse_canonical_of_debtFree wellFormed source trace who forced notOwed event pending
      response responded
  subst responseEq
  have effective : EffectiveDecision event action := by
    unfold EffectiveDecision
    cases node : nodeView (graph setup) event with
    | bind owner payload outputEq codeEq =>
        obtain ⟨value, successful⟩ := bindSuccess owner payload outputEq codeEq node
        refine ⟨value, ?_⟩
        rw [← successful]
        simp
    | resolve | sample => trivial
  have spec := pendingEvent_spec pending
  have retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound :=
    retainsCoveredCanonical_of_adequate bounds covers capacity horizon scheduler bound
  have member := canonical_mem_onePacket_of_pending bounds trace who event spec.1 spec.2.2.2
    action (retains trace who event action spec.1 spec.2.2.2 fits effective (by rw [sends]; simp))
  refine ⟨action, material, ?_, sends, bindSuccess⟩
  unfold responseChoice
  simp only [member, ↓reduceDIte]

end Vegas
