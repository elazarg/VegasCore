/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnDisclosure
import Vegas.Game.OnePacketBindingSite
import Vegas.Game.OnePacketRetention

/-! # Genuine debt-free main responses transmit successful canonical calls -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol Interaction EventGraphRuntime
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- Actual own debt-freeness rules out the guard obstruction to canonical
openings; actual one-packet histories provide fresh binding slots. -/
theorem canonicalTransmitsAt_of_debtFree (wellFormed : setup.WellFormed)
    {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (forced : ForcedState setup timeouts leaks who (some control))
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup timeouts leaks who (some (control.execution.logs who,
      control.execution.observe (application setup timeouts leaks) who)) = some event) :
    CanonicalTransmitsAt setup timeouts leaks who (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who) event := by
  have owned := (pendingEvent_spec (timeouts := timeouts) pending).2.2.1
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have noActor := nodeView_sample_actor outputEq codeEq
      rw [owned] at noActor
      cases noActor
  | bind owner payload outputEq codeEq =>
      have same : owner = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst owner
      intro sourceAction graphAction encoded commitsValue _
      obtain ⟨value, actionEq⟩ := encodeEventAction?_commitsValue setup.program event sourceAction
        commitsValue graphAction encoded who payload outputEq
      rw [actionEq]
      have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup)
        horizon scheduler trace
      have readyView := (pendingEvent_spec (timeouts := timeouts) pending).2.1
      have ready := (control.execution.application.publicView_eventReady event).mp readyView
      have facts := legalFacts setup leaks horizon scheduler _ rawTrace
      have active := control.execution.application.active_of_ready_owned facts.quiescent ready owned
      obtain ⟨serial, selected⟩ := onePacket_canonicalFreshSlot_exists (timeouts := timeouts)
        trace who
      rw [(canonicalServiceDecision_binding timeouts) leaks who (control.execution.logs who)
        (control.execution.observe (application setup timeouts leaks) who) event payload outputEq
        codeEq node active serial selected (.success value)]
      exact Option.some_ne_none _
  | resolve owner payload binding checks outputEq codeEq =>
      have same : owner = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst owner
      have resolves := disclosureResolves_of_debtFree (timeouts := timeouts) wellFormed trace who
        forced notOwed
      exact canonicalTransmitsAt_of_disclosureResolves resolves pending node

/-- A sampled source-main response is an actual transmitting canonical call at a
forced debt-free prefix, with a successful binding action if the event binds.
This derives transmission from the runtime guard/debt invariant. -/
theorem honestResponse_canonical_of_debtFree (wellFormed : setup.WellFormed)
    (source : setup.intendedModel.BehavioralAssessment)
    {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (forced : ForcedState setup timeouts leaks who (some control))
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup timeouts leaks who (some (control.execution.logs who,
      control.execution.observe (application setup timeouts leaks) who)) = some event)
    (response : (application setup timeouts leaks).Action)
    (supported : response ∈ (honestResponse setup timeouts leaks source who
      (control.execution.logs who)
      (control.execution.observe (application setup timeouts leaks) who)).support) :
    ∃ (action : (graph setup).Action event) (material : (application setup timeouts
      leaks).Submission),
      response = (canonicalServiceDecision timeouts) leaks who (control.execution.logs who)
        (control.execution.observe (application setup timeouts leaks) who) event action ∧
      response.transmission = some material ∧
      ∀ owner payload outputEq codeEq,
        nodeView (graph setup) event = .bind owner payload outputEq codeEq →
          ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
            Option (PublicationResult (L.Val payload))) = some (.success value) := by
  have transmits := canonicalTransmitsAt_of_debtFree (timeouts := timeouts) wellFormed trace who
    forced notOwed event
    pending
  have turn := (pendingEvent_spec (timeouts := timeouts) pending).1
  obtain ⟨rank, point, ordered, decoded, _⟩ := forced
  unfold honestResponse at supported
  rw [turn] at supported
  obtain ⟨sourceChoice, chosen, responseEq⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have ready := (control.execution.application.publicView_eventReady event).mp
    (pendingEvent_spec (timeouts := timeouts) pending).2.1
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  have active := control.execution.application.active_of_ready_owned facts.quiescent ready
    (pendingEvent_spec (timeouts := timeouts) pending).2.2.1
  have encodes := asIfHonestProfile_encodes (timeouts := timeouts) source who control.execution rank
    ordered point
    decoded (control.execution.logs who) event turn active sourceChoice chosen
  rcases sourceChoice with _ | sourceAction
  · simp at encodes
  cases encoded : encodeEventAction? setup.program event sourceAction with
  | none => simp [encoded] at encodes
  | some action =>
      have success := asIfHonestProfile_success (timeouts := timeouts) source who control.execution
        rank ordered
        point decoded (control.execution.logs who) sourceAction chosen
      have sends := transmits sourceAction action encoded success.1 success.2
      obtain ⟨material, submits⟩ := Option.ne_none_iff_exists'.mp sends
      have commits := success.1
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
    {control : (application setup timeouts leaks).Control}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (forced : ForcedState setup timeouts leaks who (some control))
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup timeouts leaks who (some (control.execution.logs who,
      control.execution.observe (application setup timeouts leaks) who)) = some event)
    (bound : (graph setup).EventId → Nat)
    (fits : control.execution.application.publicView.InclusionFitsDeadline timeouts bound
      event)
    (choice : (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      (some (control.execution.logs who,
        control.execution.observe (application setup timeouts leaks) who)))
    (supported : choice ∈ (honestChoice setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler
      source who (some (control.execution.logs who,
        control.execution.observe (application setup timeouts leaks) who))).support) :
    ∃ (action : (graph setup).Action event) (material : (application setup timeouts
      leaks).Submission),
      choice.1 = some ((canonicalServiceDecision timeouts) leaks who
        (control.execution.logs who) (control.execution.observe (application setup timeouts
          leaks) who)
        event action) ∧
      ((canonicalServiceDecision timeouts) leaks who (control.execution.logs who)
        (control.execution.observe (application setup timeouts leaks) who) event
          action).transmission =
          some material ∧
      ∀ owner payload outputEq codeEq,
        nodeView (graph setup) event = .bind owner payload outputEq codeEq →
          ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
            Option (PublicationResult (L.Val payload))) = some (.success value) := by
  classical
  obtain ⟨response, responded, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨action, material, responseEq, sends, bindSuccess⟩ :=
    honestResponse_canonical_of_debtFree (timeouts := timeouts) wellFormed source trace who forced
      notOwed event pending
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
  have spec := pendingEvent_spec (timeouts := timeouts) pending
  have retains : RetainsCoveredCanonical setup timeouts leaks bounds horizon scheduler bound :=
    retainsCoveredCanonical_of_adequate (timeouts := timeouts) bounds covers capacity horizon
      scheduler bound
  have member := canonical_mem_onePacket_of_pending (timeouts := timeouts) bounds trace who event
    spec.1 spec.2.2.2
    action (retains trace who event action spec.1 spec.2.2.2 fits effective (by rw [sends]; simp))
  refine ⟨action, material, ?_, sends, bindSuccess⟩
  unfold responseChoice
  simp only [member, ↓reduceDIte]

end Vegas
