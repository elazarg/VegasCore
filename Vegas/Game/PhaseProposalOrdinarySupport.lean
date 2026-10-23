/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOrdinaryDomination
import Vegas.Game.PhaseProposalBindingSupport
import Vegas.Game.PhaseProposalQueryDomain
import Vegas.Pending.PhaseProposalBindingSlots
import Vegas.Pending.PhaseProposalCanonicalBinding

/-! # Usable counted bindings have positive ordinary-only mass -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

/-- A usable actual counted binding alias is supported by the fixed-table
ordinary-only comparison. A successful semantic guard is not required: this
statement concerns preparation at the event's declared type. -/
theorem phaseProposalOrdinaryBindingResponses_supported
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (rates : PhaseProposalRates) (waitBelow : rates.waiting.val < 1)
    (slots : 0 < rates.slots.val) (aliases : 0 < rates.aliases.val)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest (serviceGraph setup mode))
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (execution.recall owner) (execution.observe app owner))
    (value : L.Val payload)
    (usable : opening.bind (fun raw => raw.as? payload) = some value) :
    (⟨⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩, member⟩ :
      PhaseProposal.Response runtime leaks bounds owner (execution.recall owner)
        (execution.observe app owner)) ∈
      (phaseProposalOrdinaryResponses setup mode runtime leaks bounds plan values rates owner
        (execution.recall owner) (execution.observe app owner)).support := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  have counted : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler counted)
  let past := execution.recall owner
  let view := execution.observe app owner
  have base : phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates.ordinary
      owner past view = mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
        (PMF.pure ⟨none⟩) (PhaseCount.bindingResultEncoder runtime leaks bounds owner event payload
          (phaseProposalBindingResults setup mode runtime leaks plan values rates.ordinary owner
            event payload binding) rates.slots.val rates.slots.property.1 rates.slots.property.2
          past view) := by
    unfold phaseProposalBasePolicy
    exact phasePolicyDispatch_binding setup mode runtime leaks _ _ execution native owner event
      payload binding request
  have bounded := covered event
  rw [binding] at bounded
  have slot := PhaseProposal.binding_slot_of_counted_response runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining owner
      execution counted event payload binding request serial opening evidence member bounded
  have canonicalMember := (Finset.mem_filter.mp slot).2.2 (PublicationResult.success value)
  have same := PhaseProposal.responseClass_binding runtime leaks bounds owner past view event
    payload binding serial opening evidence member (by simpa only [usable, Option.elim_some]
      using canonicalMember)
  have projected : PhaseProposal.projectResponse runtime leaks bounds owner past view
      ⟨⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩, member⟩ =
      PhaseProposal.projectResponse runtime leaks bounds owner past view
        ⟨phaseBindingResponse runtime leaks owner event payload (.success value) serial,
          canonicalMember⟩ := by
    apply Subtype.ext
    simpa only [PhaseProposal.projectResponse, usable, Option.elim_some] using same
  obtain ⟨key, queried, nativeValues⟩ := phaseProposalDomainValues_fullSupport_of_binding setup mode
    runtime leaks complete plan maximal values fullValues horizon scheduler raw owner rfl event
      payload binding request
  have resultSupported : PublicationResult.success value ∈
      (phaseProposalBindingResults setup mode runtime leaks plan values rates.ordinary owner event
        payload binding past view).support := by
    unfold phaseProposalBindingResults
    rw [queried]
    simp only [PhaseProposalRates.ordinary, mix_zero]
    obtain ⟨choice, selected, typed⟩ := (PMF.mem_support_map_iff _ _ _).mp (nativeValues value)
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨choice, selected, congrArg PublicationResult.success
      typed⟩
  apply phaseProposalOrdinaryResponses_mem_of_class setup mode runtime leaks bounds plan values
    rates aliases owner past view
  rw [projected]
  apply phaseProposalBaseClasses_mem_of_response setup mode runtime leaks bounds plan values
    rates.ordinary owner past view ⟨_, canonicalMember⟩
  rw [base]
  apply mem_support_mix_right _ _ _ waitBelow
  apply mem_support_mix_left _ _ _ slots
  have nonempty : (PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload past
      view).Nonempty := ⟨serial, slot⟩
  rw [PhaseCount.phaseBindingSlotPolicy, dite_eq_left nonempty]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨serial,
    (PMF.mem_support_uniformOfFinset_iff ..).mpr slot,
    (PMF.mem_support_map_iff _ _ _).mpr ⟨.success value, resultSupported, rfl⟩⟩

end Vegas
