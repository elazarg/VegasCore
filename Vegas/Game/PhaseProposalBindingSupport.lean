/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalReference
import Vegas.Pending.PhaseProposalCanonicalBinding
import Vegas.Pending.PhaseProposalBindingSlots
import Vegas.Pending.PhaseNativeInvariant

/-! # Genuine binding menus exhaust the reference packet classes -/

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

/-- Attaching the actual menu witness and projecting a supported response
preserves support. This is not a history or posterior existence premise. -/
theorem phaseProposalBaseClasses_mem_of_response
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) (response : PhaseProposal.Response runtime leaks bounds who past view)
    (supported : response.val ∈
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates who
        past view).support) :
    PhaseProposal.projectResponse runtime leaks bounds who past view response ∈
      (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates who
        past view).support := by
  rw [← phaseProposalBaseResponses_map_val setup mode runtime leaks bounds plan values rates who
    past view] at supported
  obtain ⟨attached, positive, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have attachedEq : attached = response := Subtype.ext same
  subst attached
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨response, positive, rfl⟩

/-- Every allowed binding slot/preparation class appears in the actual BASE
law. Genuine shape/freshness/count facts discharge the slot and encoding
guards, including at off-path histories after earlier failures. -/
theorem phaseProposalBindingClasses_fullSupport
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (boundedValues : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (resultsFull : FullSupport (phaseProposalBindingResults setup mode runtime leaks plan values
      rates owner event payload binding (execution.recall owner) (execution.observe app owner))) :
    FullSupport (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates owner
      (execution.recall owner) (execution.observe app owner)) := by
  classical
  let past := execution.recall owner
  let view := execution.observe app owner
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  have base : phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates owner
      past view = mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
        (PMF.pure ⟨none⟩)
        (PhaseCount.bindingResultEncoder runtime leaks bounds owner event payload
          (phaseProposalBindingResults setup mode runtime leaks plan values rates owner event
            payload binding) rates.slots.val rates.slots.property.1 rates.slots.property.2
          past view) := by
    unfold phaseProposalBasePolicy
    exact phasePolicyDispatch_binding setup mode runtime leaks _ _ execution native
      owner event payload binding request
  intro chosen
  obtain ⟨response, projects⟩ := chosen.property
  have classEq : PhaseProposal.projectResponse runtime leaks bounds owner past view response =
      chosen := Subtype.ext projects
  rw [← classEq]
  rcases response with ⟨⟨transmission⟩, member⟩
  cases transmission with
  | none =>
      apply phaseProposalBaseClasses_mem_of_response setup mode runtime leaks bounds plan values
        rates owner past view ⟨⟨none⟩, member⟩
      rw [base]
      exact mem_support_mix_left _ _ _ waitPositive ((PMF.mem_support_pure_iff _ _).mpr rfl)
  | some material =>
      obtain ⟨serial, opening, evidence, rfl, _bounded, _fresh⟩ :=
        PhaseCount.onePacket_binding_shape runtime leaks bounds plan
          (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining owner
          execution trace event payload binding request material member
      have slot := PhaseProposal.binding_slot_of_counted_response runtime leaks bounds plan
        (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining owner
          execution trace event payload binding request serial opening evidence member boundedValues
      let result : PublicationResult (L.Val payload) :=
        (opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success
      have canonicalMember := (Finset.mem_filter.mp slot).2.2 result
      have same := PhaseProposal.responseClass_binding runtime leaks bounds owner past view event
        payload binding serial opening evidence member canonicalMember
      have projectSame : PhaseProposal.projectResponse runtime leaks bounds owner past view
          ⟨⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩, member⟩ =
        PhaseProposal.projectResponse runtime leaks bounds owner past view
          ⟨phaseBindingResponse runtime leaks owner event payload result serial, canonicalMember⟩ :=
        Subtype.ext same
      rw [projectSame]
      apply phaseProposalBaseClasses_mem_of_response setup mode runtime leaks bounds plan values
        rates owner past view ⟨_, canonicalMember⟩
      rw [base]
      apply mem_support_mix_right _ _ _ waitBelow
      apply mem_support_mix_left _ _ _ slotPositive
      have nonempty :
          (PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
            past view).Nonempty :=
        ⟨serial, slot⟩
      rw [PhaseCount.phaseBindingSlotPolicy, dite_eq_left nonempty]
      apply (PMF.mem_support_bind_iff _ _ _).mpr
      refine ⟨serial, (PMF.mem_support_uniformOfFinset_iff ..).mpr slot, ?_⟩
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, resultsFull result, rfl⟩

end Vegas
