/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalUnflagged
import Vegas.Pending.PhaseOpeningPolicy

/-! # Actual unflagged publication responses disclose the locked value -/

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

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks

/-- At a genuine unspent publication request with a usable locked binding,
zero prospective flags emit the truthful packet with probability one. Private
syntax can be canonicalized, but the entire emitted packet is unchanged.
No guard success, timely receipt or semantic publication success is assumed. -/
theorem phaseProposalUnflaggedOpening_packet_law
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (inputs : PMF (graph).Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : (graph).EventId) (payload : L.Ty)
    (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (outputEq : (graph).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph).layout) outputEq) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (value : L.Val payload)
    (stored : binding.get? execution.application.current.native.config.store =
      some (.success value))
    (bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ candidate,
      execution.application.current.native.accepted binding.field = some candidate ∧
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values owner
        (execution.recall owner) (execution.observe app owner)).map
          (fun response => response.transmission.map fun material =>
            (PhaseCount.localEnvelope runtime leaks owner (execution.recall owner)
              (execution.observe app owner) material).payload) =
        PMF.pure ((PhaseCount.phaseOpeningResponse runtime leaks event candidate
          ⟨payload, value⟩).transmission.map fun material =>
            (PhaseCount.localEnvelope runtime leaks owner (execution.recall owner)
              (execution.observe app owner) material).payload) := by
  classical
  let past := execution.recall owner
  let view := execution.observe app owner
  let opens := fun (_ : List (app).PlayerEntry) (_ : (app).PlayerView) =>
    mix PhaseProposalRates.zero.waiting.val PhaseProposalRates.zero.waiting.property.1
      PhaseProposalRates.zero.waiting.property.2 (PMF.pure false) (PMF.pure true)
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨_draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  have base : phaseProposalBasePolicy setup mode runtime leaks bounds plan values
      PhaseProposalRates.zero owner past view =
        PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding
          opens past view := by
    unfold phaseProposalBasePolicy
    exact phasePolicyDispatch_opening setup mode runtime leaks _ _ execution native owner event
      payload binding checks outputEq codeEq request
  obtain ⟨candidate, accepted, opening⟩ := PhaseCount.phaseOpeningPolicy_of_history runtime leaks
    bounds plan inputs horizon scheduler trace owner event payload binding checks outputEq codeEq
      node request unsent value stored bounded opens
  have baseLaw : phaseProposalBasePolicy setup mode runtime leaks bounds plan values
      PhaseProposalRates.zero owner past view =
        PMF.pure (PhaseCount.phaseOpeningResponse runtime leaks event candidate
          ⟨payload, value⟩) := by
    rw [base, opening]
    simp only [opens, PhaseProposalRates.zero, mix_zero, PMF.pure_map, ↓reduceIte]
  have projected := congrArg (fun law : PMF
      (PhaseProposal.ResponseClass runtime leaks bounds owner past view) =>
        law.map (fun chosen => chosen.val.2))
    (phaseProposalUnflaggedResponses_project setup mode runtime leaks bounds plan values owner
      past view)
  have packetLaw : (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
      owner past view).map (fun response => response.transmission.map fun material =>
        (PhaseCount.localEnvelope runtime leaks owner past view material).payload) =
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan values PhaseProposalRates.zero
        owner past view).map (fun response => response.transmission.map fun material =>
          (PhaseCount.localEnvelope runtime leaks owner past view material).payload) := by
    rw [← phaseProposalBaseResponses_map_val setup mode runtime leaks bounds plan values
      PhaseProposalRates.zero owner past view]
    simpa only [phaseProposalUnflaggedPolicy, phaseProposalBaseClasses, PMF.map_comp,
      Function.comp_def, PhaseProposal.projectResponse, PhaseProposal.responseClass] using projected
  refine ⟨candidate, accepted, ?_⟩
  change (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values owner
    past view).map _ = _
  rw [packetLaw, baseLaw, PMF.pure_map]

/-- Every supported unflagged action discloses the existing accepted handle
at its fixed typed value. This is an emission fact, independent of whether a
later inclusion meets the deadline or passes its source guard. -/
theorem phaseProposalUnflaggedOpening_supported_truthful
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (inputs : PMF (graph).Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : (graph).EventId) (payload : L.Ty)
    (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (outputEq : (graph).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph).layout) outputEq) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (value : L.Val payload)
    (stored : binding.get? execution.application.current.native.config.store =
      some (.success value))
    (bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (response : (app).Action)
    (supported : response ∈ (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan
      values owner (execution.recall owner) (execution.observe app owner)).support) :
    ∃ (candidate : Handle graph) (material : WitnessedSubmission graph),
      execution.application.current.native.accepted binding.field = some candidate ∧
      response.transmission = some material ∧
      material.call.packet = .opening event candidate ⟨payload, value⟩ := by
  obtain ⟨candidate, accepted, law⟩ := phaseProposalUnflaggedOpening_packet_law setup mode runtime
    leaks bounds plan values inputs horizon scheduler remaining owner execution trace event
      payload binding checks outputEq codeEq node request unsent value stored bounded
  have observed := (PMF.mem_support_map_iff
    (fun action : (app).Action => action.transmission.map fun material =>
      (PhaseCount.localEnvelope runtime leaks owner (execution.recall owner)
        (execution.observe app owner) material).payload) _ _).mpr ⟨response, supported, rfl⟩
  rw [law] at observed
  have same := (PMF.mem_support_pure_iff _ _).mp observed
  cases transmitted : response.transmission with
  | none =>
      simp only [transmitted, PhaseCount.phaseOpeningResponse, Option.map_none,
        Option.map_some] at same
      cases same
  | some material =>
      refine ⟨candidate, material, accepted, rfl, ?_⟩
      simp only [transmitted, PhaseCount.phaseOpeningResponse, Option.map_some] at same
      have calls := congrArg (fun packet : CommitAttemptPacket graph => packet.packet.call)
        (Option.some.inj same)
      simpa only [PhaseCount.localEnvelope, PhaseCount.maskPacket_call,
        disclosureSubmission] using calls

end Vegas
