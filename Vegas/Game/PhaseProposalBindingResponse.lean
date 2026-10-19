/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalEmissionFrontier
import Vegas.Game.PhaseProposalBindingAutomatic
import Vegas.Pending.PhaseBindingMenuShape

/-! # Actual native SEND updates preserve the same binding potential -/

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
local notation "graph" => serviceGraph setup mode

/-- The actual current raw response, including its retained private alias,
updates the SAME emission frontier before physical inclusion. The expectation
of its deterministic excluded closure is the original graph potential. -/
theorem phaseProposalUnflagged_binding_response_harmonic
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (horizon : Nat) (scheduler : (app).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount) (remaining : Nat) (who : Player)
    (execution anchor : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : RuntimePhase (graph)) (commitment : phase.kind = .commitment)
    (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (code : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind who payload)
    (inside : event ∈ phase.events) (active : who ∉ anchor.application.current.excluded)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (attempt : execution.application.attempt = anchor.application.attempt)
    (retired : execution.application.retired = anchor.application.retired)
    (failures : ∀ rank ≤ execution.application.attempt.phase,
      execution.application.current.native.publicView.sourceFailureFootprint.1 rank =
        anchor.application.current.native.publicView.sourceFailureFootprint.1 rank)
    (archive : PhaseProposal.observedSourceArchive runtime leaks (execution.recall who)
        (execution.observe app who) =
      PhaseProposal.observedSourceArchive runtime leaks (anchor.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor who
          ((graph).playerObserve who execution.application.current.native.config)))
    (frontier : (graph).Config)
    (agreement : execution.application.current.native.config.CompletedOutputAgreement frontier)
    (inputs : execution.application.current.native.config.inputs = frontier.inputs)
    (hidden : ∀ pending ∈ frontier.cut.completed,
      pending ∉ execution.application.current.native.config.cut.completed →
        ¬ (graph).fieldVisibleTo who (.inr pending)) :
    let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor
      phase values
    (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
      (execution.recall who) (execution.observe app who)).bind (fun response =>
        (graph).canonicalContinuation profile
          (phaseProposalBindingFrontierAdvance setup mode runtime leaks anchor phase frontier
            (some ⟨remaining, some who, execution⟩)
            (Function.update (fun _ => none) who (some response)))) =
      (graph).canonicalContinuation profile frontier := by
  intro profile
  obtain ⟨ready, harmonic⟩ := phaseProposalUnflagged_binding_emission_harmonic setup mode runtime
    leaks bounds plan complete covered maximal values fullValues horizon scheduler capacity
      remaining
      who execution anchor trace phase event payload binding code inside active request unsent
        attempt retired failures archive frontier agreement inputs hidden
  rw [← harmonic]
  apply bind_congr_on_support
  intro response supported
  obtain ⟨material, _value, transmitted, _typed⟩ :=
    phaseProposalUnflaggedBinding_supported_usable setup mode runtime leaks bounds plan complete
      covered maximal values fullValues horizon scheduler capacity remaining who execution trace
        event payload binding request unsent response supported
  let originalInputs := setup.initialLaw.map encodeInputs
  have counted : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (originalInputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some who, execution⟩) := by
    dsimp only [originalInputs]
    rw [PMF.map_comp]
    exact trace
  have member := phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values
    who (execution.recall who) (execution.observe app who) response supported
  have responseEq : response = ⟨some material⟩ := by
    cases response
    cases transmitted
    rfl
  rw [responseEq] at member
  obtain ⟨serial, opening, evidence, materialEq, _bounded, _fresh⟩ :=
    PhaseCount.onePacket_binding_shape runtime leaks bounds plan
      (serviceGraph_revealRelaxedOrdered setup mode) originalInputs horizon scheduler remaining who
        execution counted event payload binding request material member
  have packet : material.call.packet = .commitment event (who, .prepared serial) := by
    rw [materialEq]
  rw [phaseProposalBindingFrontierAdvance_binding setup mode runtime leaks anchor phase frontier
    remaining who execution (Function.update (fun _ => none) who (some response)) response
      (Function.update_self ..) material transmitted event (who, .prepared serial) packet payload
        binding code attempt inside ready]
  rw [phaseProposalPreparedBindingAction_step setup mode runtime leaks frontier event who payload
    binding code response ready, PMF.pure_bind]
  exact phaseProposalBindingPotentialProfile_drain setup mode runtime leaks plan anchor phase
    commitment values
      (⟨{ anchor.application.current.native with config := (frontier.complete event ready
        (phaseProposalPreparedBindingAction setup mode runtime leaks event who payload binding
          response)
        (cast (congrArg EventField.Value binding.symm)
          (((response.transmission.bind PhaseProposal.bindingPreparation).bind
            (fun raw => raw.as? payload)).elim PublicationResult.failure
              PublicationResult.success))) }, anchor.application.current.excluded⟩ :
        RecoveryState (graph)) rfl

end Vegas
