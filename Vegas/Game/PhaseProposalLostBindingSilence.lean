/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalLostBindingWord
import Vegas.Pending.PhaseBindingResponseWitness

/-! # A lost sender has no later strategic choice in its unfinished attempt

Every future callback before the original omission closes has only WAIT.
The proof uses actual remembered SEND provenance and source owner order,
rather than a policy restriction or an unobserved qualification event.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- An actual later callback of the lost sender admits exactly WAIT, even
with inherited exclusions and arbitrary remembered private aliases. -/
theorem phase_lost_binding_callback_silent
    (scheduler : (app).Scheduler) (ordered : graph.RevealRelaxedOrdered)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (prior : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (closing : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some closing))
    (retained : TracePrefix prior trace)
    (same : execution.application.attempt = closing.execution.application.attempt)
    (after : (app).Execution) (current : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution after current)
    (phase : RuntimePhase graph)
    (installed : closing.execution.application.phases.head? = some phase)
    (kind : phase.kind = .commitment)
    (omitted : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout omitted = .binding owner payload)
    (inside : omitted ∈ phase.events)
    (unaccepted : (phase.drain current).native.accepted (.inr omitted) = none)
    (entry : (app).PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (material : WitnessedSubmission graph)
    (transmitted : entry.action.transmission = some material)
    (candidate : Handle graph)
    (named : material.call.packet = .commitment omitted candidate)
    (sameEntry : entry.beforeView.application.2.attempt = execution.application.attempt) :
    PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
      (execution.observe app owner) = {⟨none⟩} := by
  classical
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have nativeOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler prior)
  have metadata := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler ⟨remaining, some owner, execution⟩ closing prior trace retained nativeOrdered same
  have phases : execution.application.phases = closing.execution.application.phases :=
    congrArg Prod.fst metadata
  have currentInstalled : execution.application.phases.head? = some phase := by
    rw [phases]
    exact installed
  apply Finset.ext
  intro response
  constructor
  · intro offered
    apply Finset.mem_singleton.mpr
    cases response with
    | mk transmission =>
        cases transmission with
        | none => rfl
        | some sent =>
            exfalso
            obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks
              bounds plan inputs horizon scheduler remaining owner execution prior sent offered
            obtain ⟨actualPhase, head, member⟩ := request.2.1
            have headEq : execution.application.phases.head? = some actualPhase :=
              Option.mem_def.mp head
            have phaseEq : actualPhase = phase :=
              Option.some.inj (headEq.symm.trans currentInstalled)
            subst actualPhase
            obtain ⟨lower, upper⟩ := phase.mem_events coordinate.event |>.mp member
            have field := phase.fields coordinate.event lower upper
            rw [kind] at field
            obtain ⟨actor, ty, eventBinding⟩ := field
            have actorEq : actor = owner := Option.some.inj
              ((actor?_of_outputLayout_binding graph eventBinding).symm.trans request.2.2.2.1)
            subst actor
            have coordinateEq : coordinate = ⟨execution.application.attempt, coordinate.event⟩ := by
              cases coordinate with
              | mk attempt event =>
                  congr 1
                  exact request.1
            rw [coordinateEq] at request
            have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan ordered inputs
              horizon scheduler remaining owner execution prior _ request sent offered
            have later := phase_recorded_binding_rank_lt_of_unsent_request runtime leaks bounds
              plan inputs horizon ordered scheduler prior owner entry recorded material transmitted
              omitted
              candidate named sameEntry coordinate.event request unsent
            have forbidden := phase_closing_unaccepted_no_later_owned_request runtime leaks bounds
              plan inputs horizon scheduler ordered ⟨remaining, some owner, execution⟩ closing prior
              trace retained same after current effect phase currentInstalled owner omitted
              coordinate.event payload ty binding eventBinding inside unaccepted request
            exact forbidden later
  · intro silent
    cases Finset.mem_singleton.mp silent
    exact PhaseCount.silence_onePacket runtime leaks bounds owner _ _

end Vegas.EventGraphRuntime
