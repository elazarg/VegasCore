/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalLostBindingClosure
import Vegas.Pending.PhaseProposalEmissionOrder
import Vegas.Game.PhaseCountServiceForeignWord

/-! # The complete emission word at an original omitted binding

The closing witness is the real primitive command before settlement. The
source-ranked bound applies to every recalled private submission in that
attempt, retaining each original evidence alias and prepared slot.
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

/-- No later owned binding SEND occurs anywhere in the literal recalled
word of an attempt whose original closing snapshot omits this binding. The
claim includes inherited exclusions and does not inspect a restored table. -/
theorem phase_closing_unaccepted_binding_word_bound
    (scheduler : (app).Scheduler) (ordered : graph.RevealRelaxedOrdered)
    (closing : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some closing))
    (after : (app).Execution) (current : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution after current)
    (phase : RuntimePhase graph)
    (installed : closing.execution.application.phases.head? = some phase)
    (owner : Player) (omitted : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout omitted = .binding owner payload)
    (inside : omitted ∈ phase.events)
    (unaccepted : (phase.drain current).native.accepted (.inr omitted) = none) :
    ∀ (entry : (app).PlayerEntry), entry ∈ closing.execution.recall owner →
      ∀ (material : WitnessedSubmission graph),
        entry.action.transmission = some material →
        entry.beforeView.application.2.attempt = closing.execution.application.attempt →
        ∀ (event : graph.EventId) (candidate : Handle graph) (eventPayload : L.Ty),
          material.call.packet = .commitment event candidate →
          graph.outputLayout event = .binding owner eventPayload →
          event.val ≤ omitted.val := by
  intro entry recorded material transmitted sameNamespace event candidate eventPayload named
    eventBinding
  obtain ⟨before, prior, retained, _acting, viewed, request⟩ :=
    phase_recorded_binding_request runtime leaks bounds plan inputs horizon ordered scheduler
      trace owner entry recorded material transmitted event candidate named
  have same : before.execution.application.attempt = closing.execution.application.attempt := by
    rw [viewed] at sameNamespace
    exact sameNamespace
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have beforeOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized ((menu).toRawTrace initial horizon scheduler prior)
  have metadata := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler before closing prior trace retained beforeOrdered same
  have phases : before.execution.application.phases = closing.execution.application.phases :=
    congrArg Prod.fst metadata
  have beforeInstalled : before.execution.application.phases.head? = some phase := by
    rw [phases]
    exact installed
  have noLater := phase_closing_unaccepted_no_later_owned_request runtime leaks bounds plan inputs
    horizon scheduler ordered before closing prior trace retained same after current effect phase
      beforeInstalled owner omitted event payload eventPayload binding eventBinding inside
        unaccepted request
  omega

end Vegas.EventGraphRuntime
