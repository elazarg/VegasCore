/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountedSeedService
import Vegas.Pending.ReactiveReadyOwnerMiss
import Interaction.ReactiveTraceExtension

/-! # Genuine service domains along protected surviving episodes -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Genuine clean service domains persist through actual covered dispatches while
an ordered ready event of the same owner remains unfinished. -/
theorem countedSeedDomain_dispatch_of_ready_survives
    (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (ordered : graph.RevealRelaxedOrdered)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (bounds.onePacketMenu runtime leaks).actions who past view)
    (owner : Player) (event : graph.EventId) (owned : graph.actor? event = some owner)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (genuine : runtime.CountedSeedDomain leaks bounds inputs owner execution)
    (ready : execution.application.config.cut.Ready event)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ ((runtime.reactiveApplication leaks).dispatch players command
      execution).support)
    (unfinished : event ∉ next.application.config.cut.completed) :
    runtime.CountedSeedDomain leaks bounds inputs owner next := by
  obtain ⟨horizon, scheduler, remaining, ⟨trace⟩, unmissed⟩ := genuine
  obtain ⟨extended, realized⟩ := (bounds.onePacketMenu runtime leaks).trace_dispatch
    (inputs.map State.initial) horizon scheduler remaining execution next trace players covered
    command reached
  refine ⟨horizon + 1, extended, remaining, realized, ?_⟩
  exact runtime.unmissed_dispatch_of_ready_survives leaks ordered players execution next command
    event owner ready owned unmissed reached unfinished

/-- An actual retained activation supplies the ready premise of the protected
survival closure used by the local seed observer's run induction. -/
theorem countedSeedDomain_dispatch_of_activated_survives
    (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (ordered : graph.RevealRelaxedOrdered)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (bounds.onePacketMenu runtime leaks).actions who past view)
    (owner : Player) (event : graph.EventId) (owned : graph.actor? event = some owner)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (genuine : runtime.CountedSeedDomain leaks bounds inputs owner execution)
    (setup : graph.Inputs) (invariant : execution.application.Invariant setup)
    (entered : Nat) (activated : execution.application.activatedAt event = some entered)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ ((runtime.reactiveApplication leaks).dispatch players command
      execution).support)
    (unfinished : event ∉ next.application.config.cut.completed) :
    runtime.CountedSeedDomain leaks bounds inputs owner next := by
  apply runtime.countedSeedDomain_dispatch_of_ready_survives leaks bounds inputs ordered players
    covered owner event owned execution next genuine ?_ command reached unfinished
  exact ((invariant.activated_iff event).mp (by rw [activated]; rfl)).1

end Vegas.EventGraphRuntime
