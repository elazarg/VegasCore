/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochInterval
import Vegas.Pending.PhaseBindingServiceCompletion
import Vegas.Pending.PhaseSeedServiceBook

/-! # Actual phase geometry used by semantic cycle exhaustion -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

structure ProgressGeometry (inputs : graph.Inputs) (state : PhaseRuntimeState graph) : Prop where
  valid : WorkValid inputs state
  frontier : state.Frontier
  live : state.Live
  maximal : RuntimePhase.PartitionRegular state.phases
  quiescent : ∀ event, ¬ state.current.AutomaticReady event

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
theorem progress_geometry_invariant (ordered : graph.RevealRelaxedOrdered)
    (inputs : graph.Inputs) : (app).Invariant (ProgressGeometry inputs) where
  submit state owner material geometry := by
    have nextGeometry := (phaseApplication_quiescent runtime leaks ordered).submit
      state owner material ⟨geometry.frontier, geometry.maximal, geometry.quiescent⟩
    have living := (phaseApplication_live runtime leaks).submit state owner material
      ⟨geometry.frontier, geometry.live⟩
    exact ⟨(work_valid_invariant runtime leaks inputs).submit state owner material geometry.valid,
      nextGeometry.1, living.2, nextGeometry.2.1, nextGeometry.2.2⟩
  handle state message next geometry reached := by
    have nextGeometry := (phaseApplication_quiescent runtime leaks ordered).handle
      state message next ⟨geometry.frontier, geometry.maximal, geometry.quiescent⟩ reached
    have living := (phaseApplication_live runtime leaks).handle state message next
      ⟨geometry.frontier, geometry.live⟩ reached
    exact ⟨(work_valid_invariant runtime leaks inputs).handle state message next geometry.valid
      reached, nextGeometry.1, living.2, nextGeometry.2.1, nextGeometry.2.2⟩
  environment state command next geometry reached := by
    have nextGeometry := (phaseApplication_quiescent runtime leaks ordered).environment
      state command next ⟨geometry.frontier, geometry.maximal, geometry.quiescent⟩ reached
    have living := (phaseApplication_live runtime leaks).environment state command next
      ⟨geometry.frontier, geometry.live⟩ reached
    exact ⟨(work_valid_invariant runtime leaks inputs).environment state command next geometry.valid
      reached, nextGeometry.1, living.2, nextGeometry.2.1, nextGeometry.2.2⟩

omit [Fintype Player] in
theorem runRounds_nonempty_before (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (count : Nat) (before after : (app).Execution)
    (ordered : before.application.Ordered)
    (reached : after ∈ ((app).runRounds scheduler players count before).support)
    (nonempty : after.application.phases ≠ []) : before.application.phases ≠ [] :=
  PhaseSeedCalendar.nonempty_of_namespace_progress before.application after.application
    (PhaseService.runRounds_namespace_progress runtime leaks scheduler players count before after
      ordered reached).2 nonempty

omit [Fintype Player] in
theorem initial_progress_geometry (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : RuntimePhase.PartitionRegular plan.phases) (inputs : graph.Inputs) :
    ProgressGeometry inputs (PhaseRuntimeState.initial plan inputs) := by
  have geometry := phaseApplication_initial_quiescent plan ordered maximal inputs
  exact ⟨⟨(PhaseRuntimeState.initial_invariant plan inputs).1,
    PhaseRuntimeState.initial_ordered plan inputs,
      PhaseRuntimeState.initial_seedBudget plan inputs⟩,
      geometry.1, PhaseRuntimeState.initial_live plan inputs, geometry.2.1, geometry.2.2⟩

end Vegas.EventGraphRuntime.ReservedEpoch
