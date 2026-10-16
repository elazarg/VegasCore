/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingOpaqueEnvironment

/-! # Literal same-command physical replay in an opaque binding block -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every actual clear application-command outcome has a genuine same-command
outcome reconstructing its complete phase state and full external history.
The saved entry and candidate memory are retained; no target outcome is supplied. -/
theorem environment_opaque_replay (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (clear : right.application.current.excluded = ∅)
    (bindingPhase : ∀ phase ∈ right.application.phases.head?, phase.kind = .commitment)
    (command : EnvironmentCommand graph) (next : (app).Execution)
    (reached : next ∈ (left.environmentStep app (.application command)).support)
    (nextClear : next.application.current.excluded = ∅) :
    ∃ image ∈ (right.environmentStep app (.application command)).support,
      next.application = memory.phased owner image.application ∧
      next.network = image.network ∧ next.receipts = image.receipts ∧
      next.environmentRecall = image.environmentRecall ∧
      (∀ who, who ≠ owner → next.recall who = image.recall who) := by
  classical
  let finish (physical : (app).Execution) (state : PhaseRuntimeState graph) : (app).Execution :=
    { physical with
      application := state
      environmentRecall := physical.environmentRecall ++
        [⟨physical.observeEnvironment app, .application command⟩] }
  have before : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, application, phased_publicView owned]
    rfl
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
  change next ∈ ((left.application.environment runtime command).map (finish left)).support
    at reached
  obtain ⟨firstState, moved, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  have rawClear : firstState.current.excluded = ∅ := nextClear
  have law : left.application.environment runtime command =
      (right.application.environment runtime command).map (memory.phased owner) := by
    rw [application] at moved ⊢
    exact environment_opaque_memory runtime memory owner owned right.application clear bindingPhase
      command firstState moved rawClear
  rw [law] at moved
  obtain ⟨secondState, supported, equality⟩ := (PMF.mem_support_map_iff _ _ _).mp moved
  subst firstState
  refine ⟨finish right secondState, ?_, rfl, network, receipts, ?_, recalled⟩
  · simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    change finish right secondState ∈
      ((right.application.environment runtime command).map (finish right)).support
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨secondState, supported, rfl⟩
  · change left.environmentRecall ++ [_] = right.environmentRecall ++ [_]
    rw [service, before]

end Vegas.EventGraphRuntime.BindingShadow
