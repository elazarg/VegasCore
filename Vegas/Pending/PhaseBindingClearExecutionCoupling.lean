/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingClearCommandLaw
import Interaction.ReactiveRounds

/-! # Original execution-command coupling up to first public exclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- An original application command couples entire surviving executions with
their actual saved and live memory. First exclusion is jointly projected out;
all unchanged private words and the exact original scheduler entry are retained. -/
theorem environment_clear_execution_coupling (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (clear : right.application.current.excluded = ∅)
    (opaquePhase : ∀ phase ∈ right.application.phases.head?, phase.kind = .commitment)
    (command : EnvironmentCommand graph) :
    ∃ paired : PMF (Option (app).Execution × Option (app).Execution),
      paired.map Prod.fst = ((left.environmentStep app (.application command)).map fun next =>
        if next.application.current.excluded = ∅ then some next else none) ∧
      paired.map Prod.snd = ((right.environmentStep app (.application command)).map fun next =>
        if next.application.current.excluded = ∅ then some next else none) ∧
      ∀ pair ∈ paired.support, match pair with
        | (none, none) => True
        | (some first, some second) =>
            first.application = memory.phased owner second.application ∧
            first.network = second.network ∧ first.receipts = second.receipts ∧
            first.environmentRecall = second.environmentRecall ∧
            (∀ who, who ≠ owner → first.recall who = second.recall who) ∧
            first.recall owner = left.recall owner ∧ second.recall owner = right.recall owner
        | _ => False := by
  classical
  let finish (physical : (app).Execution) (state : PhaseRuntimeState graph) : (app).Execution :=
    { physical with application := state, environmentRecall := physical.environmentRecall ++
      [⟨physical.observeEnvironment app, .application command⟩] }
  let paired := (right.application.environment runtime command).map fun state =>
    if state.current.excluded = ∅ then
      (some (finish left (memory.phased owner state)), some (finish right state)) else (none, none)
  have before : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, application, phased_publicView owned]
    rfl
  refine ⟨paired, ?_, ?_, ?_⟩
  · have original := environment_clear_observation_law runtime memory owner owned
      right.application clear opaquePhase command
    have lifted := congrArg (fun law : PMF (Option (PhaseRuntimeState graph)) =>
      law.map (fun state => state.map (finish left))) original
    simp only [PMF.map_comp, Function.comp_def, apply_ite, Option.map_some, Option.map_none]
      at lifted
    simp only [paired, PMF.map_comp, Function.comp_def, apply_ite]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    rw [application]
    exact lifted.symm
  · simp only [paired, ReactiveApplication.Execution.environmentStep, PMF.map_comp,
      Function.comp_def, apply_ite]
    rfl
  · intro pair supported
    obtain ⟨state, _supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    by_cases survives : state.current.excluded = ∅
    · simp only [survives, ite_true] at same
      cases same
      refine ⟨rfl, network, receipts, ?_, recalled, rfl, rfl⟩
      change left.environmentRecall ++ [_] = right.environmentRecall ++ [_]
      rw [service, before]
    · simp only [survives, ite_false] at same
      cases same
      trivial

end Vegas.EventGraphRuntime.BindingShadow
