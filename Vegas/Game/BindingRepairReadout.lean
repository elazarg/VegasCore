/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphParameterReadout
import Vegas.Game.RevealServicePayoffs
import Vegas.Pending.ReactiveBindingFrameStep

/-! # Analysis outcomes of concrete hidden-binding repair

The actual paired native states have the same initial parameters and public
source result, including their joint dependence. The proof uses the native
frame and typed terminal decoding; it assumes neither a source execution law
nor an equality of repaired future hidden values.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem bindingFrame_parameterReadout {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (parameter : State L setup.context → Parameter)
    (owner : Player) (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Control)
    (frame : memory.Frame (runtime setup) leaks owner original.execution repaired.execution)
    (onlyBindings : memory.shadow.OwnBindings owner) :
    (sourceReadout setup leaks (some original)).map (setup.parameterOutcome parameter) =
      (sourceReadout setup leaks (some repaired)).map (setup.parameterOutcome parameter) := by
  have observations := congrArg (PublicView.observation (graph := graph setup)) frame.publicView
  have orders := congrArg EventGraph.PublicObservation.completionOrder observations
  have stores := congrArg EventGraph.PublicObservation.store observations
  change original.execution.application.config.history.map EventGraph.Completion.event =
    repaired.execution.application.config.history.map EventGraph.Completion.event at orders
  have completed : original.execution.application.config.cut.completed =
      repaired.execution.application.config.cut.completed := by
    ext event
    rw [← original.execution.application.config.history_exact event,
      ← repaired.execution.application.config.history_exact event, orders]
  have terminal : original.execution.application.config.cut.Terminal ↔
      repaired.execution.application.config.cut.Terminal := by
    unfold EventOrder.Cut.Terminal
    rw [completed]
  unfold sourceReadout serviceSourceReadout
  simp only [Option.bind_some]
  by_cases done : original.execution.application.config.cut.Terminal
  · rw [ite_eq_left done, ite_eq_left (terminal.mp done)]
    obtain ⟨left, leftEq⟩ := Option.isSome_iff_exists.mp
      (decodeState?_isSome_of_available (terminalRefs setup.program)
        original.execution.application.config.store
        (original.execution.application.config.store_available_of_terminal done))
    obtain ⟨right, rightEq⟩ := Option.isSome_iff_exists.mp
      (decodeState?_isSome_of_available (terminalRefs setup.program)
        repaired.execution.application.config.store
        (repaired.execution.application.config.store_available_of_terminal (terminal.mp done)))
    rw [leftEq, rightEq, Option.map_some, Option.map_some]
    exact congrArg some (decoded_parameterOutcome_eq setup parameter .sequential
      original.execution.application.config repaired.execution.application.config left right
      leftEq rightEq (frame.inputs onlyBindings) stores)
  · rw [ite_eq_right done, ite_eq_right (fun h => done (terminal.mpr h))]

/-- Every utility of persistent initial parameters and public results is
unchanged by the concrete repair, before any audit charge. -/
theorem bindingFrame_baseUtility {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (owner : Player) (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Control)
    (frame : memory.Frame (runtime setup) leaks owner original.execution repaired.execution)
    (onlyBindings : memory.shadow.OwnBindings owner) :
    baseUtility setup leaks (fun source => utility (setup.parameterOutcome parameter source))
        (some original) =
      baseUtility setup leaks (fun source => utility (setup.parameterOutcome parameter source))
        (some repaired) := by
  have same := bindingFrame_parameterReadout setup leaks parameter owner memory original repaired
    frame onlyBindings
  funext who
  have value := congrArg (fun outcome : Option (Parameter × PublicOutcome setup.program) =>
    outcome.elim 0 (fun output => utility output who)) same
  cases first : sourceReadout setup leaks (some original) <;>
    cases second : sourceReadout setup leaks (some repaired) <;>
    simp only [baseUtility, serviceBaseUtility, first, second, Option.map_none, Option.map_some,
      Option.elim_none, Option.elim_some] at value ⊢
  all_goals exact value

end Vegas
