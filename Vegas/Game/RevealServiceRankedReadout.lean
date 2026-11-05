/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealServicePayoffs
import Vegas.Compile.ConcurrentRevealGraph

/-! # Source readout in instruction order

The service reader decodes the native history in completion order, so with
concurrent reveals the public default record depends on the scheduler. The
ranked reader decodes the same store against the history rearranged into
instruction order, which is how the source semantics indexes default entries.
The two readers agree whenever the history is already in instruction order, in
particular on every run of the sequential service graph.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

open Interaction EventGraphRuntime GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Configured

variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- Read the complete source configuration from the native terminal store, with
completions listed in instruction order. -/
def serviceRankedReadout (state : (serviceApplication setup mode deadline leaks).ProtocolState) :
    Option (Config Player L setup.program.terminalCtx) :=
  state.bind fun control =>
    let config := control.execution.application.config
    if config.cut.Terminal then
      Vegas.decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
        (Setup.rankedHistory (graph := serviceGraph setup mode) config)
    else none

omit [DecidableEq Player] in
/-- A history already in rank order is its own ranked history. -/
theorem rankedHistory_eq_of_rankSort {graph : Vegas.EventGraph Player L}
    (config : graph.Config)
    (ordered : graph.rankSort (config.history.map EventCompletion.event) =
      config.history.map EventCompletion.event) :
    Setup.rankedHistory config = config.history := by
  have records : ∀ completion ∈ config.history,
      completionOf config completion.event = some completion := fun completion member =>
    (completionOf_eq_some_iff config completion.event completion).mpr ⟨member, rfl⟩
  have restricted : (List.finRange graph.order.eventCount).filterMap (completionOf config) =
      ((List.finRange graph.order.eventCount).filter fun event =>
        event ∈ config.history.map EventCompletion.event).filterMap (completionOf config) := by
    rw [List.filterMap_filter]
    congr 1
    funext event
    by_cases member : event ∈ config.history.map EventCompletion.event
    · simp [member]
    · have absent : completionOf config event = none := by
        rw [← Option.not_isSome_iff_eq_none, ← mem_completed_iff_completionOf,
          ← config.history_exact]
        exact member
      simp [member, absent]
  unfold Setup.rankedHistory
  rw [restricted]
  change (graph.rankSort (config.history.map EventCompletion.event)).filterMap _ = _
  rw [ordered, List.filterMap_map]
  calc _ = config.history.filterMap some :=
        List.filterMap_congr fun completion member => records completion member
    _ = config.history := List.filterMap_some

/-- On a history in instruction order, the ranked and the service readers agree. -/
theorem serviceRankedReadout_eq_of_rankSort
    (control : (serviceApplication setup mode deadline leaks).Control)
    (ordered : (serviceGraph setup mode).rankSort
        (control.execution.application.config.history.map EventCompletion.event) =
      control.execution.application.config.history.map EventCompletion.event) :
    serviceRankedReadout setup mode deadline leaks (some control) =
      serviceSourceReadout setup mode deadline leaks (some control) := by
  unfold serviceRankedReadout serviceSourceReadout
  simp only [Option.bind_some]
  rw [rankedHistory_eq_of_rankSort _ ordered]

end Configured

end Vegas
