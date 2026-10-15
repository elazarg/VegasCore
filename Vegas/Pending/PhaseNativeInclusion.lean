/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeHandle

/-! # Clear physical inclusions commute with native message execution -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- Every envelope selected for physical inclusion was actually authored. -/
theorem included_authentic (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (selected : (current.execution.network.includePending id).1 = some message) :
    message ∈ current.execution.network.inputs := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have origins := (P).retained_envelopes_mem_inputs current.execution
    ((P).history_provenance _ horizon scheduler raw)
    ((P).history_inputRecall _ horizon scheduler raw)
  unfold MessageNetwork.includePending at selected
  cases found : current.execution.network.lookup id with
  | none => simp only [found] at selected; cases selected
  | some actual =>
      simp only [found] at selected
      cases Option.some.inj selected
      exact origins.pending message (List.mem_of_find?_eq_some found)

/-- Including an authentic packet preserves the full projected execution whenever
its actual normalized endpoint has no exclusion. -/
theorem includePending_of_clear_result (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (id : MessageId Player)
    (afterClear : (current.execution.includePending P id).application.current.excluded = ∅) :
    execution runtime leaks plan (current.execution.includePending P id) =
      (execution runtime leaks plan current.execution).includePending N id := by
  have handles (message : Message Player (CommitAttemptPacket graph))
      (selected : (current.execution.network.includePending id).1 = some message) :=
    handle_map_of_clear runtime leaks plan bounds ordered maximal inputs horizon scheduler trace
      clear message (included_authentic runtime leaks plan bounds inputs horizon scheduler trace
        id message selected)
  simp only [ReactiveApplication.Execution.includePending, execution] at afterClear ⊢
  rw [← MessageNetwork.mapPayload_includePending]
  generalize queued : current.execution.network.includePending id = pair at afterClear ⊢
  rcases pair with ⟨envelope, network⟩
  cases envelope with
  | none => rfl
  | some message =>
      have selected : (current.execution.network.includePending id).1 = some message :=
        congrArg Prod.fst queued
      dsimp only [] at afterClear ⊢
      have handled := handles message selected
      change (P).handle current.execution.application message = _ at handled
      erw [handled] at afterClear ⊢
      simp only [Option.map_some] at afterClear ⊢
      cases accepted : (N).handle current.execution.application.current.native
          (Message.mapPayload CommitAttemptPacket.packet message) with
      | none =>
          simp only [Option.map_none, Option.getD_none, Option.isSome_none]
      | some native =>
          rw [accepted, Option.map_some, Option.getD_some] at afterClear
          simp only [Option.map_some, Option.getD_some, Option.isSome_some]
          have same := PhaseRuntimeState.normalize_of_clear
            ({ current.execution.application with
              current := current.execution.application.current.inclusionResult
                message.payload.packet.call native } : PhaseRuntimeState graph) afterClear
          erw [same.1]
          rfl

end Vegas.EventGraphRuntime.PhaseNativeProjection
