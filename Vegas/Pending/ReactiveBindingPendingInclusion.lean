/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingPendingCommands
import Vegas.Pending.ReactiveBindingUsableStep

/-! # Real inclusion of the pending failed binding

The anchored bare commitment can be accepted or rejected at its actual include
command. Public rejection preserves the pending frame. Actual acceptance
completes its named binding and recovers completed memory from the one pending
exception. Neither timely acceptance nor completed pending memory is assumed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- The actual pending envelope's include law preserves its frame and exceptional
memory. Completion of that actual event, rather than a timing promise, restores
CompletedAt. The fixed candidate and original failure are submission resources. -/
theorem pending_failed_binding_include_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (pending : graph.EventId)
    (past : memory.shadow.CompletedExcept original.application.config pending)
    (payload : L.Ty)
    (outputEq : graph.outputLayout pending = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes pending) = .bind owner payload)
    (node : nodeView graph pending = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle graph)
    (found : original.network.lookup id =
      some ⟨id, ⟨.commitment pending candidate, none, some ⟨pending⟩⟩⟩)
    (leftFixed : original.application.candidates.lookup candidate ≠ .fresh)
    (rightFixed : repaired.application.candidates.lookup candidate ≠ .fresh)
    (failed : original.application.bindingResult candidate payload = .failure)
    (rememberedAction : memory.shadow.actions pending = some
      (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure))
    (rememberedValue : memory.shadow.values (.inr pending) = some
      (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure)) :
    let app := runtime.reactiveApplication leaks
    ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = original.environmentStep app (.include id) ∧
      coupling.map Prod.snd = repaired.environmentStep app (.include id) ∧
      ∀ pair ∈ coupling.support,
        Frame runtime leaks memory owner pair.1 pair.2 ∧
          memory.shadow.CompletedExcept pair.1.application.config pending ∧
          (pending ∈ pair.1.application.config.cut.completed →
            memory.shadow.CompletedAt pair.1.application.config) := by
  let app := runtime.reactiveApplication leaks
  let included (execution : app.Execution) : app.Execution :=
    { execution.includePending app id with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .include id⟩] }
  have actual (execution : app.Execution) :
      execution.environmentStep app (.include id) = PMF.pure (included execution) := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  have retained := (runtime.reactiveCompletedInvariant leaks
    original.application.config.cut.completed).includePending original id (Finset.Subset.refl _)
  have pendingMemory : memory.shadow.CompletedExcept
      (included original).application.config pending := past.mono retained
  refine ⟨PMF.pure (included original, included repaired), ?_, ?_, ?_⟩
  · rw [PMF.pure_map, actual]
  · rw [PMF.pure_map, actual]
  · intro pair supported
    cases (PMF.mem_support_pure_iff _ _).mp supported
    refine ⟨?_, pendingMemory, pendingMemory.completedAt⟩
    by_cases allowed : original.application.publicView.BindingIncludable runtime
        ⟨id, .commitment pending candidate⟩
    swap
    · exact frame.commitment_step_not_includable id pending candidate none (some ⟨pending⟩)
        found allowed
    change original.application.publicView.EventReady pending ∧
      original.application.WithinDeadline runtime pending ∧ _ at allowed
    obtain ⟨publicReady, timely, checks⟩ := allowed
    simp only [node, Message.sender] at checks
    obtain ⟨sender, owned, vacant, unused⟩ := checks
    have ready := (original.application.publicView_eventReady pending).mp publicReady
    exact frame.pending_binding_inclusion pending payload outputEq codeEq node id candidate
      sender owned found ready timely vacant unused leftFixed rightFixed
      (by simpa only [failed] using rememberedAction)
      (by simpa only [failed] using rememberedValue)
      (fun value success => by rw [failed] at success; cases success)

end Vegas.EventGraphRuntime.BindingMemory.Frame
