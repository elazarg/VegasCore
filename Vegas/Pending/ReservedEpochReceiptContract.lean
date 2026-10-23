/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochReceiptDelay
import Vegas.Pending.PhaseServiceContract

/-! # Raw receipt delays imply the physical protected-inclusion contract -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
theorem emission_receipt_of_idle (initial : PMF (app).State) (horizon bound : Nat)
    (scheduler : (app).Scheduler)
    (idle : ∀ remaining execution,
      ((app).protocol initial horizon scheduler).Trace (some ⟨remaining, none, execution⟩) →
      ∀ owner entry, entry ∈ execution.recall owner →
        ∀ message, entry.emitted = some message →
          entry.beforeView.application.1.publicView.clock + bound <
            execution.application.current.native.clock →
          ∃ accepted, (message.id, accepted) ∈ execution.receipts)
    (current : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some current))
    (owner : Player) (entry : (app).PlayerEntry)
    (recorded : entry ∈ current.execution.recall owner)
    (message : Message Player (app).Payload) (emitted : entry.emitted = some message)
    (elapsed : entry.beforeView.application.1.publicView.clock + bound <
      current.execution.application.current.native.clock) :
    ∃ accepted, (message.id, accepted) ∈ current.execution.receipts := by
  rcases current with ⟨remaining, actor, execution⟩
  cases actor with
  | none => exact idle remaining execution trace owner entry recorded message emitted elapsed
  | some actor =>
      obtain ⟨quietTrace⟩ := (app).raw_trace_respond initial horizon scheduler remaining execution
        actor ⟨none⟩ trace
      have quietRecorded := (app).respond_recall_mono execution actor owner ⟨none⟩ recorded
      obtain ⟨accepted, received⟩ := idle remaining (execution.respond app actor ⟨none⟩) quietTrace
        owner entry quietRecorded message emitted elapsed
      exact ⟨accepted, by simpa only [(app).respond_receipts] using received⟩

theorem family_emission_receipt {length : Nat} (cycles : Nat) (tape : Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps cycles activationGap processingGap)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
        (family runtime leaks (submissionBudget (Player := Player) cycles) tape)).Trace
          (some current))
    (owner : Player) (entry : (app).PlayerEntry)
    (recorded : entry ∈ current.execution.recall owner)
    (message : Message Player (app).Payload) (emitted : entry.emitted = some message)
    (elapsed : entry.beforeView.application.1.publicView.clock + (processingGap + 1) <
      current.execution.application.current.native.clock) :
    ∃ accepted, (message.id, accepted) ∈ current.execution.receipts := by
  apply emission_receipt_of_idle runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
    (horizon (graph := graph) cycles) (processingGap + 1)
      (family runtime leaks (submissionBudget (Player := Player) cycles) tape) _ current trace
        owner entry recorded message emitted elapsed
  intro remaining execution localTrace who remembered member envelope sent old
  exact idle_emission_receipt runtime leaks cycles tape activationGap processingGap gaps plan inputs
    remaining execution localTrace who remembered member envelope sent old

theorem family_protectedInclusion {length : Nat} (cycles : Nat) (tape : Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps cycles activationGap processingGap)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) :
    PhaseService.ProtectedInclusion runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
        (family runtime leaks (submissionBudget (Player := Player) cycles) tape)
          (fun _ => processingGap + 1) := by
  intro current trace coordinate owner _acting earlier later entry message recalled emitted
    _sender _attempt _event _ready _sole _current _unfinished elapsed
  apply family_emission_receipt runtime leaks cycles tape activationGap processingGap gaps plan
    inputs current trace owner entry _ message emitted elapsed
  rw [recalled]
  exact List.mem_append_right _ List.mem_cons_self

end Vegas.EventGraphRuntime.ReservedEpoch
