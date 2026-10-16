/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingMemoryFreshness
import Vegas.Pending.PhaseBindingSlotHistory

/-! # Actual eligible serials under all-value binding reconstruction -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Both genuine unsent callbacks offer exactly the same bounded serials.
The complete typed-result legality guard is discharged from the real traces;
no menu or slot-set equality is an input to the reconstruction. -/
theorem bindingSlots_eq_of_histories (bounds : MessageBounds graph)
    (menu : (app).ResponseMenu) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler)
    (left right : (app).Control)
    (leftTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some left))
    (rightTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some right))
    (memory : BindingShadow graph) (owner : Player)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (application : left.execution.application = memory.phased owner right.execution.application)
    (network : left.execution.network = right.execution.network)
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (request : right.execution.application.SeedRequest owner
      ⟨right.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (right.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨right.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
        (left.execution.recall owner) (left.execution.observe app owner) =
      PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
        (right.execution.recall owner) (right.execution.observe app owner) := by
  classical
  have leftRecall := (app).history_inputRecall _ horizon scheduler
    (menu.toRawTrace _ horizon scheduler leftTrace)
  have rightRecall := (app).history_inputRecall _ horizon scheduler
    (menu.toRawTrace _ horizon scheduler rightTrace)
  have outputs : (app).outputs (left.execution.recall owner) =
      (app).outputs (right.execution.recall owner) := by
    rw [← leftRecall owner, ← rightRecall owner, network]
  have attempt : left.execution.application.attempt = right.execution.application.attempt := by
    rw [application]
    rfl
  have leftRequest : left.execution.application.SeedRequest owner
      ⟨left.execution.application.attempt, event⟩ := by
    rw [application]
    exact request
  have leftUnsent : ∀ message ∈ (app).outputs (left.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨left.execution.application.attempt, event⟩ := by
    rw [outputs, attempt]
    exact unsent
  rw [PhaseCount.phaseBindingSlots_eq_fresh_of_history runtime leaks bounds menu plan inputs
    horizon scheduler left leftTrace owner event payload binding leftRequest leftUnsent values,
    PhaseCount.phaseBindingSlots_eq_fresh_of_history runtime leaks bounds menu plan inputs
      horizon scheduler right rightTrace owner event payload binding request unsent values]
  ext serial
  simp only [Finset.mem_filter]
  have fresh : left.execution.application.current.native.candidates.lookup
        (owner, .prepared serial) = .fresh ↔
      right.execution.application.current.native.candidates.lookup
        (owner, .prepared serial) = .fresh := by
    rw [application]
    simp only [phased, recovery, native, CommitmentCandidates.lookup, ↓reduceIte]
    exact memory.candidate_fresh_iff valid _ _
  exact and_congr Iff.rfl fresh

end Vegas.EventGraphRuntime.BindingShadow
