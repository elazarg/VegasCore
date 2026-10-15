/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingWordKernel
import Vegas.Pending.PhaseBindingSlotHistory

/-! # Actual callback guards of latent binding-word members

The permanent physical catalogue and the real callback count select the
canonical slot. Its menu guard holds for every latent result at an initialized
unsent binding callback. No source-word likelihood identity is assumed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

/-- All latent members use one actual fresh-slot channel, with their global
menu guards discharged from the genuine initialized physical trace. -/
theorem phaseBindingWordPolicy_of_history {Word : Type}
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (missing : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF Bool)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (read : Word → PublicationResult (L.Val payload))
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control)) (active : control.actor = some who)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    let serialAt := fun (_ : List (phaseApplication runtime leaks).PlayerEntry)
        (view : (phaseApplication runtime leaks).PlayerView) =>
      (reactiveFreshSlot view.application.1).getD 0
    ∃ serial, serial < horizon ∧
      serialAt (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who) = serial ∧
      (phaseBindingSlots runtime leaks bounds who event payload (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).Nonempty ∧
      (∀ result, phaseBindingResponse runtime leaks who event payload result serial ∈
        onePacketActions runtime leaks bounds who (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who)) ∧
      ∀ word, phaseBindingWordPolicy runtime leaks bounds who event payload missing serialAt
        slotWeight slotNonnegative slotBounded read word (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) =
        phaseBindingWordResponse runtime leaks bounds who event payload
          (missing (control.execution.recall who)
            (control.execution.observe (phaseApplication runtime leaks) who)) serial slotWeight
          slotNonnegative slotBounded (read word) (control.execution.recall who)
            (control.execution.observe (phaseApplication runtime leaks) who) := by
  classical
  intro serialAt
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨serial, bounded, selected⟩ := PhaseCandidates.reactiveFreshSlot_lt_horizon runtime leaks
    plan inputs horizon scheduler control raw who active
  have member := mem_phaseBindingSlots_of_history runtime leaks bounds menu plan inputs horizon
    scheduler control trace who event payload outputEq request unsent values serial
      (bounded.trans_le capacity) (reactiveFreshSlot_spec _ serial selected)
  have offered := (Finset.mem_filter.mp member).2.2
  have serialEq : serialAt (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who) = serial := by
    change (reactiveFreshSlot _).getD 0 = serial
    rw [selected]
    rfl
  refine ⟨serial, bounded, serialEq, ⟨serial, member⟩, offered, ?_⟩
  intro word
  unfold phaseBindingWordPolicy
  rw [serialEq, ite_eq_left offered]

end Vegas.EventGraphRuntime.PhaseCount
