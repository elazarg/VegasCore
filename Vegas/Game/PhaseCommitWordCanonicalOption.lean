/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCommitTimingWordPolicy
import Vegas.Pending.PhaseBindingWordHistory

/-! # The actual prescribed word channel as its genuine fresh timing option -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

/-- The independent eligible-slot tier and its selected eligible serial use
one original omission law before encoding. -/
theorem phaseBindingTimingWordResponse_at_eligible
    (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (missing : PMF Bool) (serial : Fin bounds.candidateCount)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (result : PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (eligible : serial.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
      past view) :
    phaseBindingTimingWordResponse setup mode runtime leaks bounds owner event payload missing
        (some serial) slotWeight slotNonnegative slotBounded result past view =
      PhaseCount.phaseBindingWordResponse runtime leaks bounds owner event payload missing
        serial.val slotWeight slotNonnegative slotBounded result past view := by
  classical
  simp only [phaseBindingTimingWordResponse, eligible, ↓reduceIte,
    PhaseCount.phaseBindingWordResponse, mix_one, mix_zero]
  rw [← bind_mix_kernel]
  apply congrArg (PMF.bind missing)
  funext omitted
  cases omitted <;> simp only [Bool.false_eq_true, ↓reduceIte, mix_self]

/-- At an actual active unsent binding, the prescribed member is exactly the
timing member of its genuine least fresh serial, uniformly over all original
complete words and failed results. The slot is derived from the actual history. -/
theorem phaseCommitWordPolicy_canonical_option
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player) (active : control.actor = some owner)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs
      (control.execution.recall owner), PhaseCount.event? message.payload ≠
        some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (inside : low ≤ event.val ∧ event.val < low + block.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩) :
    ∃ serial : Fin bounds.candidateCount,
      (reactiveFreshSlot (control.execution.observe (phaseApplication runtime leaks)
        owner).application.1).getD 0 = serial.val ∧
      ∀ word, phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment block low
          generation slotWeight slotNonnegative slotBounded owner word
            (control.execution.recall owner)
              (control.execution.observe (phaseApplication runtime leaks) owner) =
        phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed assessment block low
          generation slotWeight slotNonnegative slotBounded (some serial) owner word
            (control.execution.recall owner)
              (control.execution.observe (phaseApplication runtime leaks) owner) := by
  classical
  let missing := fun (_past : List (phaseApplication runtime leaks).PlayerEntry)
      (view : (phaseApplication runtime leaks).PlayerView) =>
    (assessment.strategy owner (setup.commitRecoveryClearInformation wellFormed owner
      (phaseSourceView? setup mode runtime leaks owner event view))).map
        (fun choice => CommitRecoveryMove.missed choice.1)
  let read := fun word => (phaseRecoveryBindingData setup mode event owner payload binding
    (CommitRecoveryMove.lift (block.wordAction owner (event.val - low) word))).1
  obtain ⟨serial, bounded, serialEq, _slots, _offered, wordLaw⟩ :=
    PhaseCount.phaseBindingWordPolicy_of_history runtime leaks bounds owner event payload binding
      missing slotWeight slotNonnegative slotBounded read
        (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler capacity
          control trace active request unsent values
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨canonical, _canonicalBounded, selected⟩ := PhaseCandidates.reactiveFreshSlot_lt_horizon
    runtime leaks plan inputs horizon scheduler control raw owner active
  have sameSerial : serial = canonical := by
    change (reactiveFreshSlot _).getD 0 = serial at serialEq
    rw [selected] at serialEq
    exact serialEq.symm
  subst canonical
  have eligible := PhaseCount.mem_phaseBindingSlots_of_history runtime leaks bounds
    (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler control trace
      owner
      event payload binding request unsent values serial (bounded.trans_le capacity)
        (reactiveFreshSlot_spec _ serial selected)
  obtain ⟨draw, invariant⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler raw
  refine ⟨⟨serial, bounded.trans_le capacity⟩, serialEq, ?_⟩
  intro word
  rw [phaseCommitWordPolicy_binding setup mode runtime leaks bounds wellFormed assessment block low
    generation slotWeight slotNonnegative slotBounded owner word control.execution invariant event
      payload binding request inside address]
  rw [wordLaw word]
  rw [phaseCommitTimingWordPolicy_binding setup mode runtime leaks bounds wellFormed assessment
    block low generation slotWeight slotNonnegative slotBounded _ owner word control.execution
      invariant event payload binding request inside address]
  exact (phaseBindingTimingWordResponse_at_eligible setup mode runtime leaks bounds owner event
    payload _ ⟨serial, bounded.trans_le capacity⟩ slotWeight slotNonnegative slotBounded _ _ _
      eligible).symm

end Vegas
