/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixWord
import Vegas.Game.PhaseSourcePolicy
import Vegas.Game.PhaseSourceSlotPolicy
import Vegas.Pending.PhaseBindingWordHistory

/-! # Physical member policies for one complete owned commitment word

The member reads only one owner's latent complete view. Actual requests and
the public phase address select the addressed action. Outside that block the
member uses the existing source recipe, independently of its latent word.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

open Classical in
private def commitWordBinding {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (word : DecisionView who Δ)
    (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload) :
    (phaseApplication runtime leaks).Policy := fun past view =>
  if same : owner = who then
    if low ≤ event.val ∧ event.val < low + block.length ∧
        view.application.2.attempt = ⟨low, generation⟩ then
      PhaseCount.phaseBindingWordPolicy runtime leaks bounds owner event payload
        (fun _ view =>
          (assessment.strategy owner (setup.commitRecoveryClearInformation wellFormed owner
            (phaseSourceView? setup mode runtime leaks owner event view))).map
              (fun choice => CommitRecoveryMove.missed choice.1))
        (fun _ view => (reactiveFreshSlot view.application.1).getD 0)
        slotWeight slotNonnegative slotBounded
        (fun ownWord => (phaseRecoveryBindingData setup mode event owner payload binding
          (CommitRecoveryMove.lift (block.wordAction owner (event.val - low) ownWord))).1)
        (cast (congrArg (fun owner => DecisionView owner Δ) same.symm) word) past view
    else mix slotWeight slotNonnegative slotBounded
      (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment
        owner event payload binding past view)
      (phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed assessment
        owner event payload binding past view)
  else PMF.pure ⟨none⟩

private theorem commitWordBinding_covered {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (word : DecisionView who Δ)
    (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (commitWordBinding setup mode runtime leaks bounds wellFormed
      assessment block low generation slotWeight slotNonnegative slotBounded who word owner event
        payload binding past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view := by
  classical
  unfold commitWordBinding at supported
  split at supported
  · split at supported
    · exact PhaseCount.phaseBindingWordPolicy_covered runtime leaks bounds owner event payload
        _ _ slotWeight slotNonnegative slotBounded _ _ past view response supported
    · rcases support_mix_subset _ _ _ _ _ supported with slot | canonical
      · exact phaseRecoverySlotPolicy_covered setup mode runtime leaks bounds wellFormed
          assessment owner event payload binding past view response slot
      · exact phaseRecoveryBindingPolicy_covered setup mode runtime leaks bounds wellFormed
          assessment owner event payload binding past view response canonical
  · cases (PMF.mem_support_pure_iff ..).mp supported
    exact PhaseCount.silence_onePacket runtime leaks bounds owner past view

/-- The total member uses one owner's complete latent word at this block's
actual requests. No saved entry or foreign private configuration is a policy
input. Omission flags remain fresh original source draws. -/
def phaseCommitWordPolicy {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (word : DecisionView who Δ) : (phaseApplication runtime leaks).Policy :=
  phasePolicyDispatch setup mode runtime leaks bounds
    (commitWordBinding setup mode runtime leaks bounds wellFormed assessment block low generation
      slotWeight slotNonnegative slotBounded who word) who

/-- Every member respects the original counted one-packet menu globally. -/
theorem phaseCommitWordPolicy_covered {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (word : DecisionView who Δ)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed
      assessment block low generation slotWeight slotNonnegative slotBounded who word past
        view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view :=
  phasePolicyDispatch_covered setup mode runtime leaks bounds _
    (commitWordBinding_covered setup mode runtime leaks bounds wellFormed assessment block low
      generation slotWeight slotNonnegative slotBounded who word) who past view response supported

/-- At a genuine owned binding request in the addressed block, the dispatcher
selects the concrete owner-word member channel. Its remaining physical menu
guard is discharged by `phaseBindingWordPolicy_of_history`. -/
theorem phaseCommitWordPolicy_binding {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (word : DecisionView who Δ)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (inside : low ≤ event.val ∧ event.val < low + block.length)
    (address : execution.application.attempt = ⟨low, generation⟩) :
    phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment block low
        generation slotWeight slotNonnegative slotBounded who word (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who) =
      PhaseCount.phaseBindingWordPolicy runtime leaks bounds who event payload
        (fun _ view => (assessment.strategy who
          (setup.commitRecoveryClearInformation wellFormed who
            (phaseSourceView? setup mode runtime leaks who event view))).map
              (fun choice => CommitRecoveryMove.missed choice.1))
        (fun _ view => (reactiveFreshSlot view.application.1).getD 0)
        slotWeight slotNonnegative slotBounded
        (fun ownWord => (phaseRecoveryBindingData setup mode event who payload binding
          (CommitRecoveryMove.lift (block.wordAction who (event.val - low) ownWord))).1)
        word (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) := by
  classical
  rw [phaseCommitWordPolicy, phasePolicyDispatch_binding setup mode runtime leaks bounds _
    execution valid who event payload binding request]
  unfold commitWordBinding
  simp only [dite_true, cast_eq,
    ite_eq_left (show low ≤ event.val ∧ event.val < low + block.length ∧
      (execution.observe (phaseApplication runtime leaks) who).application.2.attempt =
        ⟨low, generation⟩ from ⟨inside.1, inside.2, address⟩)]

end Vegas
