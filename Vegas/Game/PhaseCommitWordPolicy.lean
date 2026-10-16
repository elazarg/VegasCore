/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixWord
import Vegas.Game.PhaseSourcePolicy
import Vegas.Game.PhaseSourceSlotPolicy
import Vegas.Pending.PhaseBindingWordHistory
import Interaction.ReactiveMixtureRecall

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
  phasePolicyDispatch setup mode runtime leaks (fun owner event payload binding =>
      PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _ _ =>
      PMF.pure true))
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
  phasePolicyDispatch_covered (opened := (fun owner event payload binding past view response
      supported => PhaseCount.phaseOpeningPolicy_covered runtime leaks bounds owner event payload
      binding (fun _ _ => PMF.pure true) past view response supported)) setup mode runtime leaks
      bounds (fun owner event payload binding => PhaseCount.phaseOpeningPolicy runtime leaks
      bounds owner event payload binding (fun _ _ => PMF.pure true)) _
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
  rw [phaseCommitWordPolicy, phasePolicyDispatch_binding setup mode runtime leaks (fun owner event
      payload binding => PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload
      binding (fun _ _ => PMF.pure true)) _
    execution valid who event payload binding request]
  unfold commitWordBinding
  simp only [dite_true, cast_eq,
    ite_eq_left (show low ≤ event.val ∧ event.val < low + block.length ∧
      (execution.observe (phaseApplication runtime leaks) who).application.2.attempt =
        ⟨low, generation⟩ from ⟨inside.1, inside.2, address⟩)]


/-- Every concrete raw response has the same mass for all whole-word members
that support it. This holds for the total dispatcher: dormant callbacks and
openings are word independent, sends identify their typed result, and binding
WAIT keeps the original omission draw without revealing a latent value. -/
theorem phaseCommitWordPolicy_apply_eq_of_support
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (first second : DecisionView who Δ)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (left : response ∈ (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded who first past view).support)
    (right : response ∈ (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded who second past view).support) :
    phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment block low generation
        slotWeight slotNonnegative slotBounded who first past view response =
      phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment block low
        generation slotWeight slotNonnegative slotBounded who second past view response := by
  classical
  unfold phaseCommitWordPolicy at left right ⊢
  apply phasePolicyDispatch_apply_eq_of_support setup mode runtime leaks (fun owner event payload
      binding => PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding
      (fun _ _ => PMF.pure true)) _ _ who past view
    response ?_ left right
  intro owner event payload binding left right
  unfold commitWordBinding at left right ⊢
  by_cases owned : owner = who
  · simp only [dite_eq_left owned] at left right ⊢
    by_cases addressed : low ≤ event.val ∧ event.val < low + block.length ∧
        view.application.2.attempt = ⟨low, generation⟩
    · simp only [ite_eq_left addressed] at left right ⊢
      exact PhaseCount.phaseBindingWordPolicy_apply_eq_of_support runtime leaks bounds owner event
        payload _ _ slotWeight slotNonnegative slotBounded _ _ _ past view response left right
    · simp only [ite_eq_right addressed]
  · simp only [dite_eq_right owned]


open Classical in
/-- The whole actual own-recall posterior of the immutable word implementation
is the original word prior conditioned by the supported member fiber. All
recorded WAIT, opening, dormant and slot probabilities cancel on that fiber;
source failed results remain distinct possible sending values. -/
theorem phaseCommitWordPolicy_posterior_consistency_fiber
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (prior : PMF (DecisionView who Δ))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (consistent : ((phaseApplication runtime leaks).policyMixture prior
      (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment block low
        generation slotWeight slotNonnegative slotBounded who)).policy.Consistent past) :
    ((phaseApplication runtime leaks).policyMixture prior
      (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment block low
        generation slotWeight slotNonnegative slotBounded who)).posterior past =
      fiberPosterior prior (fun word => decide ((phaseCommitWordPolicy setup mode runtime leaks
        bounds wellFormed assessment block low generation slotWeight slotNonnegative slotBounded
          who word).Consistent past)) true := by
  apply (phaseApplication runtime leaks).policyMixture_posterior_consistency_fiber prior _ ?_ past
    consistent
  intro earlier view response first second left right
  exact phaseCommitWordPolicy_apply_eq_of_support setup mode runtime leaks bounds wellFormed
    assessment block low generation slotWeight slotNonnegative slotBounded who first second earlier
      view response left right


/-- At any full physical input, the word family is either constant or uses
one addressed owned binding channel. This is a decomposition of the existing
total dispatcher, with no assumption about source or native likelihoods. -/
theorem phaseCommitWordPolicy_cases
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    (∃ law, ∀ word, phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded who word past view = law) ∨
    ∃ event payload, ∃ binding :
      (serviceGraph setup mode).outputLayout event = .binding who payload,
      (low ≤ event.val ∧ event.val < low + block.length) ∧
      view.application.2.attempt = ⟨low, generation⟩ ∧
      ∀ word, phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment block low
        generation slotWeight slotNonnegative slotBounded who word past view =
        PhaseCount.phaseBindingWordPolicy runtime leaks bounds who event payload
          (fun _ view => (assessment.strategy who
            (setup.commitRecoveryClearInformation wellFormed who
              (phaseSourceView? setup mode runtime leaks who event view))).map
                (fun choice => CommitRecoveryMove.missed choice.1))
          (fun _ view => (reactiveFreshSlot view.application.1).getD 0)
          slotWeight slotNonnegative slotBounded
          (fun word => (phaseRecoveryBindingData setup mode event who payload binding
            (CommitRecoveryMove.lift (block.wordAction who (event.val - low) word))).1)
          word past view := by
  classical
  obtain constant | ⟨event, payload, binding, selected⟩ :=
    phasePolicyDispatch_indexed_cases setup mode runtime leaks (fun owner event payload binding =>
        PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _ _ =>
        PMF.pure true))
      (fun word => commitWordBinding setup mode runtime leaks bounds wellFormed assessment block low
        generation slotWeight slotNonnegative slotBounded who word) who past view
  · exact Or.inl constant
  · by_cases addressed : low ≤ event.val ∧ event.val < low + block.length ∧
        view.application.2.attempt = ⟨low, generation⟩
    · refine Or.inr ⟨event, payload, binding, ⟨addressed.1, addressed.2.1⟩, addressed.2.2, ?_⟩
      intro word
      rw [phaseCommitWordPolicy, selected word]
      simp only [commitWordBinding, dite_true, cast_eq, ite_eq_left addressed]
    · refine Or.inl ⟨mix slotWeight slotNonnegative slotBounded
        (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
          payload binding past view)
        (phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed assessment who event
          payload binding past view), ?_⟩
      intro word
      rw [phaseCommitWordPolicy, selected word]
      simp only [commitWordBinding, dite_true, ite_eq_right addressed]

end Vegas
