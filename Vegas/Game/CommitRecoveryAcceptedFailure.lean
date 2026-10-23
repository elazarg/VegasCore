/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryOmissionKernel
import Vegas.Game.CommitRecoveryCommitFailure
import Vegas.Game.CommitRecoveryVoluntaryFailurePayoff
import Vegas.Game.CommitRecoveryReference
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.Joint

/-! # Accepted failure compared with actual domain choices

The two original commitment-window laws are coupled on their common omission
word. A failed close erases both attempts; a clean close checkpoints the
actual failed declaration and forces its owner's permanent exclusion payoff.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
theorem commitRecovery_joint_word_prefix
    {state : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace state)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal state joint)
    {target : setup.commitRecoveryProtocol.State}
    (realized : target ∈ (setup.commitRecoveryProtocol.step state ⟨joint, legal⟩).support)
    (later : setup.commitRecoveryProtocol.History)
    (kept : TracePrefix (prior.extend joint legal realized) later.trace) :
    ∃ added, setup.recoveryJointRecall later.trace =
      added ++ joint :: setup.recoveryJointRecall prior ∧
      later.trace.length = prior.length + 1 + added.length := by
  rcases later with ⟨laterState, laterTrace⟩
  dsimp only at kept ⊢
  induction kept with
  | refl => exact ⟨[], rfl, by simp only [Trace.length, List.length_nil, Nat.add_zero]⟩
  | @extend _ _ _ _ actual _ _ ih =>
      obtain ⟨added, word, length⟩ := ih
      refine ⟨actual :: added, ?_, ?_⟩
      · simp only [recoveryJointRecall, word, List.cons_append]
      · simp only [Trace.length, List.length_cons]
        omega

open Classical in
/-- A forced failed current declaration occurs in the NEW original window
word. The occurrence is extracted from the actual supported first draw;
older failed records cannot discharge this conclusion. -/
theorem commitRecovery_local_failed_window_recorded
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (choice : setup.commitRecoveryModel.Choice focal
      (setup.commitRecoveryModel.infoOf focal prior))
    (failed : ∃ move, choice.val = some move ∧ move.action.IsFailure)
    (fuel : Nat) (positive : 0 < fuel)
    (within : fuel + ProtocolState.commitEnd setup.program first.saved ≤
      ProtocolState.remaining setup.program first.point)
    (final : setup.commitRecoveryProtocol.History)
    (supported : final ∈ (setup.commitRecoveryModel.runBehavioralFrom
      (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) profile focal
        ((profile focal).withLaw (setup.commitRecoveryModel.infoOf focal prior)
          (PMF.pure choice))) fuel ⟨some first, prior⟩).support) :
    ∃ joint ∈ (setup.recoveryJointRecall final.trace).take fuel,
      ∃ move, joint focal = some move ∧ move.action.IsFailure := by
  classical
  let altered := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
    profile focal ((profile focal).withLaw (setup.commitRecoveryModel.infoOf focal prior)
      (PMF.pure choice))
  have running : ¬ setup.commitRecoveryProtocol.terminal (some first) := by
    intro terminal
    have zero := (ProtocolState.remaining_zero_iff_terminal setup.program first.point).mpr terminal
    have positive := ProtocolState.commitEnd_lt_remaining setup.program first.point committing
    omega
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  change final ∈ (setup.commitRecoveryModel.runBehavioralFrom altered (rest + 1)
    ⟨some first, prior⟩).support at supported
  have originalSupported := supported
  rw [setup.commitRecoveryModel.runBehavioralFrom_succ_of_not_terminal altered rest running,
    PMF.mem_support_bind_iff] at supported
  obtain ⟨draw, drawn, continued⟩ := supported
  rw [PMF.mem_support_bindOnSupport_iff] at continued
  obtain ⟨target, realized, child⟩ := continued
  have selected : draw.val focal = choice.val := by
    have marginal : draw.val ∈ ((setup.commitRecoveryModel.behavioralJoint altered prior
        running).map Subtype.val).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
    rw [setup.commitRecoveryModel.behavioralJoint_map_val,
      independentProduct_support_iff] at marginal
    simpa only [altered, Profile.update_same, InformationModel.BehavioralPolicy.withLaw_self,
      PMF.pure_map, PMF.mem_support_pure_iff] using marginal focal
  have kept := ReachesWithin.tracePrefix
    (setup.commitRecoveryModel.runBehavioralFrom_reachesWithin altered rest
      ((⟨some first, prior⟩ : setup.commitRecoveryProtocol.History).extend
        draw.property realized) final child)
  obtain ⟨added, word, length⟩ :=
    setup.commitRecovery_joint_word_prefix prior draw.val draw.property
    realized final kept
  let initial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  obtain ⟨_last, _joints, _addresses, _state, _count, _path, consumed, _word, _signals⟩ :=
    setup.commitRecovery_run_commit_window_instructions altered initial (rest + 1) first prior
      committing within final originalSupported
  have addedLength : added.length = rest := by omega
  refine ⟨draw.val, ?_, ?_⟩
  · rw [word, List.take_append, addedLength, show rest.succ - rest = 1 by omega]
    exact List.mem_append_right _ (by simp only [List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false])
  · obtain ⟨move, chosen, failed⟩ := failed
    exact ⟨move, selected.trans chosen, failed⟩

variable
  (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
  (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
  (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
    PMF (setup.CommitRecoveryValueChoice who info))

local notation "baseline" => setup.commitRecoveryNormalizedTrembledProfile omission
  omissionNonnegative omissionBounded bad badNonnegative badBounded values

end Vegas.SourceProgram.Setup
