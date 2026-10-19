/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryFailedLocalLaw
import Vegas.Game.ProposalRecoveryGains
import Vegas.Game.CommitRecoveryGlobalWordDensity
import Vegas.Game.ProposalRecoveryCommitFailure
import Vegas.Game.ProposalRecoveryDebtPayoff
import Vegas.Game.CommitRecoveryAcceptedFailure
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.Joint

/-! # An unusable declaration compared with the same attempt's domain choices -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- The forced declaration belongs to this actual stopped window, rather
than to an older failed attempt in the retained word. -/
theorem proposalRecovery_local_failed_window_recorded
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (choice : setup.proposalRecoveryModel.Choice focal
      (setup.proposalRecoveryModel.infoOf focal prior))
    (failed : ∃ move, choice.val.map (·.semantic) = some move ∧ move.action.IsFailure)
    (final : setup.proposalRecoveryProtocol.History)
    (supported : final ∈ (setup.proposalRecoveryModel.runBehavioralUntil certificate
      (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) profile focal
        ((profile focal).withLaw (setup.proposalRecoveryModel.infoOf focal prior)
          (PMF.pure choice)))
      (fun history => prior.length + ProtocolState.remaining setup.program first.point ≤
        history.trace.length + ProtocolState.commitEnd setup.program first.point)
      ⟨some first, prior⟩).support) :
    ∃ joint ∈ (setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace final.trace)).take
          (ProtocolState.remaining setup.program first.point -
            ProtocolState.commitEnd setup.program first.point),
      ∃ move, joint focal = some move ∧ move.action.IsFailure := by
  classical
  let altered := Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
    profile focal ((profile focal).withLaw (setup.proposalRecoveryModel.infoOf focal prior)
      (PMF.pure choice))
  let stopped := fun history : setup.proposalRecoveryProtocol.History =>
    prior.length + ProtocolState.remaining setup.program first.point ≤
      history.trace.length + ProtocolState.commitEnd setup.program first.point
  have positive := ProtocolState.commitEnd_lt_remaining setup.program first.point committing
  have going : ¬ stopped ⟨some first, prior⟩ := by
    dsimp only [stopped]
    omega
  have running : ¬ setup.proposalRecoveryProtocol.terminal (some first) := by
    intro terminal
    have zero := (ProtocolState.remaining_zero_iff_terminal setup.program first.point).mpr terminal
    omega
  have boundary := setup.proposalRecovery_stopped_window_boundary altered certificate
    first prior committing final supported
  change final ∈ (setup.proposalRecoveryModel.runBehavioralUntil certificate altered stopped
    ⟨some first, prior⟩).support at supported
  rw [setup.proposalRecoveryModel.runBehavioralUntil_of_running certificate altered going running,
    PMF.mem_support_bind_iff] at supported
  obtain ⟨child, firstStep, continued⟩ := supported
  rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal altered 0 running,
    PMF.mem_support_bind_iff] at firstStep
  obtain ⟨draw, drawn, realizedStep⟩ := firstStep
  rw [PMF.mem_support_bindOnSupport_iff] at realizedStep
  obtain ⟨target, realized, childEq⟩ := realizedStep
  have childSame : child = (⟨some first, prior⟩ : setup.proposalRecoveryProtocol.History).extend
      draw.property realized := by
    simpa only [InformationModel.runBehavioralFrom, runRandomizedFor,
      PMF.mem_support_pure_iff] using childEq
  subst child
  have selected : (draw.val focal).map (·.semantic) = choice.val.map (·.semantic) := by
    have marginal : draw.val ∈ ((setup.proposalRecoveryModel.behavioralJoint altered prior
        running).map Subtype.val).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
    rw [setup.proposalRecoveryModel.behavioralJoint_map_val,
      independentProduct_support_iff] at marginal
    have own : draw.val focal = choice.val := by
      simpa only [altered, Profile.update_same, InformationModel.BehavioralPolicy.withLaw_self,
        PMF.pure_map, PMF.mem_support_pure_iff] using marginal focal
    exact congrArg (Option.map (·.semantic)) own
  have kept := setup.proposalRecoveryModel.runBehavioralUntil_support_prefix certificate
    altered stopped _ final continued
  have erasedKept := setup.proposalRecoveryEraseTrace_prefix kept
  change TracePrefix
    ((setup.proposalRecoveryEraseTrace prior).extend (proposalRecoveryJoint draw.val)
      (setup.proposalRecovery_erase_legal draw.val draw.property) realized)
        (setup.proposalRecoveryEraseTrace final.trace) at erasedKept
  obtain ⟨added, word, length⟩ := setup.commitRecovery_joint_word_prefix
    (setup.proposalRecoveryEraseTrace prior) (proposalRecoveryJoint draw.val)
      (setup.proposalRecovery_erase_legal draw.val draw.property) realized
        ⟨final.state, setup.proposalRecoveryEraseTrace final.trace⟩
        erasedKept
  simp only [setup.proposalRecoveryEraseTrace_length] at length
  let fuel := ProtocolState.remaining setup.program first.point -
    ProtocolState.commitEnd setup.program first.point
  have addedLength : added.length + 1 = fuel := by dsimp only [fuel]; omega
  refine ⟨proposalRecoveryJoint draw.val, ?_, ?_⟩
  · change _ ∈ (setup.recoveryJointRecall
      (setup.proposalRecoveryEraseTrace final.trace)).take fuel
    rw [word, List.take_append, show fuel - added.length = 1 by omega]
    exact List.mem_append_right _ (by simp only [List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false])
  · obtain ⟨move, chosen, fails⟩ := failed
    exact ⟨move, selected.trans chosen, fails⟩

variable
  (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
  (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
  (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
  (values : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
    PMF (setup.CommitRecoveryValueChoice who key.1))

local notation "baseline" => setup.proposalRecoveryNormalizedTrembledProfile omission
  omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded values

open Classical in
/-- Couple the two actual stopped laws on their common omission word. On
reset both use the same selected continuation; without reset the failed
declaration is checkpointed and its owner receives the floor. -/
theorem proposalRecoveryNormalizedTrembledProfile_accepted_failure_value_le
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (focal : Player) (site : setup.proposalRecoveryModel.InfoState focal)
    (atSite : setup.proposalRecoveryModel.infoOf focal prior = site)
    (choice : setup.proposalRecoveryModel.Choice focal site)
    (failed : ∃ move, choice.val.map (·.semantic) = some move ∧
      move.action.IsFailure ∧ move.missing = false)
    (law : PMF (setup.proposalRecoveryModel.Choice focal site))
    (nonmissing : ∀ selected ∈ law.support,
      CommitRecoveryMove.missed (selected.val.map (·.semantic)) = false) :
    let certificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
    let altered := fun currentLaw => Profile.update
      (sig := setup.proposalRecoveryModel.behavioralSignature) baseline focal
        ((baseline focal).withLaw site currentLaw)
    expect (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
      (altered (PMF.pure choice)) ⟨some first, prior⟩)
        (setup.proposalRecoveryPayoff utility excludedPayoff focal) ≤
      expect (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate
        (altered law) ⟨some first, prior⟩)
          (setup.proposalRecoveryPayoff utility excludedPayoff focal) := by
  classical
  subst site
  let : Finite setup.proposalRecoveryProtocol.History := setup.proposalRecovery_finite_history
    finite
  intro certificate altered
  let payoff := setup.proposalRecoveryPayoff utility excludedPayoff focal
  let stopped := fun history : setup.proposalRecoveryProtocol.History =>
    prior.length + ProtocolState.remaining setup.program first.point ≤
      history.trace.length + ProtocolState.commitEnd setup.program first.point
  let badWindow := setup.proposalRecoveryModel.runBehavioralUntil certificate
    (altered (PMF.pure choice)) stopped ⟨some first, prior⟩
  let otherWindow := setup.proposalRecoveryModel.runBehavioralUntil certificate
    (altered law) stopped ⟨some first, prior⟩
  let word := setup.proposalRecoveryOmissionWord
  let finish := setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate baseline
  let mean := fun history => expect (finish history) payoff
  have ending : ProtocolState.commitEnd setup.program first.point =
      ProtocolState.commitEnd setup.program first.saved := by
    rcases setup.commitRecovery_blockFrontier (setup.proposalRecoveryEraseTrace prior) with
      ⟨_saved, _live, ending⟩ | same
    · exact ending
    · rw [same]
  let fuel := ProtocolState.remaining setup.program first.point -
    ProtocolState.commitEnd setup.program first.point
  have positive := ProtocolState.commitEnd_lt_remaining setup.program first.point committing
  have distance : fuel + ProtocolState.commitEnd setup.program first.saved =
      ProtocolState.remaining setup.program first.point := by dsimp only [fuel]; omega
  have missed : CommitRecoveryMove.missed (choice.val.map (·.semantic)) = false := by
    obtain ⟨move, selected, _failed, absent⟩ := failed
    simp only [selected, CommitRecoveryMove.missed, Option.elim_some, absent]
  have marginals : (PMF.pure choice).map (fun selected =>
      CommitRecoveryMove.missed (selected.val.map (·.semantic))) =
      law.map (fun selected => CommitRecoveryMove.missed (selected.val.map (·.semantic))) := by
    rw [PMF.pure_map, missed]
    symm
    exact (map_congr_on_support law nonmissing).trans (PMF.map_const _ _)
  have words : badWindow.map word = otherWindow.map word :=
    setup.proposalRecoveryNormalizedTrembledProfile_local_window_omissions omission
      omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded values certificate focal first prior
      committing (PMF.pure choice) law marginals
  let paired := bindPairLaw badWindow (fun left => fiberPosterior otherWindow word (word left))
  have leftMarginal : paired.map Prod.fst = badWindow := bindPairLaw_map_fst _ _
  have rightMarginal : paired.map Prod.snd = otherWindow := by
    rw [bindPairLaw_map_snd]
    change badWindow.bind ((fiberPosterior otherWindow word) ∘ word) = otherWindow
    rw [← PMF.bind_map, words, fiberPosterior_reconstruct]
  have conditional : ∀ pair ∈ paired.support, mean pair.1 ≤ mean pair.2 := by
    intro pair supported
    rw [show paired = badWindow.bind (fun left =>
      (fiberPosterior otherWindow word (word left)).map (fun right => (left, right))) from rfl,
      PMF.mem_support_bind_iff] at supported
    obtain ⟨left, leftSupported, pairSupported⟩ := supported
    obtain ⟨right, rightSupported, pairEq⟩ := (PMF.mem_support_map_iff _ _ _).mp pairSupported
    subst pair
    have present : word left ∈ (otherWindow.map word).support := by
      rw [← words]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨left, leftSupported, rfl⟩
    obtain ⟨sameWord, rightSupported⟩ := mem_support_fiberPosterior present rightSupported
    obtain ⟨leftKept, boundary⟩ := setup.proposalRecovery_stopped_window_boundary
      (altered (PMF.pure choice)) certificate first prior committing left leftSupported
    obtain ⟨rightKept, _rightBoundary⟩ := setup.proposalRecovery_stopped_window_boundary
      (altered law) certificate first prior committing right rightSupported
    obtain ⟨last, state⟩ := setup.state_some_of_prefix first
      (setup.proposalRecoveryEraseTrace prior) (setup.proposalRecoveryEraseTrace left.trace)
      (setup.proposalRecoveryEraseTrace_prefix leftKept)
    by_cases newFailure : (last.excluded \ first.entryExcluded).Nonempty
    · have shared := setup.proposalRecovery_failed_attempt_terminal_eq
        (fun who key => setup.proposalRecoveryComponentTrembledLaw who key
          omission omissionNonnegative omissionBounded bad badNonnegative badBounded
          delivery deliveryNonnegative deliveryBounded (values who key))
        certificate focal first prior committing left.trace right.trace leftKept rightKept
        sameWord.symm boundary (by rwa [state])
      apply le_of_eq
      simpa only [mean, finish, payoff, proposalRecoveryNormalizedTrembledProfile,
        Function.comp_def, ← setup.proposalRecoveryPayoff_eq_image] using
        expect_observed_law_eq _ _ setup.proposalRecoveryErasedHistory
          setup.proposalRecoveryErasedHistory
          (setup.proposalRecoveryImagePayoff utility excludedPayoff focal) shared
    · have grows : first.excluded ⊆ last.excluded := by
        simpa only [state, commitRecoveryPublic] using
          setup.prefix_excluded (setup.proposalRecoveryEraseTrace prior)
            (setup.proposalRecoveryEraseTrace left.trace)
            (setup.proposalRecoveryEraseTrace_prefix leftKept)
      have clear : last.excluded = first.entryExcluded := by
        apply Finset.Subset.antisymm _ (first.entered.trans grows)
        exact Finset.sdiff_eq_empty_iff_subset.mp
          (Finset.not_nonempty_iff_eq_empty.mp newFailure)
      have recorded := setup.proposalRecovery_local_failed_window_recorded baseline certificate
        focal first prior committing choice (by
          obtain ⟨move, chosen, fails, _⟩ := failed
          exact ⟨move, chosen, fails⟩) left leftSupported
      have constant : mean left = excludedPayoff focal := by
        calc
          mean left = expect (finish left) (fun _ => excludedPayoff focal) :=
            expect_congr_on_support fun final continued => by
              have prefixSupport := continued
              dsimp only [finish] at prefixSupport
              rw [InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
                setup.proposalRecoveryModel certificate setup.proposalRecoveryProtocol_bounded]
                  at prefixSupport
              have retained := ReachesWithin.tracePrefix
                (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin baseline _ left
                  final prefixSupport)
              exact setup.proposalRecovery_failed_commit_prefix_payoff finite first prior committing
                fuel distance focal left leftKept (by dsimp only [fuel]; omega)
                (by rwa [state]) recorded utility excludedPayoff final
                retained
                (setup.proposalRecoveryModel.runBehavioralTerminalFrom_support_terminal
                  certificate baseline left final continued)
          _ = _ := expect_constant _ _
      rw [constant, ← expect_constant (finish right) (excludedPayoff focal)]
      apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
      intro final continued
      exact setup.proposalRecovery_terminal_payoff_lower utility excludedPayoff below focal final
        (setup.proposalRecoveryModel.runBehavioralTerminalFrom_support_terminal
          certificate baseline right final continued)
  have averaged : expect badWindow mean ≤ expect otherWindow mean := by
    have compared := expect_mono conditional (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    calc
      expect badWindow mean = expect (paired.map Prod.fst) mean := by rw [leftMarginal]
      _ = expect paired (mean ∘ Prod.fst) := expect_map _ _ _
      _ ≤ expect paired (mean ∘ Prod.snd) := compared
      _ = expect (paired.map Prod.snd) mean := (expect_map _ _ _).symm
      _ = expect otherWindow mean := by rw [rightMarginal]
  have split (currentLaw : PMF (setup.proposalRecoveryModel.Choice focal
      (setup.proposalRecoveryModel.infoOf focal prior))) :=
    setup.proposalRecoveryNormalizedTrembledProfile_local_terminal_window omission
      omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded values certificate focal first prior
      committing currentLaw
  rw [split (PMF.pure choice), split law]
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
    expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  exact averaged

open Classical in
/-- The same comparison is integrated on the assessment's ORIGINAL complete
information fiber. A known retry or an ordinary representative is not assumed. -/
theorem proposalRecovery_normalized_accepted_failure_conditional_value_le
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (prescribed : ∀ who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        baseline who (setup.proposalRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (choice : setup.proposalRecoveryModel.Choice focal site.1)
    (failed : ∃ move, choice.val.map (·.semantic) = some move ∧
      move.action.IsFailure ∧ move.missing = false)
    (law : PMF (setup.proposalRecoveryModel.Choice focal site.1))
    (nonmissing : ∀ selected ∈ law.support,
      CommitRecoveryMove.missed (selected.val.map (·.semantic)) = false) :
    let certificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
    let context := assessment.continuationContext certificate site
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)
    context.value ((assessment.strategy focal).withLaw site.1 (PMF.pure choice)) ≤
      context.value ((assessment.strategy focal).withLaw site.1 law) := by
  classical
  let : Finite setup.proposalRecoveryProtocol.History := setup.proposalRecovery_finite_history
    finite
  intro certificate context
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    InformationModel.BehavioralAssessment.continuationContext_value]
  apply expect_bind_mono_on_support _ _ _ _ (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)
  intro history _supported
  have actual := setup.proposalRecovery_local_terminal_prescribed assessment
    (fun who key => setup.proposalRecoveryComponentTrembledLaw who key
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded (values who key))
    prescribed certificate focal site.1
  rw [actual _ history.1, actual _ history.1]
  rcases history with ⟨⟨state, trace⟩, atSite⟩
  have currentCommit := committing
  have clock := setup.commitRecovery_atCommit_info focal
    (setup.proposalRecoveryEraseTrace trace)
  rw [← setup.proposalRecoveryEraseInfo_observed] at clock
  change (setup.proposalRecoveryModel.infoOf focal trace).1.1.1.elim false
    (ProtocolView.atCommit focal setup.program) = _ at clock
  rw [← atSite, clock] at currentCommit
  cases state with
  | none => cases currentCommit
  | some first =>
      exact setup.proposalRecoveryNormalizedTrembledProfile_accepted_failure_value_le
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded values finite utility excludedPayoff below
        first trace currentCommit focal site.1 atSite choice failed law nonmissing

end Vegas.SourceProgram.Setup
