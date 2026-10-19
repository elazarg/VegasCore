/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryFailedLocalLaw
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

open Classical in
/-- The original accepted-failure experiment is weakly dominated by any
nonmissing current law. Each future window is sampled from its ORIGINAL law;
only the omission-word fibers are coupled in the proof. -/
theorem commitRecoveryNormalizedTrembledProfile_accepted_failure_value_le
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (focal : Player) (site : setup.commitRecoveryModel.InfoState focal)
    (atSite : setup.commitRecoveryModel.infoOf focal prior = site)
    (choice : setup.commitRecoveryModel.Choice focal site)
    (failed : ∃ move, choice.val = some move ∧ move.action.IsFailure ∧ move.missing = false)
    (law : PMF (setup.commitRecoveryModel.Choice focal site))
    (nonmissing : ∀ selected ∈ law.support, CommitRecoveryMove.missed selected.val = false) :
    let certificate := setup.commitRecoveryProtocol_bounded.wellFoundedHistories
    let altered := fun currentLaw => Profile.update
      (sig := setup.commitRecoveryModel.behavioralSignature) baseline focal
        ((baseline focal).withLaw site currentLaw)
    expect (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
      (altered (PMF.pure choice)) ⟨some first, prior⟩)
        (setup.commitRecoveryPayoff utility excludedPayoff focal) ≤
      expect (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (altered law) ⟨some first, prior⟩)
          (setup.commitRecoveryPayoff utility excludedPayoff focal) := by
  classical
  subst site
  let : Finite setup.commitRecoveryProtocol.History := setup.commitRecovery_finite_history finite
  intro certificate altered
  let payoff := setup.commitRecoveryPayoff utility excludedPayoff focal
  let fuel := ProtocolState.remaining setup.program first.point -
    ProtocolState.commitEnd setup.program first.saved
  let badWindow := setup.commitRecoveryModel.runBehavioralFrom (altered (PMF.pure choice))
    fuel ⟨some first, prior⟩
  let otherWindow := setup.commitRecoveryModel.runBehavioralFrom (altered law)
    fuel ⟨some first, prior⟩
  let word := fun history : setup.commitRecoveryProtocol.History =>
    setup.omissionRecall history.trace
  let finish := setup.commitRecoveryModel.runBehavioralTerminalFrom certificate baseline
  let mean := fun history => expect (finish history) payoff
  have ending : ProtocolState.commitEnd setup.program first.point =
      ProtocolState.commitEnd setup.program first.saved := by
    rcases setup.commitRecovery_blockFrontier prior with ⟨_saved, _live, ending⟩ | same
    · exact ending
    · rw [same]
  have inside := ProtocolState.commitEnd_lt_remaining setup.program first.point committing
  have positive : 0 < fuel := by dsimp only [fuel]; omega
  have distance : fuel + ProtocolState.commitEnd setup.program first.saved =
      ProtocolState.remaining setup.program first.point := by
    dsimp only [fuel]
    omega
  have missed : CommitRecoveryMove.missed choice.val = false := by
    obtain ⟨move, selected, _failed, absent⟩ := failed
    simp only [selected, CommitRecoveryMove.missed, Option.elim_some, absent]
  have marginals : (PMF.pure choice).map (fun selected =>
      CommitRecoveryMove.missed selected.val) =
      law.map (fun selected => CommitRecoveryMove.missed selected.val) := by
    rw [PMF.pure_map, missed]
    symm
    exact (map_congr_on_support law nonmissing).trans (PMF.map_const _ _)
  have words : badWindow.map word = otherWindow.map word :=
    setup.commitRecoveryNormalizedTrembledProfile_local_window_omissions omission
      omissionNonnegative omissionBounded bad badNonnegative badBounded values focal first prior
      committing (PMF.pure choice) law marginals fuel (by omega)
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
    have leftKept := ReachesWithin.tracePrefix
      (setup.commitRecoveryModel.runBehavioralFrom_reachesWithin
        (altered (PMF.pure choice)) fuel ⟨some first, prior⟩ left leftSupported)
    have rightKept := ReachesWithin.tracePrefix
      (setup.commitRecoveryModel.runBehavioralFrom_reachesWithin
        (altered law) fuel ⟨some first, prior⟩ right rightSupported)
    let initial := setup.initialConfig setup.initialLaw.support_nonempty.choose
    obtain ⟨last, _joints, _addresses, state, _length, _path, consumed, _word, _signals⟩ :=
      setup.commitRecovery_run_commit_window_instructions (altered (PMF.pure choice)) initial
        fuel first prior committing distance.le left leftSupported
    by_cases newFailure : (last.excluded \ first.entryExcluded).Nonempty
    · have shared := setup.commitRecoveryNoMissErasedProfile_failed_attempt_terminal_joint_eq
        (fun who info => setup.commitRecoveryValueTremble who info omission omissionNonnegative
          omissionBounded bad badNonnegative badBounded (values who info))
        utility excludedPayoff certificate focal first prior committing left.trace right.trace
        leftKept rightKept sameWord.symm (by omega) (by rwa [state])
      apply le_of_eq
      have equal := expect_observed_law_eq _ _ _ _
        (fun result : Option (State L setup.program.terminalCtx) × (Player → ℝ) =>
          result.2 focal) shared
      exact equal
    · have grows : first.excluded ⊆ last.excluded := by
        simpa only [state, commitRecoveryPublic] using
          setup.prefix_excluded prior left.trace leftKept
      have clear : last.excluded = first.entryExcluded := by
        apply Finset.Subset.antisymm _ (first.entered.trans grows)
        exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp newFailure)
      have recorded := setup.commitRecovery_local_failed_window_recorded baseline focal first
        prior committing choice (by obtain ⟨move, chosen, fails, _⟩ := failed
                                    exact ⟨move, chosen, fails⟩)
        fuel positive distance.le left leftSupported
      have constant : mean left = excludedPayoff focal := by
        calc
          mean left = expect (finish left) (fun _ => excludedPayoff focal) :=
            expect_congr_on_support fun final continued =>
              setup.commitRecovery_failed_commit_window_payoff (altered (PMF.pure choice))
                baseline first prior committing fuel distance focal left leftSupported
                (by rwa [state]) recorded utility excludedPayoff final continued
          _ = _ := expect_constant _ _
      rw [constant]
      rw [← expect_constant (finish right) (excludedPayoff focal)]
      apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
      intro final continued
      exact setup.commitRecovery_terminal_payoff_lower utility excludedPayoff below focal final
        (setup.commitRecoveryModel.runBehavioralTerminalFrom_support_terminal
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
  have split (currentLaw : PMF (setup.commitRecoveryModel.Choice focal
      (setup.commitRecoveryModel.infoOf focal prior))) :=
    setup.commitRecoveryNormalizedTrembledProfile_local_terminal_window omission
      omissionNonnegative omissionBounded bad badNonnegative badBounded values certificate focal
      first prior committing fuel distance currentLaw
  rw [split (PMF.pure choice), split law]
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
    expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  exact averaged

open Classical in
/-- At a genuine original commitment information fiber, the ACTUAL
conditional value of the fixed accepted-failure action is no greater than
that of any domain law. The same actual belief is integrated on both sides;
no ordinary-representative belief or future optimality is assumed. -/
theorem commitRecovery_normalized_accepted_failure_conditional_value_le
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (prescribed : ∀ who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        baseline who (setup.commitRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (focal : Player) (site : setup.commitRecoveryModel.InformationSite focal)
    (committing : site.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (law : PMF (setup.CommitRecoveryValueChoice focal site.1)) :
    let certificate := setup.commitRecoveryProtocol_bounded.wellFoundedHistories
    let context := assessment.continuationContext certificate site
      (setup.commitRecoveryPayoff utility excludedPayoff focal)
    context.value ((assessment.strategy focal).withLaw site.1
        (PMF.pure (setup.commitRecoveryFailureChoice focal site.1 false))) ≤
      context.value ((assessment.strategy focal).withLaw site.1 (law.map Subtype.val)) := by
  classical
  let : Finite setup.commitRecoveryProtocol.History := setup.commitRecovery_finite_history finite
  intro certificate context
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    InformationModel.BehavioralAssessment.continuationContext_value]
  apply expect_bind_mono_on_support _ _ _ _ (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)
  intro history _supported
  have actual := setup.commitRecoveryNormalizedTrembledProfile_local_terminal_of_prescribed
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded values assessment
    prescribed certificate focal site.1
  rw [actual _ history.1, actual _ history.1]
  have active := InformationModel.InformationSite.active
    (M := setup.commitRecoveryModel) site history
  rcases history with ⟨⟨state, trace⟩, atSite⟩
  have currentCommit := committing
  rw [← atSite, setup.commitRecovery_atCommit_info] at currentCommit
  cases state with
  | none => cases currentCommit
  | some first =>
      have proper : setup.commitRecoveryActive focal site.1.1.1 := by
        rw [← atSite]
        change setup.commitRecoveryActive focal
          (setup.commitRecoverySignals.withOwnPlayRecall.infoOf focal trace).1.1
        rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current]
        simpa only [commitRecoveryActive, commitRecoveryPrivate, commitRecoveryPublic,
          Option.map_some, Option.elim_some, ProtocolState.actor_observe_eq,
          commitRecoveryProtocol, CommitRecoveryState.Active] using active
      have failed : ∃ move,
          (setup.commitRecoveryFailureChoice focal site.1 false).val = some move ∧
          move.action.IsFailure ∧ move.missing = false := by
        cases selected : (setup.commitRecoveryFailureChoice focal site.1 false).val with
        | none =>
            have legal := (setup.commitRecoveryFailureChoice focal site.1 false).property
            change setup.commitRecoveryMenu focal site.1 _ at legal
            rw [selected] at legal
            exact (legal proper).elim
        | some move =>
            have result := setup.commitRecoveryFailureChoice_spec focal site.1 false move selected
            exact ⟨move, rfl, result.1, by simpa only [Bool.and_false] using result.2⟩
      apply setup.commitRecoveryNormalizedTrembledProfile_accepted_failure_value_le omission
        omissionNonnegative omissionBounded bad badNonnegative badBounded values finite utility
        excludedPayoff below first trace currentCommit focal site.1 atSite _ failed
      intro selected supported
      obtain ⟨value, _offered, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      cases chosen : value.val.val with
      | none => rfl
      | some move =>
          simpa only [CommitRecoveryMove.missed, chosen, Option.elim_some] using
            (value.property move chosen).1

end Vegas.SourceProgram.Setup
