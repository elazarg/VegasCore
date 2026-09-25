/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingAssessment
import VegasTests.MonitoredGuessingNativeDepth
import VegasTests.MonitoredGuessingNativeOutcome
import GameTheoryExtensions.Analysis.Protocol.FixedDepthBayes

/-! # Native receiver beliefs on the prescribed silent path

The receiver's prior is recovered from the actual initialized prefix law and
Bayes consistency at its positive-reach information site. No posterior is
assigned independently of the native assessment's common trembling sequence.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

/-- State beliefs at the quiet information site follow from the genuine
native prefix law. Keeping states rather than hand-picked history witnesses
retains every history that the assessment gives positive probability. -/
theorem quiet_native_state_belief (assessment : nativeModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent nativeAntichain)
    (prefixLaw : (nativeModel.runBehavioral assessment.strategy 8).map History.state =
      (FinDist.uniformOfFintype (α := Bool)).map (fun bit => (quietBobHistory bit).state)) :
    (assessment.belief bob quietBobSite).map (fun history => history.1.state) =
      (FinDist.uniformOfFintype (α := Bool)).map (fun bit => (quietBobHistory bit).state) := by
  classical
  have depth := native_bob_information_depth quietBobSite
  let law := nativeModel.runBehavioral assessment.strategy 8
  let information : Set nativeArena.History :=
    {history | nativeModel.infoOf bob history.trace = quietBobSite.1}
  have seen (history : nativeArena.History) (supported : history ∈ law.support) :
      history ∈ information := by
    have stateSupported : history.state ∈ (law.map History.state).support := by
      rw [FinDist.support_map]
      exact ⟨history, supported, rfl⟩
    rw [prefixLaw, FinDist.support_map] at stateSupported
    obtain ⟨bit, _, same⟩ := stateSupported
    change nativeModel.infoOf bob history.trace = quietBobSite.1
    exact (nativeMenu.info nativeInitialLaw nativeHorizon nativeScheduler bob history.trace).trans
      ((congrArg (nativeApp.observe bob) same).symm.trans (quiet_bob_info bit))
  have mass : law.probOf information = 1 := by
    rw [← FinDist.expect_indicator_eq_probOf]
    calc
      law.expect (fun history => if history ∈ information then (1 : ℝ) else 0) =
          law.expect (fun _ => 1) := by
        apply FinDist.expect_congr
        intro history supported
        rw [ite_eq_left (seen history supported)]
      _ = 1 := FinDist.expect_const _ _
  have informationMass : nativeModel.informationMass assessment.strategy bob quietBobSite = 1 :=
    (nativeModel.informationMass_eq_fixedDepth_probOf assessment.strategy bob quietBobSite 8
      depth).trans mass
  have positive : 0 < nativeModel.informationMass assessment.strategy bob quietBobSite := by
    rw [informationMass]
    norm_num
  obtain ⟨witness, supported⟩ := law.support_nonempty
  have meet : ∃ history ∈ information, history ∈ law.support :=
    ⟨witness, seen witness supported, supported⟩
  have bayes : assessment.belief bob quietBobSite =
      nativeModel.bayesBelief assessment.strategy bob quietBobSite
        (nativeAntichain bob quietBobSite) positive := by
    apply FinDist.ext_of_prob
    intro history
    rw [nativeModel.bayesBelief_prob]
    exact consistent.isBayesConsistent nativeAntichain bob quietBobSite positive history
  have conditioned := nativeModel.bayesBelief_map_eq_condOn assessment.strategy bob
    quietBobSite 8 depth (nativeAntichain bob quietBobSite) positive meet
  rw [← bayes] at conditioned
  have unchanged : law.condOn information meet = law := by
    apply FinDist.ext_of_prob
    intro history
    rw [FinDist.prob_condOn, mass, div_one]
    by_cases member : history ∈ information
    · rw [ite_eq_left member]
    · rw [ite_eq_right member]
      exact (FinDist.prob_eq_zero_iff.mpr fun supported => member (seen history supported)).symm
  rw [unchanged] at conditioned
  have projected := congrArg (fun histories : FinDist nativeArena.History =>
    histories.map History.state) conditioned
  simpa only [FinDist.map_comp, Function.comp_def] using projected.trans prefixLaw

/-- Every consistent native assessment retaining the prescribed sender and
watcher has the genuine fair-state posterior at Bob's quiet decision. Bob's
policies at other, potentially noisy information sites remain unrestricted. -/
theorem quiet_native_state_belief_of_prescribed (assessment : nativeModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent nativeAntichain)
    (alicePolicy : assessment.strategy alice = nativeAliceBehavior)
    (watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior) :
    (assessment.belief bob quietBobSite).map (fun history => history.1.state) =
      (FinDist.uniformOfFintype (α := Bool)).map (fun bit => (quietBobHistory bit).state) := by
  apply quiet_native_state_belief assessment consistent
  exact quiet_bob_history_law assessment.strategy alicePolicy watcherPolicy

theorem quiet_native_context (assessment : nativeModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent nativeAntichain)
    (alicePolicy : assessment.strategy alice = nativeAliceBehavior)
    (watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior)
    (deposit : ℝ) (alternative : nativeModel.BehavioralPolicy bob) :
    (assessment.continuationContext quietBobSite
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)).value
        alternative =
      (FinDist.uniformOfFintype (α := Bool)).expect (fun bit =>
        (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
          (nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
            (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob
              alternative)) (quietBobHistory bit).state).expect (nativeUtility deposit bob)) := by
  rw [native_context_value, quiet_native_state_belief_of_prescribed assessment consistent
    alicePolicy watcherPolicy, FinDist.expect_map]

end VegasTests.MonitoredGuessing
