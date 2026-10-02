/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.Assessment
import Vegas.Examples.MonitoredGuessing.NativeDepth
import Vegas.Examples.MonitoredGuessing.NativeOutcome
import GameTheory.Analysis.Protocol.BeliefTransport
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity
import GameTheoryExtensions.Math.Probability.Support

/-! # Native receiver beliefs on the prescribed silent path

The receiver's prior is recovered from the actual initialized prefix law and
Bayes consistency at its positive-reach information site. No posterior is
assigned independently of the native assessment's common trembling sequence.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

/-- State beliefs at the quiet information site follow from the genuine
native prefix law. Keeping states rather than hand-picked history witnesses
retains every history that the assessment gives positive probability. -/
theorem quiet_native_state_belief (assessment : nativeModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent nativeAntichain)
    (prefixLaw : (nativeModel.runBehavioral assessment.strategy 7).map History.state =
      (PMF.uniformOfFintype Bool).map (fun bit => (quietBobHistory bit).state)) :
    (assessment.belief bob quietBobSite).map (fun history => history.1.state) =
      (PMF.uniformOfFintype Bool).map (fun bit => (quietBobHistory bit).state) := by
  classical
  have depth := native_bob_information_depth quietBobSite
  let law := nativeModel.runBehavioral assessment.strategy 7
  let information : Set nativeArena.History :=
    {history | nativeModel.infoOf bob history.trace = quietBobSite.1}
  have seen (history : nativeArena.History) (supported : history ∈ law.support) :
      history ∈ information := by
    have stateSupported : history.state ∈ (law.map History.state).support := by
      rw [PMF.support_map]
      exact ⟨history, supported, rfl⟩
    rw [prefixLaw, PMF.support_map] at stateSupported
    obtain ⟨bit, _, same⟩ := stateSupported
    change nativeModel.infoOf bob history.trace = quietBobSite.1
    exact (nativeMenu.info nativeInitialLaw nativeHorizon nativeScheduler bob history.trace).trans
      ((congrArg (nativeApp.observe bob) same).symm.trans (quiet_bob_info bit))
  have conditioned := assessment.belief_map_eq_run_of_full_reach nativeModel nativeAntichain
    consistent bob quietBobSite 7 depth seen
  have projected := congrArg (fun histories : PMF nativeArena.History =>
    histories.map History.state) conditioned
  simpa only [PMF.map_comp, Function.comp_def] using projected.trans prefixLaw

/-- Every consistent native assessment retaining the prescribed sender and
watcher has the genuine fair-state posterior at Bob's quiet decision. Bob's
policies at other, potentially noisy information sites remain unrestricted. -/
theorem quiet_native_state_belief_of_prescribed (assessment : nativeModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent nativeAntichain)
    (alicePolicy : assessment.strategy alice = nativeAliceBehavior)
    (watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior) :
    (assessment.belief bob quietBobSite).map (fun history => history.1.state) =
      (PMF.uniformOfFintype Bool).map (fun bit => (quietBobHistory bit).state) := by
  apply quiet_native_state_belief assessment consistent
  exact quiet_bob_history_law assessment.strategy alicePolicy watcherPolicy

theorem quiet_native_context (assessment : nativeModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent nativeAntichain)
    (alicePolicy : assessment.strategy alice = nativeAliceBehavior)
    (watcherPolicy : assessment.strategy watcher = nativeWatcherBehavior)
    (charge : ℝ) (alternative : nativeModel.BehavioralPolicy bob) :
    (assessment.truncatedContinuationContext quietBobSite
      (fun history => nativeComparisonUtility charge bob history.state) (2 * nativeHorizon +
        1)).value
        alternative =
      expect (PMF.uniformOfFintype Bool) (fun bit =>
        expect (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
          (nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
            (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob
              alternative)) (quietBobHistory bit).state) (nativeComparisonUtility charge bob))
                := by
  rw [native_context_value, quiet_native_state_belief_of_prescribed assessment consistent
    alicePolicy watcherPolicy, expect_map]
  rfl

end Vegas.Examples.MonitoredGuessing
