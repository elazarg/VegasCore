/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.BobConformance
import Vegas.Examples.MonitoredGuessing.EnforcementPayoffs

/-! # The inferred receiver deposit bounds every addressed extra response

The payoff table fixes the deposit before choosing strategies. At the retained
receiver checkpoint every addressed effective action outside the source menu is
included and publicly charged. The comparison permits arbitrary later raw
policies and every declared result table.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem bob_extra_addressed_le_lower (table : PayoffTable)
    (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph)
    (available : (⟨some (.submit submission)⟩ : nativeApp.Action) ∈
      effectiveMenu.actions bob [] ((quietBob bit).observe nativeApp bob))
    (extra : (⟨some (.submit submission)⟩ : nativeApp.Action) ∉
      restrictedMenu.actions bob [] ((quietBob bit).observe nativeApp bob))
    (addressed : submission.call.packet.event? nativeGraph = some bobPublication)
    (rest : List (ServiceInstruction nativeGraph)) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (.includeLatest bobPublication bob :: rest) (bobSubmission bit submission)).expect
        (fun execution => Enforcement.executionUtility table execution bob) ≤
      Enforcement.payoffLower table bob := by
  rw [runInteractionPlan, bob_addressed_included players bit submission addressed,
    FinDist.pure_bind]
  apply FinDist.expect_le_of_forall
  intro final supported
  apply Enforcement.detected_bob_utility_le table final
  exact bob_ledger_plan_persists players rest (bobIncluded bit submission) final
    (extra_addressed_bob_detected bit submission available extra addressed) supported

/-- This bound is uniform over the source continuation: it applies to every
clean mixture of source results, including deliberately withholding profiles. -/
theorem bob_extra_addressed_le_clean_outcomes (table : PayoffTable)
    (outcomes : FinDist Results) (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph)
    (available : (⟨some (.submit submission)⟩ : nativeApp.Action) ∈
      effectiveMenu.actions bob [] ((quietBob bit).observe nativeApp bob))
    (extra : (⟨some (.submit submission)⟩ : nativeApp.Action) ∉
      restrictedMenu.actions bob [] ((quietBob bit).observe nativeApp bob))
    (addressed : submission.call.packet.event? nativeGraph = some bobPublication)
    (rest : List (ServiceInstruction nativeGraph)) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (.includeLatest bobPublication bob :: rest) (bobSubmission bit submission)).expect
        (fun execution => Enforcement.executionUtility table execution bob) ≤
      outcomes.expect (fun result => (table result bob : ℝ)) :=
  (bob_extra_addressed_le_lower table players bit submission available extra addressed rest).trans
    (Enforcement.lower_le_expect table bob outcomes)

end Vegas.Examples.MonitoredGuessing.Restricted
