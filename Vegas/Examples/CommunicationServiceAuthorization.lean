/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.ReactiveDependencyService
import Vegas.Pending.ReactiveService

/-! # The reserved selector alone does not enforce submission dependencies

In the existing early-opening execution, the binding has since been included.
The latest opening was nevertheless submitted before that dependency settled.
The raw reserved selector still selects it, but the packet carries no readiness
token, so the contract rejects it; the existing public-history monitor excludes
it before inclusion. This checks the selector on the actual fixture, without
asserting that its earlier calendar was the recurring epoch calendar.
-/

noncomputable section

namespace Vegas.Examples.CommunicationServiceAuthorization

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime
open ReactiveEarlyOpening

theorem raw_reserved_selects_premature :
    runtime.reactiveLatest leaks 1 () ((included false false).observeEnvironment app) =
      .include prematureOpeningEnvelope.id := rfl

/-- The premature opening has no readiness token, so its inclusion leaves the
disclosure undecided. -/
theorem contract_rejects_premature :
    (State.config ((included false false).includePending app
      prematureOpeningEnvelope.id).application).outputs 1 = none := by
  have found : (included false false).network.lookup prematureOpeningEnvelope.id =
      some prematureOpeningEnvelope := rfl
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]
  rw [reactiveApplication_handle_of_not_tokenValid runtime leaks _ _
    (WitnessedPacket.tokenValid_none _ _), included_state false false (by simp)]
  rfl

theorem original_submission_remains_unauthorized :
    ¬(included false false).AuthorizedAtSubmission app
      (runtime.submissionDependencyCondition leaks) prematureOpeningEnvelope :=
  premature_opening_unauthorized_after_binding

theorem monitored_reserved_waits :
    app.authorizedCommand dependencyCondition (included false false).environmentRecall
      ((included false false).observeEnvironment app)
      (runtime.reactiveLatest leaks 1 () ((included false false).observeEnvironment app)) =
        .wait := by
  classical
  rw [raw_reserved_selects_premature]
  have denied : ¬ app.SubmissionPermitted dependencyCondition
      (included false false).environmentRecall prematureOpeningEnvelope := by
    change ¬∃ observation,
      app.submissionObservation? (included false false).environmentRecall
          prematureOpeningEnvelope.id = some observation ∧
        dependencyCondition observation prematureOpeningEnvelope
    have observed : app.submissionObservation? (included false false).environmentRecall
        prematureOpeningEnvelope.id = some initialState.publicView := rfl
    rw [observed]
    rintro ⟨observation, same, permitted⟩
    cases Option.some.inj same
    exact List.not_mem_nil ((dependencyCondition_iff _ _).mp permitted rfl)
  change (if app.SubmissionPermitted dependencyCondition
    (included false false).environmentRecall prematureOpeningEnvelope then
      ReactiveApplication.Command.include prematureOpeningEnvelope.id else .wait) = _
  split
  · contradiction
  · rfl

end Vegas.Examples.CommunicationServiceAuthorization
