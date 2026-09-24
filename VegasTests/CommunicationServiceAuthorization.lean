/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveDependencyService
import Vegas.Pending.ReactiveService

/-! # The reserved selector alone does not enforce submission dependencies

In the existing early-opening execution, the binding has since been included.
The latest opening was nevertheless submitted before that dependency settled.
The raw reserved selector accepts it; the existing public-history monitor
excludes it. This checks the selector on the actual fixture, without asserting
that its earlier calendar was the recurring epoch calendar.
-/

noncomputable section

namespace VegasTests.CommunicationServiceAuthorization

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime
open ReactiveEarlyOpening

theorem raw_reserved_selects_premature :
    runtime.reactiveLatest leaks 1 () ((granted false false).observeEnvironment app) =
      .include prematureOpeningEnvelope.id := rfl

theorem raw_reserved_accepts_premature :
    (State.config ((granted false false).includePending app
      prematureOpeningEnvelope.id).application).outputs 1 = some (.success 1) :=
  early_opening

theorem original_submission_remains_unauthorized :
    ¬(granted false false).AuthorizedAtSubmission app
      (runtime.submissionDependencyCondition leaks) prematureOpeningEnvelope :=
  premature_opening_unauthorized_after_binding

theorem monitored_reserved_waits :
    app.authorizedCommand dependencyCondition (granted false false).environmentRecall
      ((granted false false).observeEnvironment app)
      (runtime.reactiveLatest leaks 1 () ((granted false false).observeEnvironment app)) =
        .wait := by
  classical
  rw [raw_reserved_selects_premature]
  have denied : ¬ app.SubmissionPermitted dependencyCondition
      (granted false false).environmentRecall prematureOpeningEnvelope := by
    change ¬∃ observation,
      app.submissionObservation? (granted false false).environmentRecall
          prematureOpeningEnvelope.id = some observation ∧
        dependencyCondition observation prematureOpeningEnvelope
    have observed : app.submissionObservation? (granted false false).environmentRecall
        prematureOpeningEnvelope.id = some initialState.publicView := rfl
    rw [observed]
    rintro ⟨observation, same, permitted⟩
    cases Option.some.inj same
    exact List.not_mem_nil ((dependencyCondition_iff _ _).mp permitted rfl)
  change (if app.SubmissionPermitted dependencyCondition
    (granted false false).environmentRecall prematureOpeningEnvelope then
      ReactiveApplication.Command.include prematureOpeningEnvelope.id else .wait) = _
  split
  · contradiction
  · rfl

end VegasTests.CommunicationServiceAuthorization
