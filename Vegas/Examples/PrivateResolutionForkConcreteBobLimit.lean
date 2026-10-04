/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkBobPinLimit
import Vegas.Examples.PrivateResolutionForkBobObservation
import Vegas.Examples.PrivateResolutionForkSpec

/-! # The prescribed LOW limit at the actual Bob turn

The actual bounded service and raw history supply Bob's ready event, empty
recall and literal compiler observation. An actual successful Alice output
therefore identifies Bob's source TRUE input without a source-policy or
posterior assumption. The same completion pins then force the native LOW
limit. Incoming history weights and rationality are separate obligations.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability Filter

private abbrev concreteBobModel :=
  (bounds.menu (runtime setup) leaks).information (initialLaw setup) horizon scheduler

/-- The exact pins returned by original completion force the evidence-free
LOW response at every actual compatible Bob turn after Alice's successful
publication. All local decoding and availability facts come from that trace. -/
theorem concrete_original_completion_bob_low_limit
    (sourceSequence : Nat → sourceModel.BehavioralAssessment)
    (sourceTarget : sourceModel.BehavioralAssessment)
    (sourceConverges : InformationModel.BehavioralAssessmentConvergesPointwise
      sourceSequence sourceTarget)
    (sourceStrategy : sourceTarget.strategy = sourceEquilibriumProfile)
    (weight : Nat → Player → app.Info → ℝ)
    (weightNonnegative : ∀ n who info, 0 ≤ weight n who info)
    (weightSmall : ∀ n who info, weight n who info ≤ 1)
    (delta : Nat → ℝ) (deltaNonnegative : ∀ n, 0 ≤ delta n)
    (deltaSmall : ∀ n, delta n ≤ 1) (deltaVanishes : Tendsto delta atTop (nhds 0))
    (sequence : Nat → concreteBobModel.BehavioralAssessment)
    (target : concreteBobModel.BehavioralAssessment)
    (index : Nat → Nat) (increasing : StrictMono index)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise
      (fun n => sequence (index n)) target)
    (pinned : ∀ n who (site : concreteBobModel.InformationSite who),
      service.sourceCompatibleInfo who site.1 →
        (sequence n).strategy who site.1 =
          mix (delta n) (deltaNonnegative n) (deltaSmall n)
            ((bounds.menu (runtime setup) leaks).uniformPolicy
              (initialLaw setup) horizon scheduler who site.1)
            (mix (weight n who site.1) (weightNonnegative n who site.1)
              (weightSmall n who site.1)
              (((bounds.menu (runtime setup) leaks).restrictPolicy
                (initialLaw setup) horizon scheduler who app.silentPolicy) site.1)
              (service.effectiveImmediateComparator (normalizeDisclosureProfile
                setup.program [] (Revelations.initial setup.context)
                (setup.decodeBehavioralProfile sourceAdmission (sourceSequence n).strategy))
                who site.1)))
    (site : concreteBobModel.InformationSite bob)
    (compatible : service.sourceCompatibleInfo bob site.1)
    (weightVanishes : Tendsto (fun n => weight n bob site.1) atTop (nhds 0))
    (remaining : Nat) (execution : app.Execution)
    (trace : ((bounds.menu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).Trace (some ⟨remaining, some bob, execution⟩))
    (observed : site.1 = some (execution.recall bob, execution.observe app bob))
    (published : (outputRef setup.program aliceResolution).get?
      execution.application.config.store = some (.success unitValue)) :
    ∃ lowChoice : concreteBobModel.Choice bob site.1,
      lowChoice.1 = some (⟨some ⟨⟨.withhold bobResolution, none⟩, .none⟩⟩ : app.Action) ∧
        target.strategy bob site.1 = PMF.pure lowChoice := by
  classical
  let control : app.Control := ⟨remaining, some bob, execution⟩
  have raw := (bounds.menu (runtime setup) leaks).toRawTrace
    (initialLaw setup) horizon scheduler trace
  have ready := bob_raw_ready control raw rfl
  have turn : execution.application.publicView.ownTurn? bob = some bobResolution :=
    ownTurn?_of_ready setup execution.application ready rfl
  have recalled := (bob_raw_decision_resources control raw rfl).2.2.1
  have unrecorded : (runtime setup).eventRecorded leaks (execution.recall bob)
      bobResolution = false := by
    rw [recalled]
    rfl
  obtain ⟨high, decoded, history⟩ :=
    bob_compiler_observation_of_history control raw rfl published
  let action : app.Action := ⟨some ⟨⟨.withhold bobResolution, none⟩, .none⟩⟩
  have canonical : (runtime setup).canonicalServiceDecision leaks bob (execution.recall bob)
      (execution.observe app bob) bobResolution false = action := by
    exact (runtime setup).canonicalServiceDecision_resolution_false leaks bob
      (execution.recall bob) (execution.observe app bob) bobResolution bob BaseTy.bool
      bobInitialBinding [] rfl bob_resolution_code (by rfl)
  have available : action ∈ (bounds.menu (runtime setup) leaks).actions bob
      (execution.recall bob) (execution.observe app bob) := by
    apply (bounds.menu_mem (runtime setup) leaks bob _ _ action).mpr
    refine ⟨⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩
    simp only [action, ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none,
      EvidenceRequest.normalize_none]
  rcases site with ⟨info, represented⟩
  dsimp only at observed
  subst info
  let site : concreteBobModel.InformationSite bob :=
    ⟨some (execution.recall bob, execution.observe app bob), represented⟩
  let lowChoice : concreteBobModel.Choice bob site.1 :=
    ⟨some action, action, available, rfl⟩
  refine ⟨lowChoice, rfl, ?_⟩
  exact original_completion_bob_low_limit service rfl sourceSequence sourceTarget
    sourceConverges (heq_of_eq sourceStrategy) weight weightNonnegative weightSmall
    delta deltaNonnegative deltaSmall deltaVanishes sequence target index increasing
    converges pinned site compatible weightVanishes remaining execution trace rfl
    bobResolution (HEq.rfl) rfl turn unrecorded
    (setup.eventGraph.fromModeObservation .sequential bob
      ((graph setup).playerObserve bob execution.application.config)) (HEq.rfl)
    high decoded history lowChoice (by
      change some action = some ((runtime setup).canonicalServiceDecision leaks bob
        (execution.recall bob) (execution.observe app bob) bobResolution false)
      exact congrArg some canonical.symm)

end Vegas.PrivateResolutionFork
