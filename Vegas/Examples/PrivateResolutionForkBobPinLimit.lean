/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkBobCompiler
import Vegas.Game.AsyncServiceOriginalCompletion

/-! # The actual prescribed Bob LOW limit

The source sequence and native pin equation below are the same fields returned
by original completion. Bob's normalized lottery comes from that genuine source
sequence. Actual typed observation and own-history decoding identify the local
compiler input; native posterior weights are never replaced by source beliefs.
The concrete builder's service certificate and input-fiber identification must
still supply these deterministic resources.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability Filter

private abbrev bobPinModel (service : AsyncServiceSpec Player simpleExpr) :=
  ReactiveApplication.ResponseMenu.information
    (service.bounds.menu (runtime service.setup) service.leaks)
    (initialLaw service.setup) service.horizon service.scheduler

private abbrev bobPinSourceModel (service : AsyncServiceSpec Player simpleExpr) :=
  service.setup.informationModel (CommitmentInterface.values service.setup.program)

/-- The original completion's exact compatible pins force LOW at Bob's
decoded TRUE input. Earlier native waits remain in recall and do not reset
the source policy. No rationality or native posterior premise is imposed. -/
theorem original_completion_bob_low_limit
    (service : AsyncServiceSpec Player simpleExpr) (setupEq : service.setup = setup)
    (sourceSequence : Nat → (bobPinSourceModel service).BehavioralAssessment)
    (sourceTarget : (bobPinSourceModel service).BehavioralAssessment)
    (sourceConverges : InformationModel.BehavioralAssessmentConvergesPointwise
      sourceSequence sourceTarget)
    (sourceStrategy : HEq sourceTarget.strategy sourceEquilibriumProfile)
    (weight : Nat → Player → (application service.setup service.leaks).Info → ℝ)
    (weightNonnegative : ∀ n who info, 0 ≤ weight n who info)
    (weightSmall : ∀ n who info, weight n who info ≤ 1)
    (delta : Nat → ℝ) (deltaNonnegative : ∀ n, 0 ≤ delta n)
    (deltaSmall : ∀ n, delta n ≤ 1) (deltaVanishes : Tendsto delta atTop (nhds 0))
    (sequence : Nat → (bobPinModel service).BehavioralAssessment)
    (target : (bobPinModel service).BehavioralAssessment)
    (index : Nat → Nat) (increasing : StrictMono index)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise
      (fun n => sequence (index n)) target)
    (pinned : ∀ n who (site : (bobPinModel service).InformationSite who),
      service.sourceCompatibleInfo who site.1 →
        (sequence n).strategy who site.1 =
          mix (delta n) (deltaNonnegative n) (deltaSmall n)
            ((service.bounds.menu (runtime service.setup) service.leaks).uniformPolicy
              (initialLaw service.setup) service.horizon service.scheduler who site.1)
            (mix (weight n who site.1) (weightNonnegative n who site.1)
              (weightSmall n who site.1)
              (((service.bounds.menu (runtime service.setup) service.leaks).restrictPolicy
                (initialLaw service.setup) service.horizon service.scheduler who
                (application service.setup service.leaks).silentPolicy) site.1)
              (service.effectiveImmediateComparator (normalizeDisclosureProfile
                service.setup.program [] (Revelations.initial service.setup.context)
                (service.setup.decodeBehavioralProfile
                  (CommitmentInterface.values service.setup.program) (sourceSequence n).strategy))
                who site.1)))
    (site : (bobPinModel service).InformationSite bob)
    (compatible : service.sourceCompatibleInfo bob site.1)
    (weightVanishes : Tendsto (fun n => weight n bob site.1) atTop (nhds 0))
    (remaining : Nat) (execution : (application service.setup service.leaks).Execution)
    (trace : ((service.bounds.menu (runtime service.setup) service.leaks).protocol
      (initialLaw service.setup) service.horizon service.scheduler).Trace
        (some ⟨remaining, some bob, execution⟩))
    (observed : site.1 = some (execution.recall bob,
      execution.observe (application service.setup service.leaks) bob))
    (event : (graph service.setup).EventId) (address : HEq event bobResolution)
    (outputEq : (graph service.setup).outputLayout event = .publication BaseTy.bool)
    (turn : execution.application.publicView.ownTurn? bob = some event)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks
      (execution.recall bob) event = false)
    (observation : (toEventGraph setup.program).PlayerObservation bob)
    (observationEq : HEq (service.setup.eventGraph.fromModeObservation .sequential bob
      ((graph service.setup).playerObserve bob execution.application.config)) observation)
    (high : Bool)
    (decoded : decodeObservation? bob bobRefs observation.store =
      some (sourceObserve bob (sourceAliceDone high true).state))
    (history : decodeCompletions setup.program observation.ownActions = [])
    (lowChoice : (bobPinModel service).Choice bob site.1)
    (selected : lowChoice.1 = some ((runtime service.setup).canonicalServiceDecision
      service.leaks bob (execution.recall bob)
      (execution.observe (application service.setup service.leaks) bob) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) false))) :
    target.strategy bob site.1 = PMF.pure lowChoice := by
  rcases service with ⟨actualSetup, leaks, bounds, values, initialValues, capacity, horizon,
    scheduler, delay, bound, contract, timely, initialFinite, leaksFinite, schedulerFinite⟩
  dsimp only at setupEq
  subst actualSetup
  have addressEq : event = bobResolution := eq_of_heq address
  subst event
  have viewed : setup.eventGraph.fromModeObservation .sequential bob
      ((graph setup).playerObserve bob execution.application.config) = observation :=
    eq_of_heq observationEq
  have sourceEq : sourceTarget.strategy = sourceEquilibriumProfile := eq_of_heq sourceStrategy
  let service : AsyncServiceSpec Player simpleExpr :=
    ⟨setup, leaks, bounds, values, initialValues, capacity, horizon, scheduler, delay, bound,
      contract, timely, initialFinite, leaksFinite, schedulerFinite⟩
  rcases site with ⟨info, represented⟩
  dsimp only at observed
  subst info
  let site : (bobPinModel service).InformationSite bob :=
    ⟨some (execution.recall bob, execution.observe (application setup leaks) bob), represented⟩
  let profiles n := normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context)
    (setup.decodeBehavioralProfile sourceAdmission (sourceSequence n).strategy)
  have immediateLimit := service.sourceCompatibleInfo_immediate_limit_from_pins profiles
    weight weightNonnegative weightSmall delta deltaNonnegative deltaSmall deltaVanishes
    sequence target index increasing converges pinned bob site compatible weightVanishes
  let response (choice : (bobPinModel service).Choice bob site.1) :=
    choice.1.getD (⟨none⟩ : (application setup leaks).Action)
  have physical (n : Nat) :
      (service.effectiveImmediateComparator (profiles n) bob site.1).map response =
        (sourceChoiceDisclosure bob (sourceBobInput true)
          ((sourceSequence n).strategy bob (sourceBobInput true))).map fun decision =>
            (runtime setup).canonicalServiceDecision leaks bob (execution.recall bob)
              (execution.observe (application setup leaks) bob) bobResolution decision := by
    have normalizedPermitted : (profiles n bob).Admitted setup.program sourceAdmission := by
      trivial
    have actual := service.sourceCompatibleInfo_immediate_decoded_response (profiles n) bob
      normalizedPermitted remaining execution trace compatible bobResolution
      turn unrecorded
    rw [sourceServiceCanonicalPolicy_at_event setup leaks _ bob execution bobResolution
      turn (by rfl), viewed] at actual
    rw [normalized_compiled_bob_choice (sourceSequence n).strategy observation high true
      decoded history] at actual
    simpa only [bobPinModel, service, response, profiles, site] using actual
  have sourceLimit := normalized_decoded_bob_low_converges sourceSequence sourceTarget
    sourceConverges sourceEq high
  have originalLimit : PMFConvergesPointwise
      (fun n => sourceChoiceDisclosure bob (sourceBobInput true)
        ((sourceSequence n).strategy bob (sourceBobInput true))) (PMF.pure false) := by
    simpa only [normalized_decoded_bob_choice] using sourceLimit
  have rendered := (originalLimit.map fun decision =>
    (runtime setup).canonicalServiceDecision leaks bob (execution.recall bob)
      (execution.observe (application setup leaks) bob) bobResolution decision).subseq increasing
  simp only [PMF.pure_map] at rendered
  have pureResponse : (PMF.pure lowChoice).map response = PMF.pure
      ((runtime setup).canonicalServiceDecision leaks bob (execution.recall bob)
        (execution.observe (application setup leaks) bob) bobResolution false) := by
    simp only [PMF.pure_map, response, selected, Option.getD_some]
    rfl
  have physicalLimit : PMFConvergesPointwise
      (fun n => (service.effectiveImmediateComparator (profiles (index n)) bob site.1).map response)
      ((PMF.pure lowChoice).map response) := by
    rw [pureResponse]
    intro action
    simp only [physical]
    exact rendered action
  have targetResponse : (target.strategy bob site.1).map response =
      (PMF.pure lowChoice).map response := (immediateLimit.map response).unique physicalLimit
  have injective : Function.Injective response := by
    intro first second same
    have firstLegal : ∃ action ∈ (bounds.menu (runtime setup) leaks).actions bob
        (execution.recall bob) (execution.observe (application setup leaks) bob),
        first.1 = some action := by
      simpa only [bobPinModel, service, ReactiveApplication.ResponseMenu.information,
        site, Set.mem_ofPred_eq] using first.2
    have secondLegal : ∃ action ∈ (bounds.menu (runtime setup) leaks).actions bob
        (execution.recall bob) (execution.observe (application setup leaks) bob),
        second.1 = some action := by
      simpa only [bobPinModel, service, ReactiveApplication.ResponseMenu.information,
        site, Set.mem_ofPred_eq] using second.2
    obtain ⟨firstAction, _firstAllowed, firstEq⟩ := firstLegal
    obtain ⟨secondAction, _secondAllowed, secondEq⟩ := secondLegal
    apply Subtype.ext
    rw [firstEq, secondEq]
    apply congrArg some
    simpa only [response, firstEq, secondEq, Option.getD_some] using same
  exact pmf_map_injective injective targetResponse

end Vegas.PrivateResolutionFork
