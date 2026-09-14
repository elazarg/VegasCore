/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidatePolicy
import Vegas.Compile.SealedCandidateSettlement
import VegasTests.SealedPayout
import Interaction.MessageApplicationLaws

/-! # Candidate selection and failed openings for a checked source

These runs use the ordinary compiler's commit/reveal rules and the shared
pending-message interpreter. Candidate identities differ from both source-site
numbers and message serials. The programmed payout is the public result.
-/

noncomputable section

namespace VegasTests.SealedCandidates

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
open GameTheory.Math.Probability SealedPublicSettlement

abbrev runtime := supported.resolvingRuntime none 2
abbrev app := runtime.candidateApplication

private def initial : app.State := State.initial app runtime.candidateInitial

private def prepareBoth := [
  (.privateCommand 0 ⟨(10, some false)⟩ : app.Action),
  .privateCommand 0 ⟨(11, some true)⟩]

private def selectedState : app.State :=
  { initial with
    application :=
      ⟨(CommitmentCandidates.empty.prepare 0 10 (some false)).prepare 0 11 (some true),
        runtime.refresh false { runtime.candidateInitial.visible with
          events := [.accepted 0 (0, 11)] }⟩
    pool := ((initial.pool.submit 0 (.commitment 0 (0, 11))).2.includePending (0, 0)).state
    receipts := [((0, 0), true)] }

/-- Preparing two candidates does not bind the source site. Acceptance selects
the second candidate, independently of preparation order and message serial. -/
theorem selecting_second_candidate :
    app.run (prepareBoth ++ [.submit 0 (.commitment 0 (0, 11)), .include (0, 0)]) initial =
      FinDist.pure selectedState := by
  simp only [prepareBoth, List.cons_append, List.nil_append,
    MessageApplication.run, MessageApplication.step, FinDist.pure_bind]
  rfl

/-- A different prepared candidate cannot replace the accepted handle. -/
theorem selected_handle_cannot_be_replaced :
    runtime.candidateHandle selectedState.application
      ⟨(0, 1), .commitment 0 (0, 10)⟩ = none := by decide

/-- Only the accepted candidate can open this source site, even when another
candidate has a valid opening in the same owner's catalog. -/
theorem wrong_candidate_cannot_open :
    runtime.candidateHandle selectedState.application
      ⟨(0, 1), .opening 1 (0, 10) (some false)⟩ = none := by decide

/-- Opening the selected candidate produces the programmed successful payout. -/
theorem selected_candidate_payout :
    (app.run [
      .submit 0 (.opening 1 (0, 11) (some true)), .include (0, 1)] selectedState).map
        (fun next => (compilation.publicPayout? next.application.visible.events).map
          (fun payout => payout 0)) =
      FinDist.pure (some (7 : Int)) := by
  simp only [MessageApplication.run, MessageApplication.step,
    FinDist.pure_bind, FinDist.map_pure]
  exact congrArg FinDist.pure (public_payout_after_opening (some true))

private def unopenableState : app.State :=
  { initial with
    application :=
      ⟨CommitmentCandidates.empty.accept (0, 17),
        runtime.refresh false { runtime.candidateInitial.visible with
          events := [.accepted 0 (0, 17)] }⟩
    pool := ((initial.pool.submit 0 (.commitment 0 (0, 17))).2.includePending (0, 0)).state
    receipts := [((0, 0), true)] }

/-- The target accepts an unprepared candidate and records a successful
inclusion receipt. It does not claim that the sender has an opening. -/
theorem unopenable_candidate_accepted :
    app.run [.submit 0 (.commitment 0 (0, 17)), .include (0, 0)] initial =
      FinDist.pure unopenableState := by
  simp only [MessageApplication.run, MessageApplication.step, FinDist.pure_bind]
  rfl

/-- Preparing after acceptance cannot revive the unopenable candidate. The
failed opening is rejected, and the same deadline mechanism pays source quit. -/
theorem unopenable_candidate_quit_payout :
    (app.run [
      .privateCommand 0 ⟨(17, some true)⟩,
      .submit 0 (.opening 1 (0, 17) (some true)), .include (0, 1),
      .environment ⟨()⟩, .environment ⟨()⟩] unopenableState).map
        (fun next => (next.application.service.lookup (0, 17),
          next.receipts, (compilation.publicPayout? next.application.visible.events).map
            (fun payout => payout 0))) =
      FinDist.pure (CommitmentCandidate.unopenable (Value := Value),
        [((0, 0), true), ((0, 1), false)], some (-3 : Int)) := by
  simp only [MessageApplication.run, MessageApplication.step,
    app, runtime, SealedResolution.candidateApplication, SealedResolution.host,
    FinDist.pure_bind, FinDist.map_pure]
  congr 1
  exact congrArg (fun payout => (CommitmentCandidate.unopenable (Value := Value),
    [((0, 0), true), ((0, 1), false)], payout)) (public_payout_after_opening none)

/-- The compiler still prepares an opaque canonical candidate in this host;
it does not compile an immediate cleartext public choice. -/
theorem compiled_policy_prepares :
    compilation.compileCandidatePolicy none 2 0 (SealedPayout.alwaysTrueProfile 0)
      [] (State.observe app initial 0) =
        FinDist.pure (.privateCommand ⟨(0, some true)⟩) := by
  change supported.commitCommand 0 _ (node 0) _ rfl [] _ = _
  unfold SealedFragment.commitCommand
  simp only [ChoiceEncoding.cachedValue_nil]
  change (ToEventGraph.compileSourcePolicy core source.core.fresh
    (ToEventGraph.BuildState.fromInitial
      (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)) rfl 0
    (SealedPayout.alwaysTrueProfile 0) (node 0) _ rfl _).map _ = _
  erw [ToEventGraph.compileSourcePolicy_at core source.core.fresh _ rfl 0
    (SealedPayout.alwaysTrueProfile 0) _ (.here _ _) (node 0) rfl rfl rfl]
  simp only [ToEventGraph.compileSourceDecision, SealedPayout.alwaysTrueProfile,
    VegasCore.commit.noConfusion, id_eq, FinDist.map_pure]
  rfl

/-- A concrete checked source instantiates the full honest execution law for
every adaptive candidate environment and finite invocation schedule. No
preparation or message-safety hypothesis is supplied by the test. -/
theorem compiled_policy_host_law (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation SealedPublicSettlement.Player)) :
    ∃ reference : runtime.messageApplication.EnvironmentPolicy,
      app.runPolicies
        (fun who => compilation.compileCandidatePolicy none 2 who
          (SealedPayout.alwaysTrueProfile who)) environment schedule
        (PolicyExecution.initial app initial) =
      (runtime.messageApplication.runPolicies
        (fun who => compilation.compileResolvingPolicy none 2 who
          (SealedPayout.alwaysTrueProfile who)) reference schedule
        (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
          runtime.candidateExecution := by
  obtain ⟨reference, rfl⟩ := runtime.candidateEnvironmentPolicy_surjective environment
  exact ⟨reference,
    (compilation.candidatePolicies_law none 2 SealedPayout.alwaysTrueProfile
      reference schedule).symm⟩

/-- Honest-host equality must not be generalized to arbitrary submissions:
even a canonical handle is accepted unprepared only in the candidate host. -/
theorem unprepared_host_difference :
    (runtime.candidateHandle runtime.candidateInitial
      ⟨(0, 0), .commitment 0 (0, 0)⟩).isSome = true ∧
    runtime.handle runtime.initial ⟨(0, 0), .commitment 0 (0, 0)⟩ = none := by
  decide

private def failedOpeningPlayers : SealedPublicSettlement.Player → app.PlayerPolicy :=
  fun _ history _ =>
  FinDist.pure <| match history.length with
  | 0 => .submit (.commitment 0 (0, 17))
  | 1 => .privateCommand ⟨(17, some true)⟩
  | 2 => .submit (.opening 1 (0, 17) (some true))
  | _ => .wait

private def failedOpeningEnvironment : app.EnvironmentPolicy := fun history _ =>
  FinDist.pure <| match history.length with
  | 0 => .include (0, 0)
  | 1 => .include (0, 1)
  | _ => .application ⟨()⟩

private def failedOpeningSchedule : List (@Invocation SealedPublicSettlement.Player) :=
  [.player 0, .environment, .player 0, .player 0,
    .environment, .environment, .environment]

private def failedOpeningLaw := app.runPolicies failedOpeningPlayers failedOpeningEnvironment
  failedOpeningSchedule (PolicyExecution.initial app initial)

private theorem failedOpeningLaw_complete :
    failedOpeningLaw.map (fun next =>
      (runtime.complete next.native.application.visible,
        next.native.application.visible.timeouts)) = FinDist.pure (true, [1]) := by
  simp [failedOpeningLaw, failedOpeningSchedule, MessageApplication.runPolicies,
    MessageApplication.invoke, failedOpeningPlayers, failedOpeningEnvironment,
    MessageApplication.playerStep, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, PlayerCommand.toAction, EnvironmentPolicyCommand.toAction,
    MessageApplication.step, app, runtime, SealedResolution.candidateApplication,
    SealedResolution.host, PolicyExecution.initial]
  rfl

/-- The source-quitting theorem is instantiated by an actual policy execution:
an unopenable commitment is accepted, late preparation and opening fail, and
the reveal expires. Completion and timeout ownership are proved, not assumed. -/
theorem failed_opening_policy_has_source_quit :
    ∃ next ∈ failedOpeningLaw.support,
      ∃ final : VEnv simpleExpr (sourceTerminalCtx core),
        SmallStep.Star ⟨source.core.Γ, source.core.env, core⟩
          ⟨sourceTerminalCtx core, final, .ret (sourceTerminalPayoffs core)⟩ ∧
        core.Chooses (ty := .option .bool) 0 (none : Value) final ∧
        compilation.publicPayout? next.native.application.visible.events =
          some (evalPayoffs (sourceTerminalPayoffs core) final) := by
  obtain ⟨next, hnext⟩ := failedOpeningLaw.support_nonempty
  have hm : (runtime.complete next.native.application.visible,
      next.native.application.visible.timeouts) ∈
      (failedOpeningLaw.map (fun next =>
        (runtime.complete next.native.application.visible,
          next.native.application.visible.timeouts))).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [failedOpeningLaw_complete, FinDist.mem_support_pure] at hm
  obtain ⟨final, hsource, hchoice, hpayout⟩ := compilation.candidate_publicPayout_source_choice
    none 2 failedOpeningPlayers failedOpeningEnvironment failedOpeningSchedule next hnext
    (congrArg Prod.fst hm) (node 1) 0
    ((congrArg (fun status : Bool × List Nat => 1 ∈ status.2) hm).mpr (by simp))
    (Or.inr ⟨node 0, _, rfl, rfl⟩)
  exact ⟨next, hnext, final, hsource, hchoice, hpayout⟩

end VegasTests.SealedCandidates
