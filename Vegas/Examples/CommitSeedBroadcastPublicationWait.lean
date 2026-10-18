/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastTailDecision
import Vegas.Examples.CommitSeedBroadcastUnopenedContinuation
import Vegas.Examples.CommitSeedBroadcastNativeContinuation

/-! # A recorded publication WAIT cannot be rescued by the assessed continuation -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement

private theorem unopened_after_recorded_round (menu : app.ResponseMenu)
    (silence : ∀ owner past view, (⟨none⟩ : app.Action) ∈ menu.actions owner past view)
    (profile : ∀ owner, (menu.information initial horizon scheduler).BehavioralPolicy owner)
    (remaining : Nat) (before after : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace (some ⟨remaining + 1, none, before⟩))
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (retired : coordinate.attempt ≠ originalAttempt)
    (entry : app.PlayerEntry) (member : entry ∈ before.recall owner)
    (previous : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (valid : owner ∈ before.application.current.excluded ∨ Unopened owner coordinate before)
    (supported : after ∈ (app.round scheduler
      (menu.decodeProfile initial horizon scheduler profile) before).support) :
    (owner ∈ after.application.current.excluded ∨ Unopened owner coordinate after) ∧
      entry ∈ after.recall owner := by
  classical
  obtain ⟨command, selected, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨observed, moved, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  obtain ⟨pending⟩ := menu.trace_environment initial horizon scheduler remaining before
    observed command trace selected moved
  have validObserved : owner ∈ observed.application.current.excluded ∨
      Unopened owner coordinate observed := by
    rcases valid with excluded | unopened
    · exact Or.inl ((phaseApplication_exclusion_monotone runtime leaks).environmentStep before
        observed command moved excluded)
    · exact Or.inr (unopened_environment owner coordinate before observed command unopened moved)
  have observedMember : entry ∈ observed.recall owner := by
    rw [app.environmentStep_recall before observed command moved]
    exact member
  cases acting : command.actor? app with
  | none =>
      change after ∈ (app.resume _ (command.actor? app) observed).support at resumed
      rw [acting] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      exact ⟨validObserved, observedMember⟩
  | some actor =>
      change after ∈ (app.resume _ (command.actor? app) observed).support at resumed
      rw [acting] at resumed
      obtain ⟨response, _chosen, rfl⟩ := PMF.support_map .. ▸ resumed
      refine ⟨?_, (app.respond_recall_prefix observed actor owner response).sublist.subset
        observedMember⟩
      rcases validObserved with excluded | unopened
      · exact Or.inl ((phaseApplication_exclusion_monotone runtime leaks).respond observed
          actor response excluded)
      · by_cases same : actor = owner
        · subst actor
          rcases unopened.2.2 with excluded | request
          · exact Or.inl ((phaseApplication_exclusion_monotone runtime leaks).respond observed
              owner response excluded)
          · rw [acting] at pending
            exact (tail_callback_no_previous_request menu silence remaining observed owner pending
                coordinate retired request entry observedMember previous).elim
        · exact Or.inr (unopened_respond_other owner coordinate observed actor response same
            unopened)

private theorem unopened_after_recorded_run (menu : app.ResponseMenu)
    (silence : ∀ owner past view, (⟨none⟩ : app.Action) ∈ menu.actions owner past view)
    (profile : ∀ owner, (menu.information initial horizon scheduler).BehavioralPolicy owner)
    (remaining count : Nat) (before after : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + count, none, before⟩))
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (retired : coordinate.attempt ≠ originalAttempt)
    (entry : app.PlayerEntry) (member : entry ∈ before.recall owner)
    (previous : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (valid : owner ∈ before.application.current.excluded ∨ Unopened owner coordinate before)
    (supported : after ∈ (app.runRounds scheduler
      (menu.decodeProfile initial horizon scheduler profile) count before).support) :
    owner ∈ after.application.current.excluded ∨ Unopened owner coordinate after := by
  induction count generalizing before with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact valid
  | succ count ih =>
      obtain ⟨middle, stepped, finished⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      have covered (actor : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
          (response : app.Action) (chosen : response ∈
            (menu.decodeProfile initial horizon scheduler profile actor past view).support) :
          response ∈ menu.actions actor past view :=
        menu.decode_embedPolicy_covered initial horizon scheduler actor (profile actor)
          past view response chosen
      obtain ⟨middleTrace⟩ := menu.trace_round initial horizon scheduler _ covered
        (remaining + count) before middle trace stepped
      have next := unopened_after_recorded_round menu silence profile (remaining + count) before
        middle trace owner coordinate retired entry member previous valid stepped
      exact ih middle middleTrace next.2 next.1 finished

private theorem unsubmitted_recorded_publication_excluded (menu : app.ResponseMenu)
    (silence : ∀ owner past view, (⟨none⟩ : app.Action) ∈ menu.actions owner past view)
    (profile : ∀ owner, (menu.information initial horizon scheduler).BehavioralPolicy owner)
    (remaining : Nat) (execution after : app.Execution) (owner : Player)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (unsubmitted : ∀ message ∈ execution.network.inputs, message.sender = owner →
      PhaseCount.event? message.payload ≠
        some ⟨execution.application.attempt, revealEvent owner⟩)
    (supported : after ∈ (app.runRounds scheduler
      (menu.decodeProfile initial horizon scheduler profile) remaining
        (execution.respond app owner ⟨none⟩)).support) :
    owner ∈ after.application.current.excluded := by
  classical
  let coordinate : CommitAttemptEvent graph :=
    ⟨execution.application.attempt, revealEvent owner⟩
  obtain ⟨responded⟩ := menu.trace_respond initial horizon scheduler remaining execution
    owner ⟨none⟩ trace (silence owner _ _)
  let next : app.Execution := execution.respond app owner ⟨none⟩
  let entry : app.PlayerEntry := ⟨execution.observe app owner, ⟨none⟩, none⟩
  have member : entry ∈ next.recall owner := by
    dsimp only [next]
    simp only [ReactiveApplication.Execution.respond, ite_true]
    change entry ∈ execution.recall owner ++ [entry]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have valid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩
    (menu.toRawTrace initial horizon scheduler trace)
  have previous : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate :=
    (execution.application.requests_publicView valid owner coordinate).mpr request
  have retained := app.retained_envelopes_mem_inputs execution
    (app.history_provenance initial horizon scheduler
      (menu.toRawTrace initial horizon scheduler trace))
    (app.history_inputRecall initial horizon scheduler
      (menu.toRawTrace initial horizon scheduler trace))
  have unopened : Unopened owner coordinate next :=
    ⟨valid, retained.mono (fun message present => unsubmitted message present), Or.inr request⟩
  have respondedZero : (menu.protocol initial horizon scheduler).Trace
      (some ⟨0 + remaining, none, next⟩) := by
    simpa only [Nat.zero_add, next] using responded
  have final := unopened_after_recorded_run menu silence profile 0 remaining next after
    respondedZero owner coordinate retired entry member previous (Or.inr unopened) supported
  rcases final with excluded | stillUnopened
  · exact excluded
  · have covered (actor : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
        (response : app.Action) (chosen : response ∈
          (menu.decodeProfile initial horizon scheduler profile actor past view).support) :
        response ∈ menu.actions actor past view :=
      menu.decode_embedPolicy_covered initial horizon scheduler actor (profile actor)
        past view response chosen
    obtain ⟨last⟩ := menu.trace_runRounds initial horizon scheduler _ covered 0 remaining
      next after respondedZero supported
    have complete := scheduler_completesPlay ⟨0, none, after⟩
      (menu.toRawTrace initial horizon scheduler last) ⟨rfl, rfl⟩
    rcases stillUnopened.2.2 with excluded | stillReady
    · exact excluded
    · exact (stillReady.2.2.1.1 (by rw [complete]; exact Finset.mem_univ _)).elim

/-- A publication WAIT leaves its original request with no subsequent callback
at which to submit it. The actual assessed continuation therefore ends with
exclusion, including at histories having zero assessed probability. -/
theorem counted_publication_wait_excluded
    (profile : ∀ owner, countedModel.BehavioralPolicy owner)
    (remaining : Nat) (execution after : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (supported : after ∈ (app.runRounds scheduler
      (countedMenu.decodeProfile initial horizon scheduler profile) remaining
        (execution.respond app owner ⟨none⟩)).support) :
    owner ∈ after.application.current.excluded := by
  exact unsubmitted_recorded_publication_excluded countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) profile remaining execution after owner
      trace retired request
      (counted_tail_callback_unsubmitted remaining execution owner trace _ retired request)
      supported

/-- Omitting the sole protected publication opportunity has the fixed loss
under the actual raw equilibrium tail, derived through its counted runner. -/
theorem counted_publication_wait_assessed_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩) :
    expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, execution.respond app owner ⟨none⟩⟩))
      (fun state => netPayoff state owner) = -(3 / 2) := by
  classical
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon scheduler remaining execution
    owner ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds owner _ _)
  let history : countedProtocol.History :=
    ⟨some ⟨remaining, none, execution.respond app owner ⟨none⟩⟩, responded⟩
  have law := counted_assessment_finish_eq assessment equilibrium history
  change app.finish initial horizon scheduler
    (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
      history.state = _ at law
  rw [← law]
  simp only [history, ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind,
    expect_map]
  rw [← expect_constant _ (-(3 / 2) : ℝ)]
  apply expect_congr_on_support
  intro after reached
  have excluded := counted_publication_wait_excluded (countedAssessmentProfile assessment)
    remaining execution after owner trace retired request reached
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon scheduler _
    (fun who past view action supported => countedMenu.decode_embedPolicy_covered
      initial horizon scheduler who (countedAssessmentProfile assessment who)
        past view action supported) 0 remaining (execution.respond app owner ⟨none⟩) after
      (by simpa only [Nat.zero_add] using responded) reached
  change netPayoff (app.finished after) owner = -(3 / 2)
  rw [counted_endpoint_payoff after finalTrace owner, ite_eq_left excluded]

end Vegas.Examples.CommitSeedBroadcast
