/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingTailDecision
import Vegas.Examples.CommitSeedSignallingUnopenedContinuation
import Vegas.Examples.CommitSeedSignallingFinishedPayoff
import Vegas.Examples.CommitSeedSignallingOwnContinuation

/-! # A recorded publication WAIT cannot be rescued by the assessed continuation -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

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

/-- The literal current WAIT has payoff minus one under the original assessed
continuation. Sequential rationality is used solely for count-charge reflection,
not to prescribe any future response. -/
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
      (fun state => netPayoff state owner) = -1 := by
  classical
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon scheduler remaining execution
    owner ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds owner _ _)
  let next : app.Execution := execution.respond app owner ⟨none⟩
  let history : countedProtocol.History := ⟨some ⟨remaining, none, next⟩, responded⟩
  let profile := countedAssessmentProfile assessment
  have law := raw_terminal_state_law assessment.strategy
    (countedInRaw.history initial horizon scheduler history)
  change (rawModel.runBehavioralTerminalFrom canonicalCertificate assessment.strategy
      (countedInRaw.history initial horizon scheduler history)).map History.state =
    app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, next⟩) at law
  rw [← law, expect_map, ← expect_constant _ (-1 : ℝ)]
  apply expect_congr_on_support
  intro final supported
  have zero := raw_equilibrium_counted_terminal_charge_zero assessment equilibrium history final
    supported owner
  have retained := supported
  rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
    (rawMenu.bounded initial horizon scheduler)] at retained
  have sameRun := (countedInRaw.actionRestriction initial horizon scheduler).runFrom_law
    profile assessment.strategy (raw_equilibrium_extends_counted assessment equilibrium)
      (2 * horizon + 1) history
  change (countedModel.runBehavioralFrom profile (2 * horizon + 1) history).map
      (countedInRaw.history initial horizon scheduler) =
    rawModel.runBehavioralFrom assessment.strategy (2 * horizon + 1)
      (countedInRaw.history initial horizon scheduler history) at sameRun
  rw [← sameRun, PMF.support_map] at retained
  obtain ⟨countedFinal, reached, same⟩ := retained
  have sourceLaw := countedMenu.run_eq_finish initial horizon scheduler profile
    (2 * horizon + 1) history (by
      have bound := app.trace_bound initial horizon scheduler
        (countedMenu.toRawTrace initial horizon scheduler history.trace)
      exact (Nat.le_add_left _ _).trans bound)
  have physical : countedFinal.state ∈
      ((countedModel.runBehavioralFrom profile (2 * horizon + 1) history).map
        History.state).support := by
    rw [PMF.support_map]
    exact ⟨countedFinal, reached, rfl⟩
  rw [sourceLaw] at physical
  change countedFinal.state ∈ (((PMF.pure next).bind
    (app.runRounds scheduler (countedMenu.decodeProfile initial horizon scheduler profile)
      remaining)).map app.finished).support at physical
  rw [PMF.pure_bind] at physical
  obtain ⟨after, rounds, stateEq⟩ := PMF.support_map .. ▸ physical
  dsimp only [next] at rounds
  have excluded := counted_publication_wait_excluded profile remaining execution after owner
    trace retired request rounds
  have state := congrArg History.state same
  change countedFinal.state = final.state at state
  have finalEq : final.state = some (⟨0, none, after⟩ : app.Control) :=
    state.symm.trans stateEq.symm
  change basePayoff final.state owner -
    TerminalAudit.charge app.stateTraffic audit final.state owner * deposit owner = -1
  rw [zero, zero_mul, sub_zero, finalEq]
  exact phaseExclusionBase_of_excluded setup .concurrentReveals runtime leaks utility
    excludedPayoff ⟨0, none, after⟩ owner excluded

private theorem silence_raw (owner : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) : (⟨none⟩ : app.Action) ∈ rawMenu.actions owner past view :=
  ((PhaseCount.mem_onePacketActions runtime leaks bounds owner past view ⟨none⟩).mp
    (PhaseCount.silence_onePacket runtime leaks bounds owner past view)).1

/-- With a clean focal past, an unsubmitted current publication WAIT has value
minus one in the actual raw equilibrium continuation. Foreign histories remain
unrestricted throughout the terminal runner. -/
theorem raw_publication_wait_assessed_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : rawProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (clean : OwnPermitted owner execution)
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (unsubmitted : ∀ message ∈ execution.network.inputs, message.sender = owner →
      PhaseCount.event? message.payload ≠
        some ⟨execution.application.attempt, revealEvent owner⟩) :
    expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, execution.respond app owner ⟨none⟩⟩))
      (fun state => netPayoff state owner) = -1 := by
  classical
  obtain ⟨responded⟩ := rawMenu.trace_respond initial horizon scheduler remaining execution owner
    ⟨none⟩ trace (silence_raw owner _ _)
  let next : app.Execution := execution.respond app owner ⟨none⟩
  let history : rawProtocol.History := ⟨some ⟨remaining, none, next⟩, responded⟩
  have cleanNext : OwnPermitted owner next := ownPermitted_respond owner owner execution
    ⟨none⟩ clean (fun _ => rfl)
  have law := raw_terminal_state_law assessment.strategy history
  change (rawModel.runBehavioralTerminalFrom canonicalCertificate assessment.strategy history).map
      History.state = app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (some ⟨remaining, none, next⟩) at law
  rw [← law, expect_map, ← expect_constant _ (-1 : ℝ)]
  apply expect_congr_on_support
  intro final supported
  have zero := raw_equilibrium_own_clean_terminal_charge_zero assessment equilibrium owner history
    final cleanNext supported
  have physical : final.state ∈ ((rawModel.runBehavioralTerminalFrom canonicalCertificate
      assessment.strategy history).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, supported, rfl⟩
  rw [law] at physical
  change final.state ∈ (((PMF.pure next).bind
    (app.runRounds scheduler (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      remaining)).map app.finished).support at physical
  rw [PMF.pure_bind] at physical
  obtain ⟨after, rounds, stateEq⟩ := PMF.support_map .. ▸ physical
  dsimp only [next] at rounds
  have excluded := unsubmitted_recorded_publication_excluded rawMenu silence_raw
    assessment.strategy remaining execution after owner trace retired request unsubmitted rounds
  change basePayoff final.state owner -
    TerminalAudit.charge app.stateTraffic audit final.state owner * deposit owner = -1
  rw [zero, zero_mul, sub_zero, ← stateEq]
  exact phaseExclusionBase_of_excluded setup .concurrentReveals runtime leaks utility
    excludedPayoff ⟨0, none, after⟩ owner excluded

end Vegas.Examples.CommitSeedSignalling
