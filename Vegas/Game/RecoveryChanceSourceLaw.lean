/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceChancePhase
import Vegas.Game.RecoveryStoppedSourceLaw
import Vegas.Pending.ExclusionNativeFailure

/-! # Chance phases under actual recovery completion -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem clear_of_actorless_completion
    {before after : EventGraphRuntime.State (graph setup)}
    (clear : PublicExclusionRecord (RecoveryState.mk before ∅))
    (moved : CompletionStep before after)
    (actorless : ∀ event, before.config.cut.Ready event → (graph setup).actor? event = none) :
    PublicExclusionRecord (RecoveryState.mk after ∅) := by
  refine ⟨clear.receipts.step moved, fun owner => ⟨?_, ?_⟩⟩
  · intro member
    simp at member
  · rintro ⟨query, owned, failed⟩
    have oldFailed : before.PublicFailure query := by
      rcases moved with ⟨same, accepted, _⟩ | ⟨event, ready, action, member, _, only⟩
      · exact (State.PublicFailure.congr query (by rw [same]) (by rw [same])
          (congrFun accepted _)).mp failed
      · have different : query ≠ event := by
          intro same
          rw [same, actorless event ready] at owned
          cases owned
        exact (State.PublicFailure.of_step_of_ne member
          (fun field changed => (only field changed).2) different).mp failed
    exact (clear.excluded owner).mpr ⟨query, owned, oldFailed⟩

private theorem chance_round_clear
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none)
    (alone : ∀ cut : (graph setup).order.Cut, ∀ other,
      cut.Ready event → cut.Ready other → other = event)
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅))
    (next : (application setup leaks).Execution)
    (moved : next ∈ ((application setup leaks).round scheduler players execution).support) :
    PublicExclusionRecord (RecoveryState.mk next.application ∅) := by
  let app := application setup leaks
  unfold ReactiveApplication.round at moved
  rw [PMF.mem_support_bind_iff] at moved
  obtain ⟨command, _, moved⟩ := moved
  unfold ReactiveApplication.dispatch at moved
  rw [PMF.mem_support_bind_iff] at moved
  obtain ⟨middle, stepped, resumed⟩ := moved
  have middleClear : PublicExclusionRecord (RecoveryState.mk middle.application ∅) := by
    apply clear_of_actorless_completion clear
      ((reactiveApplication_completionStep (runtime setup) leaks).environmentStep
        execution middle command stepped)
    intro other otherReady
    rw [alone _ other ready otherReady]
    exact actorless
  change next ∈ (app.resume players (command.actor? app) middle).support at resumed
  cases active : command.actor? app with
  | none =>
      rw [active] at resumed
      change next ∈ (PMF.pure middle).support at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      exact middleClear
  | some who =>
      rw [active] at resumed
      change next ∈ (app.invoke players who middle).support at resumed
      rw [ReactiveApplication.invoke, PMF.mem_support_map_iff] at resumed
      obtain ⟨response, _, rfl⟩ := resumed
      rcases response with ⟨transmission⟩
      cases transmission with
      | none => exact middleClear
      | some material => exact middleClear.submit who material

/-- While a chance event is ready alone, running until its completion cannot
create public exclusion, regardless of the players' responses. -/
theorem chance_runUntil_clear
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (event : (graph setup).EventId) (actorless : (graph setup).actor? event = none)
    (alone : ∀ cut : (graph setup).order.Cut, ∀ other,
      cut.Ready event → cut.Ready other → other = event) :
    ∀ count (execution : (application setup leaks).Execution),
      execution.application.config.cut.Ready event →
      PublicExclusionRecord (RecoveryState.mk execution.application ∅) →
      ∀ stopped ∈ ((application setup leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).support,
        PublicExclusionRecord (RecoveryState.mk stopped.application ∅) := by
  intro count
  induction count with
  | zero =>
      intro execution _ clear stopped supported
      change stopped ∈ (PMF.pure execution).support at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact clear
  | succ count ih =>
      intro execution ready clear stopped supported
      simp only [ReactiveApplication.runUntil, ready.1, ↓reduceIte,
        PMF.mem_support_bind_iff] at supported
      obtain ⟨next, moved, reached⟩ := supported
      have nextClear := chance_round_clear scheduler players execution event ready actorless alone
        clear next moved
      by_cases completed : event ∈ next.application.config.cut.completed
      · rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ next completed,
          PMF.mem_support_pure_iff] at reached
        subst reached
        exact nextClear
      · have same : next.application.config = execution.application.config := by
          rcases round_configStep setup leaks scheduler players execution next moved with
            same | ⟨other, otherReady, action, member⟩
          · exact same
          · have which := alone _ other ready otherReady
            subst other
            apply (completed ?_).elim
            rw [execution.application.config.step_cut event otherReady action
              next.application.config
              member, EventOrder.Cut.mem_complete]
            exact Or.inl rfl
        exact ih next (same ▸ ready) nextClear stopped reached

variable {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat} {scheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon scheduler)

include initialized nativeLaw completes in
/-- A chance phase from a genuine source boundary completes with its graph law
under actual recovery completion. Public clarity throughout the phase is derived
from the actorless ready event, rather than assumed for its future endpoints. -/
theorem recovery_chance_completion_configLaw
    (players : Player → (application setup leaks).Policy)
    (event : (graph setup).EventId) (actorless : (graph setup).actor? event = none)
    (execution : (application setup leaks).Execution)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
        (some ⟨horizon - execution.environmentRecall.length, none, execution⟩))
    (ordered : execution.application.config.cut.IsPrefix event.val)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅))
    (action : (graph setup).Action event) :
    ((application setup leaks).runUntilHorizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).map
        (fun stopped => stopped.application.config) =
      execution.application.config.step event
        ((ready_iff_rank setup _ event.val ordered event).mpr rfl) action := by
  let app := application setup leaks
  let nativeScheduler := RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler
  have ready := (ready_iff_rank setup _ event.val ordered event).mpr rfl
  have alone : ∀ cut : (graph setup).order.Cut, ∀ other,
      cut.Ready event → cut.Ready other → other = event :=
    fun cut other eventReady otherReady =>
      ready_unique (setup := setup) cut otherReady eventReady
  apply chance_runUntil nativeScheduler players event actorless execution.application.config
    alone ready action _ execution rfl
  intro stopped reached
  rcases app.runUntilHorizon_stopped nativeScheduler players _ horizon
      (horizon - execution.environmentRecall.length) execution stopped (by omega) reached with
    done | spent
  · exact done
  · have stoppedClear := chance_runUntil_clear nativeScheduler players event actorless alone
      (horizon - execution.environmentRecall.length) execution ready clear stopped reached
    obtain ⟨used, within, rounds, length⟩ := app.runUntil_runRounds nativeScheduler players _ _
      execution stopped reached
    have budget : horizon - stopped.environmentRecall.length + used =
        horizon - execution.environmentRecall.length := by omega
    have atStart : ((application setup leaks).protocol (initialLaw setup) horizon
        nativeScheduler).Trace
          (some ⟨horizon - stopped.environmentRecall.length + used, none, execution⟩) := by
      rwa [budget]
    obtain ⟨stoppedTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon nativeScheduler
      players (horizon - stopped.environmentRecall.length) used execution stopped atStart rounds
    rw [← nativeLaw] at stoppedTrace
    have terminal := Recovery.CompletesPlay.clear_native (runtime setup) leaks initialized
      completes _ stoppedTrace stoppedClear (by
        change horizon - stopped.environmentRecall.length = 0 ∧ _
        exact ⟨by omega, rfl⟩)
    change stopped.application.config.cut.completed = Finset.univ at terminal
    rw [terminal]
    exact Finset.mem_univ _

include initialized nativeLaw completes in
/-- The source continuation law is harmonic across an actual chance phase,
under recovery completion and arbitrary raw continuation policies. -/
theorem recovery_chance_sourceContinuation [Finite Player]
    (players : Player → (application setup leaks).Policy)
    (event : (graph setup).EventId) (actorless : (graph setup).actor? event = none)
    (execution : (application setup leaks).Execution)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
        (some ⟨horizon - execution.environmentRecall.length, none, execution⟩))
    (profile : BehavioralProfile setup.program)
    (residual : SourceResidual setup profile event.val execution.application.config)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅)) :
    (((application setup leaks).runUntilHorizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
        (fun stopped => sourceContinuation setup profile (event.val + 1)
          stopped.application.config)) =
      sourceContinuation setup profile event.val execution.application.config := by
  let ready := (ready_iff_rank setup _ event.val residual.checkpoint.ordered event).mpr rfl
  let action := ((graph setup).nodes event).actionOfActorNone actorless
  have configLaw := recovery_chance_completion_configLaw initialized nativeLaw completes players
    event actorless execution trace residual.checkpoint.ordered bounded clear action
  obtain ⟨law, sourceLaw, _policy, _effective, _disclosing⟩ :=
    SourceResidual.head_law leaks residual event rfl ready
  have fixed : law.bind (fun choice =>
      (execution.application.config.step event ready choice).bind
        (sourceContinuation setup profile (event.val + 1))) =
      (execution.application.config.step event ready action).bind
        (sourceContinuation setup profile (event.val + 1)) := by
    have same : (fun choice =>
        (execution.application.config.step event ready choice).bind
          (sourceContinuation setup profile (event.val + 1))) =
        (fun _ => (execution.application.config.step event ready action).bind
          (sourceContinuation setup profile (event.val + 1))) := by
      funext choice
      rw [((graph setup).nodes event).action_eq_of_actor_none actorless choice action]
    rw [same, PMF.bind_const]
  rw [sourceLaw, fixed, ← configLaw, PMF.bind_map]
  rfl

include initialized nativeLaw completes in
/-- Source continuation value has zero drift across a chance phase governed by
actual recovery completion, for every beneficiary and bounded source payoff. -/
theorem recovery_chance_sourceValue [Finite Player]
    (players : Player → (application setup leaks).Policy)
    (event : (graph setup).EventId) (actorless : (graph setup).actor? event = none)
    (execution : (application setup leaks).Execution)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
        (some ⟨horizon - execution.environmentRecall.length, none, execution⟩))
    (profile : BehavioralProfile setup.program)
    (residual : SourceResidual setup profile event.val execution.application.config)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅))
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup event.val execution.application.config = some point)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (beneficiary : Player) {payoffBound : ℝ}
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout beneficiary| ≤
        payoffBound) :
    expect ((application setup leaks).runUntilHorizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution)
      (fun stopped => expect (sourceContinuation setup profile (event.val + 1)
        stopped.application.config)
        (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout
          beneficiary)) =
      sourcePointValue setup parameter utility excludedPayoff profile beneficiary point := by
  have law := recovery_chance_sourceContinuation initialized nativeLaw completes players event
    actorless execution trace profile residual bounded clear
  have valued := congrArg (fun distribution => expect distribution
    (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout
      beneficiary)) law
  rw [expect_bind_tower_bounded _ _ _ readoutBounded] at valued
  refine valued.trans ?_
  change expect ((setup.continuationLaw profile
    (sourceServicePrefix? setup event.val execution.application.config)).map some) _ = _
  rw [decoded]
  rfl

end Vegas
