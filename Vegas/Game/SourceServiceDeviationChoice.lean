/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ObservationRecall
import Vegas.Game.ServiceDeviationTraffic
import Vegas.Game.SourceServiceTurnPolicy
import Vegas.Game.SourceServiceCompletion
import Interaction.ReactiveMixtureRounds

/-! # Actual disclosure choices and a deviating player at a ready event

A successor view retains the preceding full view and the owner's actual
optional disclosure decision. An already defaulted owner records no new choice.
At a sole ready event owned by the deviator or by chance, all other first-turn
clients remain silent until the event completes.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- The owner's successor view determines its prior view and the actual
optional choice. Boolean choices are recovered only for active callbacks. -/
theorem reveal_owner_view_reflects {Γ : SourceCtx Player L} {name : VarId}
    {who : Player} {payload : L.Ty} (published : VarId)
    (selected : HasVar Γ name (.commitment who payload))
    (left right : Config Player L Γ) (first second : Bool)
    (same : (revealSuccessor published selected left first).view who =
      (revealSuccessor published selected right second).view who) :
    left.view who = right.view who ∧
      (if who ∈ left.defaulted then none else some first) =
        (if who ∈ right.defaulted then none else some second) := by
  have prior := reveal_view_reflects who published selected left right first second same
  refine ⟨prior, ?_⟩
  have defaultsEq := congrArg DecisionView.defaulted prior
  change left.defaulted = right.defaulted at defaultsEq
  by_cases inactive : who ∈ left.defaulted
  · simp only [← defaultsEq, ite_eq_left inactive]
  · have rightActive : who ∉ right.defaulted := by rwa [← defaultsEq]
    have last := congrArg
      (fun view : DecisionView who ((published, .publication payload) :: Γ) =>
        view.history.getLast?) same
    simp only [Config.view, revealSuccessor, inactive, rightActive, ite_false,
      Function.update_self, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq, OwnAction.reveal.injEq, true_and] at last
    simp only [ite_eq_right inactive, ite_eq_right rightActive, last]

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- While an event is ready alone, no player but its actor has a turn. -/
theorem ownTurn?_none_of_alone {event : (serviceGraph setup mode).EventId}
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (state : EventGraphRuntime.State (serviceGraph setup mode))
    (ready : state.config.cut.Ready event) (player : Player)
    (other : (serviceGraph setup mode).actor? event ≠ some player) :
    state.publicView.ownTurn? player = none := by
  cases turn : state.publicView.ownTurn? player with
  | none => rfl
  | some current =>
      obtain ⟨seen, owned⟩ := PublicView.ownTurn?_spec _ player current turn
      have same := alone _ current ready ((state.publicView_eventReady current).mp seen)
      subst same
      exact (other owned).elim

/-- Readiness at a pending event is preserved until that event completes. -/
theorem round_ready_of_pending
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {event : (serviceGraph setup mode).EventId}
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    {before after : (serviceApplication setup mode deadline leaks).Execution}
    (ready : before.application.config.cut.Ready event)
    (reached : after ∈ ((serviceApplication setup mode deadline leaks).round scheduler
      players before).support) (pending : event ∉ after.application.config.cut.completed) :
    after.application.config.cut.Ready event := by
  rw [reactive_round_config_eq_of_pending (serviceRuntime setup mode deadline) leaks scheduler
    players event before after (fun other otherReady => alone _ other ready otherReady)
    pending reached]
  exact ready

/-- Until the sole ready event of the deviator or of chance completes,
first-turn clients of the other players remain silent. -/
theorem runUntil_deviation_focal
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (event : (serviceGraph setup mode).EventId)
    (focal : (serviceGraph setup mode).actor? event = none ∨ (serviceGraph setup mode).actor?
        event = some who)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event → cut.Ready
        other → other = event) (count : Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (holds : event ∉ execution.application.config.cut.completed →
      execution.application.config.cut.Ready event) :
    (serviceApplication setup mode deadline leaks).runUntil scheduler
    (Function.update
      (serviceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) profile) who deviation)
    (fun final => event ∈ final.application.config.cut.completed) count execution =
    (serviceApplication setup mode deadline leaks).runUntil scheduler
    (focalPlayers setup leaks who deviation)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  let app := serviceApplication setup mode deadline leaks
  apply app.runUntil_congr_of_agree scheduler _ _ _
    (fun current => event ∉ current.application.config.cut.completed →
      current.application.config.cut.Ready event)
  · intro current currentHolds running command _ middle moved player active
    by_cases same : player = who
    · subst same
      simp only [focalPlayers, Function.update_self]
    · simp only [focalPlayers, Function.update_of_ne same]
      have activateIs : command = .activate player := by
        cases command with
        | activate actor => cases active; rfl
        | «include» => cases active
        | application => cases active
        | wait => cases active
      subst activateIs
      have sameApp := activation_application setup leaks current middle player moved
      have idle : (middle.observe app player).application.publicView.ownTurn? player = none := by
        change middle.application.publicView.ownTurn? player = none
        rw [sameApp]
        apply ownTurn?_none_of_alone alone _ (currentHolds running) player
        rcases focal with actorless | owned
        · rw [actorless]
          exact fun impossible => by cases impossible
        · rw [owned]
          exact fun equal => same (Option.some.inj equal).symm
      simp only [serviceTurnPolicy, idle]
  · intro current currentHolds running next reached
    exact round_ready_of_pending alone (currentHolds running) reached
  · exact holds

end Vegas
