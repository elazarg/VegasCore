/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Expr.Simple
import Vegas.Compile.EventGraphInputs
import Vegas.Pending.ReactiveRuntime
import Vegas.Game.ServiceRoster

/-! # Automatic completion and roster clock service

A public omission can complete several instructions at one clock value. The
next active owner retains that readiness time as subsequent clock commands run.
The roster scheduler suppresses clock commands for blocks complete at entry.
-/

noncomputable section

namespace VegasTests

open Vegas Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Math.Probability Interaction

private def acceptBinding {Γ : SourceCtx Bool simpleExpr} (owner : Bool) (name : VarId) :
    SourceGuard simpleExpr Γ owner name .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun member => nomatch member

private def consecutiveBindings : SourceProgram Bool simpleExpr [] ∅ :=
  .commit 0 false (by decide) (acceptBinding false 0) <|
  .commit 1 false (by decide) (acceptBinding false 1) <|
  .commit 2 false (by decide) (acceptBinding false 2) <|
  .commit 3 true (by decide) (acceptBinding true 3) <|
  .reveal 4 false 0 (by decide) (.there (.there (.there .here))) (by decide) <|
  .reveal 5 false 1 (by decide) (.there (.there (.there .here))) (by decide) <|
  .reveal 6 false 2 (by decide) (.there (.there (.there .here))) (by decide) <|
  .reveal 7 true 3 (by decide) (.there (.there (.there .here))) (by decide) <|
  .ret []

private abbrev compiled := toEventGraph consecutiveBindings

private def rankedRuntime : EventGraphRuntime compiled where
  deadline event := event.val + 1

private def initialLedger : State compiled :=
  State.initial (encodeInputs (Env.empty (CellVal simpleExpr)))

private abbrev first : compiled.EventId := ⟨0, by decide⟩
private abbrev second : compiled.EventId := ⟨1, by decide⟩
private abbrev third : compiled.EventId := ⟨2, by decide⟩
private abbrev bob : compiled.EventId := ⟨3, by decide⟩

private theorem firstReady : initialLedger.config.cut.Ready first := by decide

private def omission : State compiled :=
  ({ initialLedger with clock := 1 } : State compiled).complete first firstReady none .failure

private theorem secondReady : omission.config.cut.Ready second := by decide

private def afterSecond : State compiled := omission.completeFailure second secondReady

private theorem thirdReady : afterSecond.config.cut.Ready third := by decide

private def afterThird : State compiled := afterSecond.completeFailure third thirdReady

private theorem secondAutomatic : omission.AutomaticReady second := by decide
private theorem thirdAutomatic : afterSecond.AutomaticReady third := by decide
private theorem finalClear : ∀ event, ¬ afterThird.AutomaticReady event := by decide

private theorem drain_step (fuel : Nat) (state : State compiled) (event : compiled.EventId)
    (eligible : state.AutomaticReady event) :
    State.drainFuel (fuel + 1) state =
      State.drainFuel fuel (state.completeAutomatic event eligible) := by
  have existsEvent : ∃ current, state.AutomaticReady current := ⟨event, eligible⟩
  have chosen : Classical.choose existsEvent = event :=
    state.config.cut.ready_unique (Classical.choose_spec existsEvent).1 eligible.1
  rw [State.drainFuel, dite_eq_left existsEvent]
  simp only [chosen]

private theorem exactDrain : omission.drain = afterThird := by
  have remaining : omission.config.remaining = 7 := by decide
  change State.drainFuel omission.config.remaining omission = afterThird
  rw [remaining, drain_step 6 omission second secondAutomatic]
  change State.drainFuel 6 afterSecond = afterThird
  rw [drain_step 5 afterSecond third thirdAutomatic]
  exact State.drainFuel_eq_of_clear 5 afterThird finalClear

private theorem rawExpiry :
    environmentStep rankedRuntime { initialLedger with clock := 1 } (.expire first) =
      PMF.pure omission := by
  exact environmentStep_expire_bind_eq rankedRuntime { initialLedger with clock := 1 }
    first firstReady 0 rfl (by decide) false .bool rfl rfl rfl

private def atClock (clock : Nat) : State compiled := { afterThird with clock }

/-- The actual native expiry/drain exposes Bob's event at clock one. -/
private theorem earlyReadyAfterExpiry
    (leaks : MessageNetwork.ObservationRule Bool (WitnessedPacket compiled)) :
    (rankedRuntime.reactiveApplication leaks).environment
        { initialLedger with clock := 1 } (.expire first) = PMF.pure (atClock 1) := by
  change ((environmentStep rankedRuntime { initialLedger with clock := 1 }
    (.expire first)).map State.drain) = _
  rw [rawExpiry, PMF.pure_map, exactDrain]
  rfl

/-- Remaining automatic work does not advance Bob's readiness timestamp. -/
private theorem earlyReadyMetadata :
    (atClock 1).clock = 1 ∧ (atClock 1).activatedAt bob = some 1 ∧
      (atClock 1).config.cut.Ready bob ∧
      (atClock 1).config.defaulted = ({false} : Finset Bool) := by decide

/-- A clock command increments the native clock while preserving readiness. -/
private theorem clockTick
    (leaks : MessageNetwork.ObservationRule Bool (WitnessedPacket compiled)) (clock : Nat) :
    (rankedRuntime.reactiveApplication leaks).environment (atClock clock) .advanceClock =
      PMF.pure (atClock (clock + 1)) := by
  change (PMF.pure { atClock clock with clock := (atClock clock).clock + 1 }).map State.drain = _
  rw [PMF.pure_map, State.drain_eq_of_clear]
  · rfl
  · exact finalClear

/-- The first tick is also an actual native operation from the compiled initialization. -/
private theorem initialNativeTick
    (leaks : MessageNetwork.ObservationRule Bool (WitnessedPacket compiled)) :
    (rankedRuntime.reactiveApplication leaks).environment initialLedger .advanceClock =
      PMF.pure { initialLedger with clock := 1 } := by
  change (PMF.pure { initialLedger with clock := initialLedger.clock + 1 }).map State.drain = _
  rw [PMF.pure_map, State.drain_eq_of_empty _ (by rfl)]
  rfl

/-- Expiry addressed to a skipped binding does not reset the next owner's clock. -/
private theorem skippedExpiry
    (leaks : MessageNetwork.ObservationRule Bool (WitnessedPacket compiled)) :
    (rankedRuntime.reactiveApplication leaks).environment (atClock 3) (.expire second) =
      PMF.pure (atClock 3) := by
  change (environmentStep rankedRuntime (atClock 3) (.expire second)).map State.drain = _
  rw [environmentStep_expire_of_not_ready _ _ _ (by decide), PMF.pure_map]
  rw [State.drain_eq_of_clear (atClock 3) finalClear]

/-- The native executor reaches the overdue state after expiry and four further ticks. -/
example
    (leaks : MessageNetwork.ObservationRule Bool (WitnessedPacket compiled)) :
    ((rankedRuntime.reactiveApplication leaks).environment initialLedger .advanceClock).bind
      (fun state => ((rankedRuntime.reactiveApplication leaks).environment state
        (.expire first)).bind fun state =>
        ((rankedRuntime.reactiveApplication leaks).environment state .advanceClock).bind
          fun state =>
        ((rankedRuntime.reactiveApplication leaks).environment state .advanceClock).bind
          fun state =>
        ((rankedRuntime.reactiveApplication leaks).environment state (.expire second)).bind
          fun state =>
        ((rankedRuntime.reactiveApplication leaks).environment state .advanceClock).bind
          fun state =>
        (rankedRuntime.reactiveApplication leaks).environment state .advanceClock) =
      PMF.pure (atClock 5) := by
  rw [initialNativeTick]
  erw [PMF.pure_bind, earlyReadyAfterExpiry, PMF.pure_bind, clockTick,
    PMF.pure_bind, clockTick, PMF.pure_bind, skippedExpiry, PMF.pure_bind,
    clockTick, PMF.pure_bind, clockTick]

/-- Two stale block ticks followed by two more leave the next active owner overdue. -/
example :
    (atClock 5).config.cut.Ready bob ∧ (atClock 5).activatedAt bob = some 1 ∧
      1 + bob.val < (atClock 5).clock ∧
      ¬ (atClock 5).WithinDeadline rankedRuntime bob := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  change ¬ (5 - 1 < 4)
  decide

/-- Automatic completion preserves the next active event's original entry time. -/
example (leaks : MessageNetwork.ObservationRule Bool (WitnessedPacket compiled)) :
    (rankedRuntime.reactiveApplication leaks).environment
        { initialLedger with clock := 1 } (.expire first) = PMF.pure (atClock 1) ∧
      (atClock 1).clock = 1 ∧ (atClock 1).activatedAt bob = some 1 ∧
      (atClock 1).config.cut.Ready bob ∧
      (atClock 1).config.defaulted = ({false} : Finset Bool) :=
  ⟨earlyReadyAfterExpiry leaks, earlyReadyMetadata⟩

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A saved public block-entry view determines the clock decision. -/
example (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (past : List (application setup (Vegas.runtime setup) leaks).EnvironmentEntry)
    (view : (application setup (Vegas.runtime setup) leaks).EnvironmentView)
    (event : (graph setup).EventId)
    (entry : (application setup (Vegas.runtime setup) leaks).EnvironmentEntry)
    (saved : past[(rosterPlanPrefix setup rosters event.val).length]? = some entry) :
    rosterBlockCompleted setup leaks rosters past view event ↔
      event ∈ entry.beforeView.application.observation.completionOrder := by
  simp only [rosterBlockCompleted, saved, Option.elim_some]

/-- The calendar waits at a tick of a block already complete at entry. -/
example (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (past : List (application setup (Vegas.runtime setup) leaks).EnvironmentEntry)
    (view : (application setup (Vegas.runtime setup) leaks).EnvironmentView)
    (event : (graph setup).EventId)
    (selected : (rosterPlan setup rosters)[past.length]? = some (event, .tick))
    (completed : rosterBlockCompleted setup leaks rosters past view event) :
    rosterScheduler setup leaks rosters network past view = PMF.pure .wait := by
  simp only [rosterScheduler, selected, ite_eq_left completed]

/-- A block live at entry retains its tick after its event completes. -/
example (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (past : List (application setup (Vegas.runtime setup) leaks).EnvironmentEntry)
    (view : (application setup (Vegas.runtime setup) leaks).EnvironmentView)
    (event : (graph setup).EventId)
    (selected : (rosterPlan setup rosters)[past.length]? = some (event, .tick))
    (live : ¬ rosterBlockCompleted setup leaks rosters past view event) :
    rosterScheduler setup leaks rosters network past view =
      PMF.pure (.application .advanceClock) := by
  simp only [rosterScheduler, selected, ite_eq_right live]

end VegasTests
