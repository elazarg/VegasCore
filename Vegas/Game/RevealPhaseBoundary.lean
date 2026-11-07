/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealBlockPhase
import Vegas.Game.RevealPhasing
import Vegas.Game.LastForeignPhase
import Vegas.Game.LastChancePhase
import Vegas.Game.RevealServiceHonestLaw

/-! # Phase boundaries of a ledger run with concurrent reveals

A phase boundary at a rank is an execution reached by complete rounds within
the horizon in which every earlier event has completed, every later completed
event was completed automatically for a defaulted owner, and every recorded
response saw only earlier events ready. Rounds keep the bound on what responses
saw while only allowed events are ready, because a round that completes an
event records no response.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- Every event a recorded response saw ready satisfies `allowed`. -/
def SeenOnly (allowed : (serviceGraph setup mode).EventId → Prop)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.logs who, ∀ event,
    entry.beforeView.application.publicView.EventReady event → allowed event

/-- An event outside the allowed ones is untouched. -/
theorem SeenOnly.untouched {allowed : (serviceGraph setup mode).EventId → Prop}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (seen : SeenOnly allowed execution) {event : (serviceGraph setup mode).EventId}
    (disallowed : ¬ allowed event) : Untouched setup leaks event execution :=
  fun who entry member readyView => disallowed (seen who entry member event readyView)

/-- A larger allowed set keeps the bound. -/
theorem SeenOnly.mono {allowed wider : (serviceGraph setup mode).EventId → Prop}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (seen : SeenOnly allowed execution) (widen : ∀ event, allowed event → wider event) :
    SeenOnly wider execution :=
  fun who entry member event readyView => widen event (seen who entry member event readyView)

/-- A round keeps the bound when every event ready before it is allowed. -/
theorem round_seenOnly {allowed : (serviceGraph setup mode).EventId → Prop}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (seen : SeenOnly allowed execution)
    (readyAllowed : ∀ event, execution.application.config.cut.Ready event → allowed event)
    (reached : next ∈
      ((serviceApplication setup mode deadline leaks).round scheduler players execution).support) :
    SeenOnly allowed next := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases (setup := setup) leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  intro who entry member event readyView
  rcases cases with ⟨_, rfl⟩ | ⟨actor, active, response, _, rfl⟩
  · rw [recallEq] at member
    exact seen who entry member event readyView
  · rcases app.respond_entry_origin middle actor who response entry member with
      prior | ⟨_, fresh⟩
    · rw [recallEq] at prior
      exact seen who entry prior event readyView
    · have commandEq : command = .activate actor := by
        cases command <;> simp_all [ReactiveApplication.Command.actor?]
      subst command
      have sameApp := activation_application (setup := setup) leaks execution middle actor moved
      rw [fresh] at readyView
      change middle.application.publicView.EventReady event at readyView
      have readyNow := (EventGraphRuntime.State.publicView_eventReady _ event).mp readyView
      rw [sameApp] at readyNow
      exact readyAllowed event readyNow

/-- A stopped run keeps the bound when, along an invariant kept by every round
taken, every event ready before a round is allowed. -/
theorem runUntil_seenOnly {allowed : (serviceGraph setup mode).EventId → Prop}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (stop : (serviceApplication setup mode deadline leaks).Execution → Prop) [DecidablePred stop]
    (invariant : (serviceApplication setup mode deadline leaks).Execution → Prop)
    (preserved : ∀ execution, invariant execution → ¬ stop execution →
      ∀ next ∈ ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support, invariant next)
    (readyAllowed : ∀ execution, invariant execution → ¬ stop execution →
      ∀ event, execution.application.config.cut.Ready event → allowed event)
    (count : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (valid : invariant execution) (seen : SeenOnly allowed execution)
    (final : (serviceApplication setup mode deadline leaks).Execution)
    (reached : final ∈ ((serviceApplication setup mode deadline leaks).runUntil scheduler
      players stop count execution).support) :
    SeenOnly allowed final := by
  obtain ⟨_, _, finalSeen⟩ := (serviceApplication setup mode deadline leaks).runUntil_support_holds
    scheduler players stop (fun _ current => invariant current ∧ SeenOnly allowed current)
    (fun _ current holds running next moved =>
      ⟨preserved current holds.1 running next moved,
        round_seenOnly holds.2 (readyAllowed current holds.1 running) moved⟩)
    count execution ⟨valid, seen⟩ final reached
  exact finalSeen

/-- **Runs end by the horizon.** Every final of a run stopped at `stop` satisfies
`stop` when every terminal configuration does, since the contract completes
every event by the horizon. -/
theorem runUntilHorizon_stop {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (stop : (serviceApplication setup mode deadline leaks).Execution → Prop) [DecidablePred stop]
    (terminalStops : ∀ execution : (serviceApplication setup mode deadline leaks).Execution,
      execution.application.config.cut.Terminal → stop execution)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler players execution.environmentRecall.length).support)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    ∀ final ∈ ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
      stop horizon execution).support, stop final := by
  let app := serviceApplication setup mode deadline leaks
  intro final reached
  let remaining := horizon - execution.environmentRecall.length
  change final ∈ (app.runUntil scheduler players stop remaining execution).support at reached
  rcases app.runUntil_stopped scheduler players stop remaining execution final reached
      with done | _
  · exact done
  obtain ⟨used, enough, rounds, _⟩ := app.runUntil_runRounds scheduler players stop remaining
    execution final reached
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    players execution.environmentRecall.length bounded execution supported
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (serviceInitialLaw setup mode) horizon scheduler
    players (remaining - used) used execution final
    (by simpa only [Nat.sub_add_cancel enough] using trace) rounds
  apply terminalStops
  exact contract.completes _ finalTrace (by
    change remaining - used = 0 ∧ _
    exact ⟨by dsimp only [remaining] at *; omega, rfl⟩)

/-- **A phase boundary at a rank.** -/
structure PhaseBoundary (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (horizon : Nat)
    (rank : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop where
  supported : execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
    (serviceInitialLaw setup mode) scheduler players execution.environmentRecall.length).support
  bounded : execution.environmentRecall.length ≤ horizon
  earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < rank →
    event ∈ execution.application.config.cut.completed
  later : ∀ event : (serviceGraph setup mode).EventId, rank ≤ event.val →
    event ∈ execution.application.config.cut.completed →
      completionOf execution.application.config event = some ⟨event, none, none⟩ ∧
      execution.application.config.outputs event = failureOutput event ∧
      ∃ owner, (serviceGraph setup mode).actor? event = some owner ∧
        owner ∈ execution.application.config.defaulted
  seen : SeenOnly (fun event : (serviceGraph setup mode).EventId => event.val < rank) execution
  owners : DefaultOwners execution.application.config

/-- A phase boundary has no automatically ready event. -/
theorem PhaseBoundary.quiescent
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {horizon rank : Nat}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (boundary : PhaseBoundary scheduler players horizon rank execution) :
    ∀ event, ¬ execution.application.AutomaticReady event := by
  obtain ⟨trace⟩ := (serviceApplication setup mode deadline leaks).raw_trace_roundsFrom
    (serviceInitialLaw setup mode) horizon scheduler players
    execution.environmentRecall.length boundary.bounded execution boundary.supported
  exact (legalFacts setup leaks horizon scheduler _ trace).quiescent

/-- At a phase boundary opening a run of reveals, the block starts. -/
theorem PhaseBoundary.blockStart
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {horizon start finish : Nat}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (boundary : PhaseBoundary scheduler players horizon start execution)
    (relaxed : RelaxedOrder (serviceGraph setup mode))
    (runs : FlatRevealRuns (serviceGraph setup mode))
    (run : RevealRun (serviceGraph setup mode) start finish) :
    BlockStart start finish execution.application.config where
  earlier := boundary.earlier
  later := fun event late done => run.done_of_later relaxed late done
  beyond := fun event late done => (boundary.later event (by have := run.nonempty; omega)
    done).1
  failed := fun event early _ done => (boundary.later event early done).2.1
  drained := fun event early late => by
    constructor
    · intro done
      exact (boundary.later event early done).2.2
    · rintro ⟨owner, owned, inactive⟩
      by_contra pending
      apply boundary.quiescent event
      unfold EventGraphRuntime.State.AutomaticReady
      rw [owned]
      exact ⟨(run.flat relaxed runs).ready_of_earlier boundary.earlier early late pending,
        inactive⟩
  silent := fun event early _ done => (boundary.later event early done).1

/-- At a phase boundary at an event that is not a reveal, the event is pending
exactly when the cut is the prefix before it. -/
theorem PhaseBoundary.prefix_of_pending
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {horizon : Nat}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    {event : (serviceGraph setup mode).EventId}
    (boundary : PhaseBoundary scheduler players horizon event.val execution)
    (relaxed : RelaxedOrder (serviceGraph setup mode))
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication)
    (pending : event ∉ execution.application.config.cut.completed) :
    execution.application.config.cut.IsPrefix event.val := by
  refine ⟨event.isLt.le, fun query => ⟨fun done => ?_, boundary.earlier query⟩⟩
  by_contra late
  push Not at late
  rcases Nat.eq_or_lt_of_le late with same | later
  · exact pending (Fin.ext same ▸ done)
  · exact pending (execution.application.config.cut.predecessor_closed done
      (relaxed.predecessor_of_not_publication notPublication later))

/-- A player's normalized view records no decision at an event completed
silently. -/
theorem observedAction_of_silent {graph : Vegas.EventGraph Player L} (who : Player)
    {config : graph.Config} {event : graph.EventId}
    (silent : completionOf config event = some ⟨event, none, none⟩) :
    observedAction event (graph.normalizeObservation who (graph.playerObserve who config)) =
      none := by
  unfold observedAction
  rw [normalizeObservation_playerObserve]
  simp only
  rw [find?_filterMap_tagged _ (completionOf_filter_tagged config _), silent]
  simp

end Vegas
