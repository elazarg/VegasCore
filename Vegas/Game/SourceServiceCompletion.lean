module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphPrefixReadout
public import Vegas.Game.SourceServiceTurnPolicy
public import Vegas.EventGraph.PrefixPolicy
public import Vegas.Game.SourceServiceReachedDecoding
public import Vegas.Game.SourceServiceFacts
public import Vegas.Source.SetupProtocolEvaluation
public import Vegas.Game.RevealServicePayoffs
public import Vegas.Pending.ActivationRecall
public import Vegas.Pending.PrefixBoundary
public import Vegas.Pending.ReactiveGraphSteps
public import Vegas.Pending.ReactiveAsyncContract
public import Vegas.Pending.CanonicalOutcomePublication
public import Vegas.Pending.ReactiveStateInvariant
public import Vegas.EventGraph.CanonicalStep
public import Vegas.EventGraph.BarrierBlocks
public import Interaction.ReactiveRoundReachability
public import Interaction.ReactiveRawRoundTrace
public import Interaction.ReactiveStopping
public import Interaction.ReactiveRecallInvariant

@[expose] public section

/-! # Completed prefixes and completion boundaries

On the sequentialized graph one event is ready at a time. A native command
can complete several events through automatic completion. Every complete
round extends the completed prefix while preserving its starting bound on
recorded ready-event views. Stopping at an event's completion retains the
actual later prefix rank.

A completion boundary combines a completed prefix, untouched later events
and actual complete-round reachability. Its continuation law uses the sole
source decoder and evaluator from that current endpoint.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Ranked

variable (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

/-- One round: a scheduler command, its environment step, and the response of
the activated player, if any. -/
theorem round_cases {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {players : Player → (serviceApplication setup deps duration leaks).Policy}
    {execution next : (serviceApplication setup deps duration leaks).Execution}
    (reached : next ∈
        ((serviceApplication setup deps duration leaks).round scheduler players
        execution).support) :
    ∃ command ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment (serviceApplication setup deps duration leaks))).support,
      ∃ middle ∈
          (execution.environmentStep (serviceApplication setup deps duration leaks)
              command).support,
          (command.actor? (serviceApplication setup deps duration leaks) = none ∧ next = middle) ∨ ∃
          who, command.actor? (serviceApplication setup deps duration leaks) = some who ∧ ∃ response
          ∈ (players who (middle.logs who)
              (middle.observe (serviceApplication setup deps duration leaks) who)).support,
              next = middle.respond (serviceApplication setup deps duration leaks) who
                  response := by
  exact EventGraphRuntime.round_cases (serviceTimeouts setup deps duration) leaks reached

/-- An activation leaves the application unchanged. -/
theorem activation_application
    (execution middle : (serviceApplication setup deps duration leaks).Execution) (who : Player)
    (moved : middle ∈
        (execution.environmentStep (serviceApplication setup deps duration leaks)
        (.activate who)).support) :
    middle.application = execution.application := by
  exact EventGraphRuntime.activation_application (serviceTimeouts setup deps duration) leaks
    execution middle who moved

/-- Every recorded activation was answered by its player at the public view
the scheduler saw. -/
abbrev ActivationsAnswered (execution : (serviceApplication setup deps duration leaks).Execution) :
    Prop := EventGraphRuntime.ActivationsAnswered (serviceTimeouts setup deps duration) leaks
      execution

/-- Every round answers its activation at the scheduler's public view. -/
theorem round_activationsAnswered
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {players : Player → (serviceApplication setup deps duration leaks).Policy}
    {execution next : (serviceApplication setup deps duration leaks).Execution}
    (valid : ActivationsAnswered setup leaks execution)
    (reached : next ∈
        ((serviceApplication setup deps duration leaks).round scheduler players
        execution).support) :
    ActivationsAnswered setup leaks next := by
  exact EventGraphRuntime.round_activationsAnswered (serviceTimeouts setup deps duration) leaks
    valid reached

variable {setup leaks} in
/-- Every activation in completed rounds has an actual response in own recall,
even if that response was silent or sent a packet for a different event. -/
theorem roundsFrom_activationsAnswered
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {players : Player → (serviceApplication setup deps duration leaks).Policy} (count : Nat)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (supported : execution ∈
        ((serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
        scheduler players count).support) :
    ActivationsAnswered setup leaks execution := by
  exact EventGraphRuntime.roundsFrom_activationsAnswered
    (timeouts := serviceTimeouts setup deps duration) (leaks := leaks) count execution supported

/-- No recorded response has seen `event` ready. -/
def Untouched (event : (serviceGraph setup deps).EventId)
    (execution : (serviceApplication setup deps duration leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.logs who,
    ¬ entry.beforeView.application.publicView.EventReady event

section

variable {setup leaks}

/-- Every event a recorded response saw ready satisfies `allowed`. -/
def SeenOnly (allowed : (serviceGraph setup deps).EventId → Prop)
    (execution : (serviceApplication setup deps duration leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.logs who, ∀ event,
    entry.beforeView.application.publicView.EventReady event → allowed event

/-- An event outside the allowed ones is untouched. -/
theorem SeenOnly.untouched {allowed : (serviceGraph setup deps).EventId → Prop}
    {execution : (serviceApplication setup deps duration leaks).Execution}
    (seen : SeenOnly allowed execution) {event : (serviceGraph setup deps).EventId}
    (disallowed : ¬ allowed event) : Untouched setup leaks event execution :=
  fun who entry member readyView => disallowed (seen who entry member event readyView)

/-- A larger allowed set keeps the bound. -/
theorem SeenOnly.mono {allowed wider : (serviceGraph setup deps).EventId → Prop}
    {execution : (serviceApplication setup deps duration leaks).Execution}
    (seen : SeenOnly allowed execution) (widen : ∀ event, allowed event → wider event) :
    SeenOnly wider execution :=
  fun who entry member event readyView => widen event (seen who entry member event readyView)

/-- A round keeps the bound when every event ready before it is allowed. -/
theorem round_seenOnly {allowed : (serviceGraph setup deps).EventId → Prop}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {players : Player → (serviceApplication setup deps duration leaks).Policy}
    {execution next : (serviceApplication setup deps duration leaks).Execution}
    (seen : SeenOnly allowed execution)
    (readyAllowed : ∀ event, execution.application.config.cut.Ready event → allowed event)
    (reached : next ∈
      ((serviceApplication setup deps duration leaks).round scheduler players execution).support) :
    SeenOnly allowed next := by
  let app := serviceApplication setup deps duration leaks
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
theorem runUntil_seenOnly {allowed : (serviceGraph setup deps).EventId → Prop}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop) [DecidablePred stop]
    (invariant : (serviceApplication setup deps duration leaks).Execution → Prop)
    (preserved : ∀ execution, invariant execution → ¬ stop execution →
      ∀ next ∈ ((serviceApplication setup deps duration leaks).round scheduler players
        execution).support, invariant next)
    (readyAllowed : ∀ execution, invariant execution → ¬ stop execution →
      ∀ event, execution.application.config.cut.Ready event → allowed event)
    (count : Nat) (execution : (serviceApplication setup deps duration leaks).Execution)
    (valid : invariant execution) (seen : SeenOnly allowed execution)
    (final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntil scheduler
      players stop count execution).support) :
    SeenOnly allowed final := by
  obtain ⟨_, _, finalSeen⟩ := (serviceApplication setup deps duration leaks).runUntil_support_holds
    scheduler players stop (fun _ current => invariant current ∧ SeenOnly allowed current)
    (fun _ current holds running next moved =>
      ⟨preserved current holds.1 running next moved,
        round_seenOnly holds.2 (readyAllowed current holds.1 running) moved⟩)
    count execution ⟨valid, seen⟩ final reached
  exact finalSeen

/-- Stopping no later than block completion leaves every later event unseen,
including under arbitrary native clients and automatic completion tails. -/
theorem blockRun_untouched
    {start finish : Nat}
    (shaped : BlockShaped (graph := serviceGraph setup deps) start finish)
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop) [DecidablePred stop]
    (completed : ∀ current, BlockDone finish current.application.config → stop current)
    (count : Nat) (origin final : (serviceApplication setup deps duration leaks).Execution)
    (inside : InBlock start finish origin.application.config)
    (untouched : ∀ event : (serviceGraph setup deps).EventId, finish ≤ event.val →
      Untouched setup leaks event origin)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntil scheduler players
      stop count origin).support) :
    ∀ event : (serviceGraph setup deps).EventId, finish ≤ event.val →
      Untouched setup leaks event final := by
  let app := serviceApplication setup deps duration leaks
  let holds := fun current : app.Execution =>
    ¬ stop current → InBlock start finish current.application.config
  have initial : holds origin := fun _ => inside
  have preserved : ∀ current, holds current → ¬ stop current →
      ∀ next ∈ (app.round scheduler players current).support, holds next := by
    intro current valid running next moved unfinished
    exact (valid running).path shaped
      (reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks scheduler players
        current next moved) (fun done => unfinished (completed next done))
  have allowed : ∀ current, holds current → ¬ stop current →
      ∀ event, current.application.config.cut.Ready event → event.val < finish := by
    intro current valid running event ready
    exact (shaped _ (valid running) (fun done => running (completed current done)) event ready).2
  have seen : SeenOnly (fun event => event.val < finish) origin := by
    intro who entry present event ready
    by_contra later
    exact untouched event (by omega) who entry present ready
  have finalSeen := runUntil_seenOnly scheduler players stop holds preserved allowed count origin
    initial seen final reached
  intro event later
  exact finalSeen.untouched (Nat.not_lt.mpr later)


end

/-- Every recorded response saw only events of rank at most `bound` ready. -/
abbrev ReadySeen (bound : Nat)
    (execution : (serviceApplication setup deps duration leaks).Execution) : Prop :=
  EventGraphRuntime.RememberedReadyAtMost bound execution

/-- An execution where the events of rank below `rank` have completed, no
recorded response has seen the event of rank `rank` ready, and which the
players reach by complete rounds from initialization. -/
abbrev CompletionBoundary (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (rank : Nat)
    (execution : (serviceApplication setup deps duration leaks).Execution) : Prop :=
  EventGraphRuntime.PrefixBoundary (serviceInitialLaw setup deps) scheduler players rank execution

/-- From every completion boundary within the horizon, the players' run to the
horizon has the source continuation law of the configuration's typed prefix. -/
def BoundaryContinuationLaw (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (horizon : Nat) (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (profile : BehavioralProfile setup.program) : Prop := ∀ rank
    (execution : (serviceApplication setup deps duration leaks).Execution), CompletionBoundary setup
    leaks scheduler players rank execution → execution.environmentRecall.length ≤ horizon →
    ((serviceApplication setup deps duration leaks).runToHorizon scheduler players horizon
        execution).map
    (fun final => serviceSourceReadout setup deps duration leaks
        ((serviceApplication setup deps duration leaks).finished final)) =
    (setup.continuationLaw profile
        (serviceSourcePrefix? setup deps rank execution.application.config)).map some

end Ranked

section Sequential

variable (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts setup.informationGraph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))

variable {setup} in
/-- Every saved ready event lies at or before the current actual sequential prefix. -/
theorem readySeen_of_rawTrace {horizon rank : Nat}
    {scheduler : (application setup timeouts leaks).Scheduler}
    {control : (application setup timeouts leaks).Control}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some control))
    (ordered : control.execution.application.config.cut.IsPrefix rank) :
    ReadySeen setup leaks rank control.execution := by
  have facts := legalFacts setup leaks horizon scheduler control trace
  intro owner entry member event readyView
  by_cases completed : event ∈ control.execution.application.config.cut.completed
  · exact Nat.le_of_lt ((ordered.2 event).mp completed)
  · obtain ⟨extra, order, _together, _activated, _accepted⟩ :=
      facts.eventStable owner entry member event readyView completed
    have ready := ready_of_eventReady_extends order readyView completed
    have actual : control.execution.application.config.cut.IsPrefix event.val :=
      ⟨event.isLt.le, fun query =>
        setup.informationGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
    exact (actual.unique ordered).le

/-- **A reached boundary.** The execution of a legal history at a scheduler
boundary, whose configuration is a prefix at `rank`, with every event from
`rank` on untouched and every own submission made at its author's turn. -/
structure ReachedBoundary (horizon : Nat) (scheduler : (application setup timeouts leaks).Scheduler)
    (rank : Nat) (execution : (application setup timeouts leaks).Execution) : Prop where
  trace : Nonempty (((application setup timeouts leaks).protocol (initialLaw setup) horizon
    scheduler).Trace (some ⟨horizon - execution.environmentRecall.length, none, execution⟩))
  bounded : execution.environmentRecall.length ≤ horizon
  ordered : execution.application.config.cut.IsPrefix rank
  untouched : ∀ event : setup.informationGraph.EventId, rank ≤ event.val →
    Untouched setup leaks event execution
  turns : ∀ who, OwnSubmissionsAtTurn timeouts leaks execution who


end Sequential


section

variable {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}

/-- Every initialized raw native history has a residual of the same source evaluator. -/
theorem SourceResidual.of_rawTrace (profile : BehavioralProfile setup.program)
    (horizon : Nat) (scheduler : (application setup timeouts leaks).Scheduler) :
    ∀ {state} (_trace : ((application setup timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).Trace state) (control : (application setup timeouts leaks).Control),
      state = some control →
      ∃ rank,
        Nonempty (SourceResidual setup profile rank control.execution.application.config) := by
  intro state trace
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint _ realized ih =>
      intro control current
      subst current
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state =>
            some ⟨horizon, none, ReactiveApplication.Execution.initial
              (application setup timeouts leaks) state⟩).support at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨0, ⟨SourceResidual.initial setup profile initial⟩⟩
      | some previous =>
          obtain ⟨rank, ⟨residual⟩⟩ := ih previous rfl
          exact residual.path (reactive_protocol_graph_steps timeouts leaks
            (initialLaw setup) horizon scheduler previous control joint realized)

end

section

variable {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- **Runs end by the horizon.** Every final of a run stopped at `stop` satisfies
`stop` when every terminal configuration does, since the contract completes
every event by the horizon. -/
theorem runUntilHorizon_stop {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop) [DecidablePred stop]
    (terminalStops : ∀ execution : (serviceApplication setup deps duration leaks).Execution,
      execution.application.config.cut.Terminal → stop execution)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler players execution.environmentRecall.length).support)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    ∀ final ∈ ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler players
      stop horizon execution).support, stop final := by
  let app := serviceApplication setup deps duration leaks
  intro final reached
  let remaining := horizon - execution.environmentRecall.length
  change final ∈ (app.runUntil scheduler players stop remaining execution).support at reached
  rcases app.runUntil_stopped scheduler players stop remaining execution final reached
      with done | _
  · exact done
  obtain ⟨used, enough, rounds, _⟩ := app.runUntil_runRounds scheduler players stop remaining
    execution final reached
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler
    players execution.environmentRecall.length bounded execution supported
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (serviceInitialLaw setup deps) horizon scheduler
    players (remaining - used) used execution final
    (by simpa only [Nat.sub_add_cancel enough] using trace) rounds
  apply terminalStops
  exact contract.completes _ finalTrace (by
    change remaining - used = 0 ∧ _
    exact ⟨by dsimp only [remaining] at *; omega, rfl⟩)

/-- A round from a terminal configuration keeps it. -/
theorem round_config_eq_of_terminal
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {players : Player → (serviceApplication setup deps duration leaks).Policy}
    {execution next : (serviceApplication setup deps duration leaks).Execution}
    (terminal : execution.application.config.cut.Terminal)
    (reached : next ∈
      ((serviceApplication setup deps duration leaks).round scheduler players execution).support) :
    next.application.config = execution.application.config := by
  exact EventGraph.Config.Step.path_eq_of_terminal
    (reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks _ _ _ _ reached)
    terminal

/-- Rounds from a terminal configuration keep it. -/
theorem runRounds_config_eq_of_terminal
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) :
    ∀ (count : Nat) (execution final : (serviceApplication setup deps duration leaks).Execution),
      execution.application.config.cut.Terminal →
      final ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler players count
        execution).support →
      final.application.config = execution.application.config := by
  intro count
  induction count with
  | zero =>
      intro execution final _ reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | succ count ih =>
      intro execution final terminal reached
      simp only [ReactiveApplication.runRounds] at reached
      obtain ⟨next, moved, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      have same := round_config_eq_of_terminal terminal moved
      rw [ih next final (same ▸ terminal) rest, same]

end

section

open EventGraph

/-- Canonical graph play and the initialized service continuation use the same input law. -/
theorem service_play_outcomeLaw (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    (profile : (serviceGraph setup deps).BehavioralProfile) {Outcome : Type*}
    (read : (serviceGraph setup deps).Config → Outcome) :
    (((serviceGraph setup deps).gameForm (setup.initialLaw.map setup.eventInputs)
        (serviceGraph setup deps).canonicalScheduler).play profile).map
        (fun outcome => read outcome.1) =
      (serviceInitialLaw setup deps).bind fun state =>
        outcomeLaw profile read state.config := by
  change ((setup.initialLaw.map (fun initial => setup.eventInputs initial)).bind
      (fun inputs => (serviceGraph setup deps).terminalOutcomes
        (serviceGraph setup deps).canonicalScheduler profile inputs)).map _ = _
  rw [PMF.map_bind, PMF.bind_map, serviceInitialLaw, PMF.bind_map]
  apply bind_congr_on_support _
  intro initial _
  simp only [Function.comp_apply]
  change ((serviceGraph setup deps).terminalOutcomes _ profile
    (setup.eventInputs initial)).map (read ∘ Subtype.val) = _
  rw [← PMF.map_comp, terminalOutcomes_map_val]
  have initialRemaining : (EventGraph.Config.initial (setup.eventInputs initial) :
      (serviceGraph setup deps).Config).remaining =
        (serviceGraph setup deps).order.eventCount := by
    simp [EventGraph.Config.remaining, EventGraph.Config.initial, EventOrder.Cut.empty]
  unfold outcomeLaw EventGraph.runPolicies EventGraph.run
  change _ = ((serviceGraph setup deps).runPlan _
    (EventGraph.Config.initial (setup.eventInputs initial) :
      (serviceGraph setup deps).Config).remaining _).map read
  rw [initialRemaining]
  rfl

end

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- Changing unseen graph decisions preserves initialized native support. -/
theorem roundsFrom_reference_support_of_untouched
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (left right : (serviceGraph setup deps).BehavioralProfile)
    (changed : (serviceGraph setup deps).EventId → Prop)
    (same : ∀ who event actor observation active, ¬ changed event →
      left who event actor observation active = right who event actor observation active)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (count : Nat) (after : (serviceApplication setup deps duration leaks).Execution)
    (unseen : ∀ event, changed event → Untouched setup leaks event after)
    (reached : after ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) ((serviceGraph setup deps).prefixProfile left))
          focal deviation) count).support) :
    after ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) ((serviceGraph setup deps).prefixProfile right))
          focal deviation) count).support := by
  classical
  apply ReactiveApplication.roundsFrom_support_of_recorded_policy_eq
    (serviceApplication setup deps duration leaks) (serviceInitialLaw setup deps) scheduler _ _
      count after reached
  intro who entry member past
  by_cases own : who = focal
  · subst who
    simp only [Function.update_self]
  · simp only [Function.update_of_ne own]
    apply serviceReferenceTurnPolicy_eq_of_ready_kernels bound turns
    intro event ready actor observation active
    simp only [prefixProfile, prefixPolicy]
    apply same
    intro modified
    exact unseen event modified who entry member ready

end Vegas
