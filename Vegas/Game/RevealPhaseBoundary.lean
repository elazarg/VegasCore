module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealBlockPhase
public import Vegas.Game.RevealPhasing
public import Vegas.Game.LastForeignPhase
public import Vegas.Game.LastChancePhase
public import Vegas.Game.RevealServiceHonestLaw

@[expose] public section

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
  {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- Every event a recorded response saw ready satisfies `allowed`. -/
def SeenOnly (allowed : (serviceGraph setup mode).EventId → Prop)
    (execution : (serviceApplication setup mode duration leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.logs who, ∀ event,
    entry.beforeView.application.publicView.EventReady event → allowed event

/-- An event outside the allowed ones is untouched. -/
theorem SeenOnly.untouched {allowed : (serviceGraph setup mode).EventId → Prop}
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (seen : SeenOnly allowed execution) {event : (serviceGraph setup mode).EventId}
    (disallowed : ¬ allowed event) : Untouched setup leaks event execution :=
  fun who entry member readyView => disallowed (seen who entry member event readyView)

/-- A larger allowed set keeps the bound. -/
theorem SeenOnly.mono {allowed wider : (serviceGraph setup mode).EventId → Prop}
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (seen : SeenOnly allowed execution) (widen : ∀ event, allowed event → wider event) :
    SeenOnly wider execution :=
  fun who entry member event readyView => widen event (seen who entry member event readyView)

/-- A round keeps the bound when every event ready before it is allowed. -/
theorem round_seenOnly {allowed : (serviceGraph setup mode).EventId → Prop}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy}
    {execution next : (serviceApplication setup mode duration leaks).Execution}
    (seen : SeenOnly allowed execution)
    (readyAllowed : ∀ event, execution.application.config.cut.Ready event → allowed event)
    (reached : next ∈
      ((serviceApplication setup mode duration leaks).round scheduler players execution).support) :
    SeenOnly allowed next := by
  let app := serviceApplication setup mode duration leaks
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
    (scheduler : (serviceApplication setup mode duration leaks).Scheduler)
    (players : Player → (serviceApplication setup mode duration leaks).Policy)
    (stop : (serviceApplication setup mode duration leaks).Execution → Prop) [DecidablePred stop]
    (invariant : (serviceApplication setup mode duration leaks).Execution → Prop)
    (preserved : ∀ execution, invariant execution → ¬ stop execution →
      ∀ next ∈ ((serviceApplication setup mode duration leaks).round scheduler players
        execution).support, invariant next)
    (readyAllowed : ∀ execution, invariant execution → ¬ stop execution →
      ∀ event, execution.application.config.cut.Ready event → allowed event)
    (count : Nat) (execution : (serviceApplication setup mode duration leaks).Execution)
    (valid : invariant execution) (seen : SeenOnly allowed execution)
    (final : (serviceApplication setup mode duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup mode duration leaks).runUntil scheduler
      players stop count execution).support) :
    SeenOnly allowed final := by
  obtain ⟨_, _, finalSeen⟩ := (serviceApplication setup mode duration leaks).runUntil_support_holds
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
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (players : Player → (serviceApplication setup mode duration leaks).Policy)
    (stop : (serviceApplication setup mode duration leaks).Execution → Prop) [DecidablePred stop]
    (terminalStops : ∀ execution : (serviceApplication setup mode duration leaks).Execution,
      execution.application.config.cut.Terminal → stop execution)
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup mode duration leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler players execution.environmentRecall.length).support)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    ∀ final ∈ ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler players
      stop horizon execution).support, stop final := by
  let app := serviceApplication setup mode duration leaks
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
structure PhaseBoundary (scheduler : (serviceApplication setup mode duration leaks).Scheduler)
    (players : Player → (serviceApplication setup mode duration leaks).Policy) (horizon : Nat)
    (rank : Nat) (execution : (serviceApplication setup mode duration leaks).Execution) :
    Prop where
  supported : execution ∈ ((serviceApplication setup mode duration leaks).roundsFrom
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
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy} {horizon rank : Nat}
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (boundary : PhaseBoundary scheduler players horizon rank execution) :
    ∀ event, ¬ execution.application.AutomaticReady event := by
  obtain ⟨trace⟩ := (serviceApplication setup mode duration leaks).raw_trace_roundsFrom
    (serviceInitialLaw setup mode) horizon scheduler players
    execution.environmentRecall.length boundary.bounded execution boundary.supported
  exact (legalFacts setup leaks horizon scheduler _ trace).quiescent

/-- At a phase boundary opening a run of reveals, the block starts. -/
theorem PhaseBoundary.blockStart
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy}
    {horizon start finish : Nat}
    {execution : (serviceApplication setup mode duration leaks).Execution}
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
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy} {horizon : Nat}
    {execution : (serviceApplication setup mode duration leaks).Execution}
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

/-- Every execution a stopped run reaches is reached by graph steps. -/
theorem runUntil_config_path
    (scheduler : (serviceApplication setup mode duration leaks).Scheduler)
    (players : Player → (serviceApplication setup mode duration leaks).Policy)
    (stop : (serviceApplication setup mode duration leaks).Execution → Prop) [DecidablePred stop]
    (count : Nat) (execution final : (serviceApplication setup mode duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup mode duration leaks).runUntil scheduler players
      stop count execution).support) :
    Relation.ReflTransGen Config.Step execution.application.config final.application.config := by
  obtain ⟨_, walked⟩ := (serviceApplication setup mode duration leaks).runUntil_support_holds
    scheduler players stop
    (fun _ current => Relation.ReflTransGen Config.Step execution.application.config
      current.application.config)
    (fun _ current walked _ next moved => walked.trans (round_config_path moved))
    count execution .refl final reached
  exact walked

/-- A run within the horizon keeps the execution supported and within the
horizon. -/
theorem runUntilHorizon_bounded {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy}
    {stop : (serviceApplication setup mode duration leaks).Execution → Prop} [DecidablePred stop]
    {execution final : (serviceApplication setup mode duration leaks).Execution}
    (supported : execution ∈ ((serviceApplication setup mode duration leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler players execution.environmentRecall.length).support)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (reached : final ∈ ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
      players stop horizon execution).support) :
    final ∈ ((serviceApplication setup mode duration leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler players final.environmentRecall.length).support ∧
    final.environmentRecall.length ≤ horizon := by
  let app := serviceApplication setup mode duration leaks
  refine ⟨app.roundsFrom_runUntil scheduler players (serviceInitialLaw setup mode) stop _
    execution final supported reached, ?_⟩
  obtain ⟨used, enough, _, lengths⟩ := app.runUntil_runRounds scheduler players stop _
    execution final reached
  omega

/-- A later event completed silently stays so along graph paths. -/
private theorem later_path {before after : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step before after)
    {event : (serviceGraph setup mode).EventId}
    (done : event ∈ before.cut.completed)
    (silent : completionOf before event = some ⟨event, none, none⟩ ∧
      before.outputs event = failureOutput event ∧
      ∃ owner, (serviceGraph setup mode).actor? event = some owner ∧ owner ∈ before.defaulted) :
    completionOf after event = some ⟨event, none, none⟩ ∧
      after.outputs event = failureOutput event ∧
      ∃ owner, (serviceGraph setup mode).actor? event = some owner ∧ owner ∈ after.defaulted := by
  obtain ⟨recorded, output, owner, owned, inactive⟩ := silent
  exact ⟨Config.Step.path_completionOf_of_some path event _ recorded,
    (outputs_path path done).trans output, owner, owned,
    Config.Step.path_defaulted_mono path inactive⟩

/-- **The end of a block phase is the next phase boundary.** -/
theorem blockPhase_endpoint {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup mode duration) delay bound)
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (who : Player) (deviation : (serviceApplication setup mode duration leaks).Policy)
    (relaxed : RelaxedOrder (serviceGraph setup mode))
    (runs : FlatRevealRuns (serviceGraph setup mode))
    {start finish : Nat} (run : RevealRun (serviceGraph setup mode) start finish)
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (boundary : PhaseBoundary scheduler (Function.update (serviceReferenceTurnPolicy setup mode
      duration leaks bound turns (firstTurnTiming setup turns mode) reference) who deviation)
      horizon start execution)
    (final : (serviceApplication setup mode duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
      (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
        (firstTurnTiming setup turns mode) reference) who deviation)
      (fun current => BlockDone finish current.application.config) horizon execution).support) :
    PhaseBoundary scheduler (Function.update (serviceReferenceTurnPolicy setup mode duration leaks
      bound turns (firstTurnTiming setup turns mode) reference) who deviation) horizon finish
      final := by
  let app := serviceApplication setup mode duration leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
    (firstTurnTiming setup turns mode) reference) who deviation
  have shaped := run.shaped relaxed
  have begin := boundary.blockStart relaxed runs run
  have done := runUntilHorizon_stop contract players
    (fun current => BlockDone finish current.application.config)
    (fun current terminal event _ => by rw [terminal]; exact Finset.mem_univ _)
    execution boundary.supported boundary.bounded final reached
  obtain ⟨path, sound⟩ := blockRun_facts bound turns contract timely reference decides who
    deviation start finish shaped run.publications execution boundary.supported
    boundary.bounded begin.inside
    (fun event early _ => boundary.seen.untouched (by omega)) final reached
  obtain ⟨finalSupported, finalBounded⟩ :=
    runUntilHorizon_bounded boundary.supported boundary.bounded reached
  refine ⟨finalSupported, finalBounded, done, fun event late finished => ?_, ?_,
    DefaultOwners.path path boundary.owners⟩
  · by_cases old : event ∈ execution.application.config.cut.completed
    · exact later_path path old (boundary.later event (by have := run.nonempty; omega) old)
    · rcases sound event old finished with silent | ⟨_, smaller, _⟩
      · exact silent
      · omega
  · apply runUntil_seenOnly scheduler players
      (fun current => BlockDone finish current.application.config)
      (fun current => Relation.ReflTransGen Config.Step execution.application.config
        current.application.config ∧
        (¬ BlockDone finish current.application.config →
          InBlock start finish current.application.config))
      (fun current valid running next moved =>
        ⟨valid.1.trans (round_config_path moved), fun unfinished =>
          (valid.2 running).path shaped (round_config_path moved) unfinished⟩)
      (fun current valid running event ready => (shaped _ (valid.2 running) running event ready).2)
      (horizon - execution.environmentRecall.length) execution ⟨.refl, begin.inside⟩
      (boundary.seen.mono fun event smaller => by have := run.nonempty; omega) final reached

omit [DecidableEq Player] in
/-- An event that is not a reveal is alone when ready. -/
theorem alone_of_not_publication {graph : Vegas.EventGraph Player L}
    (concurrent : graph.RevealsOnlyConcurrent) {event : graph.EventId}
    (notPublication : ¬ (graph.outputLayout event).IsPublication) :
    ∀ (cut : graph.order.Cut) other, cut.Ready event → cut.Ready other → other = event := by
  intro cut other ready otherReady
  by_contra different
  rcases concurrent cut ready otherReady (Ne.symm different) with independent | independent
  · exact notPublication independent.1
  · exact notPublication independent.2.1

/-- **The end of a solitary phase is the next phase boundary.** -/
theorem solitaryPhase_endpoint {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (players : Player → (serviceApplication setup mode duration leaks).Policy)
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (event : (serviceGraph setup mode).EventId)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication)
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (boundary : PhaseBoundary scheduler players horizon event.val execution)
    (final : (serviceApplication setup mode duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler
      players (fun current => event ∈ current.application.config.cut.completed) horizon
      execution).support) :
    PhaseBoundary scheduler players horizon (event.val + 1) final := by
  let app := serviceApplication setup mode duration leaks
  have alone := alone_of_not_publication concurrent notPublication
  have done := runUntilHorizon_stop contract players
    (fun current => event ∈ current.application.config.cut.completed)
    (fun current terminal => by rw [terminal]; exact Finset.mem_univ _)
    execution boundary.supported boundary.bounded final reached
  have path := runUntil_config_path scheduler players _ _ execution final reached
  obtain ⟨finalSupported, finalBounded⟩ :=
    runUntilHorizon_bounded boundary.supported boundary.bounded reached
  have readyOf {config : (serviceGraph setup mode).Config}
      (earlier : ∀ query : (serviceGraph setup mode).EventId, query.val < event.val →
        query ∈ config.cut.completed)
      (pending : event ∉ config.cut.completed) : config.cut.Ready event :=
    ⟨pending, fun prior member => earlier prior
      ((serviceGraph setup mode).order.predecessor_lt member)⟩
  refine ⟨finalSupported, finalBounded, fun query smaller => ?_, fun query late finished => ?_,
    ?_, DefaultOwners.path path boundary.owners⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp smaller with before | same
    · exact Config.Step.path_completed_mono path (boundary.earlier query before)
    · exact Fin.ext same ▸ done
  · by_cases old : query ∈ execution.application.config.cut.completed
    · exact later_path path old (boundary.later query (by omega) old)
    by_cases pending : event ∈ execution.application.config.cut.completed
    · have stopped := app.runUntil_of_stop scheduler players
        (fun current => event ∈ current.application.config.cut.completed)
        (horizon - execution.environmentRecall.length) execution pending
      change final ∈ (app.runUntil scheduler players _ _ execution).support at reached
      rw [stopped, PMF.mem_support_pure_iff] at reached
      subst reached
      exact (old finished).elim
    have ready := readyOf boundary.earlier pending
    obtain ⟨action, native, primary, drained⟩ := runUntil_completed_primary_drain
      (serviceTimeouts setup mode duration) leaks scheduler players event
      (horizon - execution.environmentRecall.length) execution final ready
      (fun other otherReady => alone _ other ready otherReady) boundary.quiescent reached done
    obtain ⟨record, recorded⟩ := Option.isSome_iff_exists.mp
      ((completionOf_isSome_iff final.application.config query).mpr finished)
    obtain ⟨present, recordEvent⟩ :=
      (completionOf_eq_some_iff final.application.config query record).mp recorded
    rw [drained] at present
    have notNative : query ∉ native.config.cut.completed := by
      rw [execution.application.config.step_cut event ready action native.config primary,
        EventOrder.Cut.mem_complete]
      rintro (same | earlier)
      · rw [same] at late
        omega
      · exact old earlier
    have primaryAbsent : record ∉ native.config.history := fun inside =>
      notNative ((native.config.history_exact query).mp
        (List.mem_map.mpr ⟨record, inside, recordEvent⟩))
    obtain ⟨silent, quiet, _, output, owner, owned, inactive⟩ :=
      drainRecord_of_not_mem native record primaryAbsent present
    subst recordEvent
    rw [drained]
    exact ⟨completionOf_of_silent present silent quiet, output, owner, owned, inactive⟩
  · apply runUntil_seenOnly scheduler players
      (fun current => event ∈ current.application.config.cut.completed)
      (fun current => ∀ query : (serviceGraph setup mode).EventId, query.val < event.val →
        query ∈ current.application.config.cut.completed)
      (fun current valid _ next moved query smaller =>
        Config.Step.path_completed_mono (round_config_path moved) (valid query smaller))
      (fun current valid running query ready => by
        rw [alone _ query (readyOf valid running) ready]
        exact Nat.lt_succ_self _)
      (horizon - execution.environmentRecall.length) execution boundary.earlier
      (boundary.seen.mono fun query smaller => Nat.lt_succ_of_lt smaller) final reached

end Vegas
