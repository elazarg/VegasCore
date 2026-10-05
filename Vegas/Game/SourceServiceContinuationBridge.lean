/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompletion
import Vegas.Game.SourceServicePhaseStart

/-! # The continuation bridge on the fixed calendar

The completion-stopped bridge (`Vegas.TimedApproximant.response_completion_law`)
holds for every scheduler that completes play, given source continuations
from completion boundaries. On the roster calendar both premises hold:

* the calendar completes play (`rosterScheduler_asyncContract`);
* from every completion boundary the timed players' run has the source
  continuation law (`Vegas.TimedApproximant.roster_boundaryContinuationLaw`).
  A completion boundary on the calendar is either the start of an event's
  block, or a point inside the previous block after that event completed,
  where only clock ticks and the expiry of the completed event remain.

The configuration law when the decision's event completes is the
configuration law at the end of the event's block
(`Vegas.TimedApproximant.completionConfigLaw_eq_phaseConfigLaw`): before
completion only roster visits run, which change no configuration, and after it
only ticks and an expiry of the completed event. Together these give the
calendar bridge `Vegas.TimedApproximant.response_continuation_law`.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Quiet

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- A response records the view it was chosen at. -/
theorem respond_records_view (execution : (application setup leaks).Execution) (who : Player)
    (action : (application setup leaks).Action) :
    ∃ entry ∈ (execution.respond (application setup leaks) who action).recall who,
      entry.beforeView = execution.observe (application setup leaks) who := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  | some transmission =>
      simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

/-- Recorded responses persist through a scheduler round. -/
theorem round_recall_mono (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (execution next : (application setup leaks).Execution)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support)
    (who : Player) : execution.recall who ⊆ next.recall who := by
  let app := application setup leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have recallEq := app.environmentStep_recall execution middle command moved
  change next ∈ (app.resume players (command.actor? app) middle).support at resumed
  cases active : command.actor? app with
  | none =>
      rw [active] at resumed
      simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
      subst resumed
      intro entry member
      rw [recallEq]
      exact member
  | some actor =>
      rw [active] at resumed
      change next ∈ (app.invoke players actor middle).support at resumed
      rw [ReactiveApplication.invoke, PMF.support_map] at resumed
      obtain ⟨response, _, rfl⟩ := resumed
      intro entry member
      exact app.respond_recall_mono middle actor who response (by rw [recallEq]; exact member)

/-- Recorded responses persist through scheduler rounds. -/
theorem runRounds_recall_mono (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (count : Nat)
    (execution next : (application setup leaks).Execution)
    (reached : next ∈ ((application setup leaks).runRounds scheduler players count
      execution).support) (who : Player) : execution.recall who ⊆ next.recall who := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact List.Subset.refl _
  | succ count ih =>
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact List.Subset.trans
        (round_recall_mono setup leaks scheduler players execution middle moved who)
        (ih middle rest)

/-- A roster instruction is quiet for `event` when it is a player visit, a clock
tick, or the expiry of `event` after it completed. -/
def QuietInstruction (event : (graph setup).EventId) (config : (graph setup).Config) :
    ServiceInstruction (graph setup) → Prop
  | .player _ => True
  | .tick => True
  | .expire expired => expired = event ∧ event ∈ config.cut.completed
  | _ => False

/-- A quiet instruction leaves the configuration unchanged. -/
theorem interactionStep_config_quiet (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (event : (graph setup).EventId)
    (instruction : ServiceInstruction (graph setup))
    (execution next : (application setup leaks).Execution)
    (quiet : QuietInstruction setup event execution.application.config instruction)
    (reached : next ∈ ((runtime setup).interactionStep leaks players network instruction
      execution).support) :
    next.application.config = execution.application.config := by
  let app := application setup leaks
  cases instruction with
  | player who =>
      simp only [interactionStep, interactionInstruction, PMF.pure_bind] at reached
      rw [ReactiveApplication.dispatch, PMF.support_bind] at reached
      obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp reached
      have sameApp : middle.application = execution.application := by
        unfold ReactiveApplication.Execution.environmentStep at moved
        rw [PMF.support_map] at moved
        obtain ⟨updated, supported, rfl⟩ := moved
        rw [PMF.support_map] at supported
        obtain ⟨_, _, rfl⟩ := supported
        rfl
      change next ∈ (app.invoke players who middle).support at resumed
      rw [ReactiveApplication.invoke, PMF.support_map] at resumed
      obtain ⟨response, _, rfl⟩ := resumed
      rw [((runtime setup).reactive_respond_application leaks middle who response).1, sameApp]
  | tick =>
      simp only [interactionStep, interactionInstruction, PMF.pure_bind] at reached
      rw [ReactiveApplication.dispatch, PMF.support_bind] at reached
      obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp reached
      change next ∈ (PMF.pure middle).support at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      have member := (applicationStep_facts execution next .advanceClock moved).1
      simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at member
      rw [member]
  | expire expired =>
      obtain ⟨rfl, finished⟩ := quiet
      simp only [interactionStep, interactionInstruction, PMF.pure_bind] at reached
      rw [ReactiveApplication.dispatch, PMF.support_bind] at reached
      obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp reached
      change next ∈ (PMF.pure middle).support at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      have member := (applicationStep_facts execution next (.expire expired) moved).1
      rw [environmentStep_expire_of_not_ready (runtime setup) _ expired
        (fun ready => ready.1 finished), PMF.mem_support_pure_iff] at member
      rw [member]
  | wire => exact quiet.elim
  | includeLatest _ _ => exact quiet.elim
  | sample _ => exact quiet.elim

/-- A plan of quiet instructions leaves the configuration unchanged. -/
theorem runInteractionPlan_config_quiet (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (event : (graph setup).EventId) :
    ∀ (plan : List (ServiceInstruction (graph setup)))
      (execution next : (application setup leaks).Execution),
      (∀ instruction ∈ plan,
        QuietInstruction setup event execution.application.config instruction) →
      next ∈ ((runtime setup).runInteractionPlan leaks players network plan execution).support →
      next.application.config = execution.application.config
  | [], execution, next, _, reached => by
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | instruction :: rest, execution, next, quiet, reached => by
      rw [EventGraphRuntime.runInteractionPlan, PMF.support_bind] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp reached
      have first := interactionStep_config_quiet setup leaks players network event instruction
        execution middle (quiet instruction List.mem_cons_self) moved
      rw [runInteractionPlan_config_quiet players network event rest middle next
        (fun other member => first ▸ quiet other (List.mem_cons_of_mem _ member)) later, first]

/-- After its first instruction, the rest of an event's block is quiet once the
event has completed: only clock ticks and the event's expiry remain. -/
theorem rosterPhaseEnding_drop_quiet (event : (graph setup).EventId) (count : Nat)
    (late : 0 < count) (config : (graph setup).Config)
    (finished : event ∈ config.cut.completed) :
    ∀ instruction ∈ (rosterPhaseEnding setup event).drop count,
      QuietInstruction setup event config instruction := by
  intro instruction member
  have shape : rosterPhaseEnding setup event =
      (match (graph setup).actor? event with
        | none => ServiceInstruction.sample event
        | some owner => .includeLatest event owner) ::
        (List.replicate (event.val + 1) .tick ++ [.expire event]) := by
    unfold rosterPhaseEnding
    cases (graph setup).actor? event <;> rfl
  obtain ⟨rest, rfl⟩ : ∃ rest, count = rest + 1 := ⟨count - 1, by omega⟩
  rw [shape, List.drop_succ_cons] at member
  rcases List.mem_append.mp (List.mem_of_mem_drop member) with ticking | expiring
  · rw [(List.mem_replicate.mp ticking).2]
    exact True.intro
  · rw [List.mem_singleton.mp expiring]
    exact ⟨rfl, finished⟩

/-- The rest of an event's block after its settlement instruction is quiet
once the event has completed. -/
theorem rosterBlock_drop_quiet (rosters : (graph setup).EventId → List Player)
    (event : (graph setup).EventId) (offset : Nat) (late : (rosters event).length < offset)
    (config : (graph setup).Config) (finished : event ∈ config.cut.completed) :
    ∀ instruction ∈ (rosterBlock setup rosters event).drop offset,
      QuietInstruction setup event config instruction := by
  intro instruction member
  rw [rosterBlock_eq_ending, List.drop_append,
    List.drop_eq_nil_of_le (by rw [List.length_map]; omega), List.nil_append,
    List.length_map] at member
  exact rosterPhaseEnding_drop_quiet setup event _ (by omega) config finished instruction member

end Quiet

variable [Fintype Player]

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

omit [Fintype Player] in
/-- The calendar completes play. -/
theorem roster_completesPlay :
    CompletesPlay (runtime service.setup) service.leaks (initialLaw service.setup)
      service.planLength service.scheduler :=
  (rosterScheduler_asyncContract service.setup service.leaks service.rosters service.network
    service.opportunities).completes

omit [Fintype Player] in
theorem plan_take_prefix (rank : Nat) :
    (rosterPlan service.setup service.rosters).take
        (rosterPlanPrefix service.setup service.rosters rank).length =
      rosterPlanPrefix service.setup service.rosters rank := by
  obtain ⟨suffix, split⟩ := rosterPlanPrefix_isPrefix service.setup service.rosters rank
  rw [← split]
  exact List.take_left

/-- A supported execution at the start of an event's block has completed
exactly the earlier events. -/
theorem blockStart_ordered (event : (graph service.setup).EventId)
    (execution : (application service.setup service.leaks).Execution)
    (supported : execution ∈ ((application service.setup service.leaks).roundsFrom
      (initialLaw service.setup) service.scheduler approx.players
      execution.environmentRecall.length).support)
    (position : execution.environmentRecall.length =
      (rosterPlanPrefix service.setup service.rosters event.val).length) :
    execution.application.config.cut.IsPrefix event.val := by
  have bounded : execution.environmentRecall.length ≤ service.planLength := by
    rw [position]
    exact (rosterPlanPrefix_isPrefix service.setup service.rosters event.val).length_le
  obtain ⟨trace⟩ := service.menu.trace_roundsFrom_of_admissible (initialLaw service.setup)
    service.planLength service.scheduler approx.players approx.covered _ bounded execution
    supported
  obtain ⟨_, _, _, _, _, boundary⟩ := sourceService_phase_boundary service.setup service.leaks
    service.bounds service.values service.capacity service.rosters service.opportunities.binding
    service.network ⟨_, none, execution⟩ trace rfl event
    (by change (rosterPlan service.setup service.rosters).take
          execution.environmentRecall.length = _
        rw [position]
        exact plan_take_prefix (service := service) event.val)
  exact boundary.ordered

/-- From the start of a block, the timed players' run to the horizon has the
source continuation law. -/
theorem blockStart_continuation (focal : Player) (rank : Nat)
    (within : rank ≤ (graph service.setup).order.eventCount)
    (execution : (application service.setup service.leaks).Execution)
    (supported : execution ∈ ((application service.setup service.leaks).roundsFrom
      (initialLaw service.setup) service.scheduler approx.players
      execution.environmentRecall.length).support)
    (position : execution.environmentRecall.length =
      (rosterPlanPrefix service.setup service.rosters rank).length) :
    ((application service.setup service.leaks).runToHorizon service.scheduler approx.players
      service.planLength execution).map (fun final => sourceReadout service.setup service.leaks
        ((application service.setup service.leaks).finished final)) =
      (service.setup.continuationLaw approx.profile
        (sourceServicePrefix? service.setup rank execution.application.config)).map some := by
  have whole := rosterPlanPrefix_append_suffix service.setup service.rosters rank
  have lengths := congrArg List.length whole
  rw [List.length_append] at lengths
  have bounded : execution.environmentRecall.length ≤ service.planLength := by
    change _ ≤ (rosterPlan service.setup service.rosters).length
    omega
  have prefixLaw := supported
  rw [roster_roundsFrom service.setup service.leaks service.rosters service.network
    approx.players _ bounded, position, plan_take_prefix] at prefixLaw
  have rounds := roster_segment_rounds service.setup service.leaks service.rosters
    service.network approx.players (rosterPlanPrefix service.setup service.rosters rank)
    (rosterPlanSuffix service.setup service.rosters rank) [] (by rw [List.append_nil, whole])
    execution position
  have count : service.planLength - execution.environmentRecall.length =
      (rosterPlanSuffix service.setup service.rosters rank).length := by
    change (rosterPlan service.setup service.rosters).length - _ = _
    omega
  unfold ReactiveApplication.runToHorizon
  rw [count, rounds]
  exact sourceServiceTimedPolicy_continuation_law service.setup service.leaks service.bounds
    service.values service.capacity service.rosters service.opportunities.binding approx.timing
    service.network approx.profile approx.covered approx.effective focal rank within execution
    prefixLaw

/-- On the calendar, no completion boundary lies inside an event's block
after its first visit while the event is unfinished: that visit recorded a
response seeing the event ready. -/
theorem roster_visited_touched (current : (graph service.setup).EventId) (first : Player)
    (others : List Player) (rosterEq : service.rosters current = first :: others) (later : Nat)
    (execution : (application service.setup service.leaks).Execution)
    (supported : execution ∈ ((application service.setup service.leaks).roundsFrom
      (initialLaw service.setup) service.scheduler approx.players
      ((rosterPlanPrefix service.setup service.rosters current.val).length +
        (later + 1))).support) :
    ¬ Untouched service.setup service.leaks current execution := by
  let app := application service.setup service.leaks
  intro untouched
  unfold ReactiveApplication.roundsFrom at supported
  rw [PMF.support_bind] at supported
  obtain ⟨state, stateMem, reached⟩ := Set.mem_iUnion₂.mp supported
  rw [ReactiveApplication.runRounds_add, PMF.support_bind] at reached
  obtain ⟨start, startMem, rest⟩ := Set.mem_iUnion₂.mp reached
  rw [ReactiveApplication.runRounds, PMF.support_bind] at rest
  obtain ⟨visited, visitedMem, rest⟩ := Set.mem_iUnion₂.mp rest
  have startSupported : start ∈ (app.roundsFrom (initialLaw service.setup) service.scheduler
      approx.players (rosterPlanPrefix service.setup service.rosters current.val).length).support :=
    by
      unfold ReactiveApplication.roundsFrom
      rw [PMF.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨state, stateMem, startMem⟩
  have startLength := app.roundsFrom_recall _ _ _ _ start startSupported
  have startOrdered := approx.blockStart_ordered current start
    (by rw [startLength]; exact startSupported) startLength
  have blockLength := rosterBlock_length service.setup service.rosters current
  have inside : 0 < (service.rosters current).length := by rw [rosterEq]; simp
  have firstVisit := rosterPlan_getElem_block service.setup service.rosters current 0 (by omega)
  rw [Nat.add_zero, rosterBlock_roster service.setup service.rosters current 0 inside] at firstVisit
  have named : (service.rosters current)[0]'inside = first :=
    (List.getElem?_eq_some_iff.mp (show (service.rosters current)[0]? = some first by
      rw [rosterEq]; rfl)).2
  rw [named] at firstVisit
  have selected : (rosterPlan service.setup service.rosters)[start.environmentRecall.length]? =
      some (.player first) := by
    rw [startLength]
    exact firstVisit
  have step : app.round service.scheduler approx.players start =
      (runtime service.setup).interactionStep service.leaks approx.players service.network
        (.player first) start := by
    simp only [ReactiveApplication.round, SourceServiceSpec.scheduler, rosterScheduler, selected,
      interactionStep]
    rfl
  rw [step] at visitedMem
  simp only [interactionStep, interactionInstruction, PMF.pure_bind] at visitedMem
  rw [ReactiveApplication.dispatch, PMF.support_bind] at visitedMem
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp visitedMem
  have sameApp : middle.application = start.application := by
    unfold ReactiveApplication.Execution.environmentStep at moved
    rw [PMF.support_map] at moved
    obtain ⟨updated, supportedUpdate, rfl⟩ := moved
    rw [PMF.support_map] at supportedUpdate
    obtain ⟨_, _, rfl⟩ := supportedUpdate
    rfl
  change visited ∈ (app.invoke approx.players first middle).support at resumed
  rw [ReactiveApplication.invoke, PMF.support_map] at resumed
  obtain ⟨response, _, rfl⟩ := resumed
  obtain ⟨entry, entryMem, view⟩ :=
    respond_records_view service.setup service.leaks middle first response
  have persists := runRounds_recall_mono service.setup service.leaks service.scheduler
    approx.players later _ execution rest first entryMem
  apply untouched first entry persists
  rw [view]
  change middle.application.publicView.EventReady current
  rw [State.publicView_eventReady, sameApp]
  exact (ready_iff_rank service.setup _ current.val startOrdered current).mpr rfl

/-- **Calendar boundary continuations.** From every completion boundary within
the horizon, the timed players' run has the source continuation law. A
boundary is either the start of a block, or a point inside a block after the
block's event completed, followed only by ticks and that event's expiry. -/
theorem roster_boundaryContinuationLaw (focal : Player) :
    BoundaryContinuationLaw service.setup service.leaks service.scheduler service.planLength
      approx.players approx.profile := by
  intro rank execution boundary bounded
  let app := application service.setup service.leaks
  obtain ⟨menuTrace⟩ := service.menu.trace_roundsFrom_of_admissible (initialLaw service.setup)
    service.planLength service.scheduler approx.players approx.covered _ bounded execution
    boundary.supported
  have reach := rosterReach_history service.setup service.leaks service.rosters service.network
    (service.menu.toRawTrace _ _ _ menuTrace)
  rcases reach with ⟨current, offset, phase⟩ | ⟨remainingZero, _, done⟩
  · have position : execution.environmentRecall.length =
        (rosterPlanPrefix service.setup service.rosters current.val).length + offset :=
      phase.position
    have inside := phase.inside
    have succLength := congrArg List.length
      (rosterPlanPrefix_succ service.setup service.rosters current)
    rw [List.length_append] at succLength
    have planLength := congrArg List.length
      (rosterPlanPrefix_append_suffix service.setup service.rosters (current.val + 1))
    rw [List.length_append] at planLength
    rcases phase.completed with ordered | ⟨late, advanced⟩
    · have rankEq : rank = current.val := isPrefix_unique boundary.ordered ordered
      subst rankEq
      by_cases start : offset = 0
      · subst start
        exact approx.blockStart_continuation focal current.val (Nat.le_of_lt current.isLt)
          execution boundary.supported position
      · exfalso
        cases rosterEq : service.rosters current with
        | nil =>
            cases owned : (graph service.setup).actor? current with
            | none =>
                have completed := phase.sampled owned (by rw [rosterEq, List.length_nil]; omega)
                exact isPrefix_succ_false current ordered completed
            | some owner =>
                have member := service.opportunities current owner owned
                rw [rosterEq] at member
                cases member
        | cons first others =>
            obtain ⟨later, rfl⟩ : ∃ later, offset = later + 1 := ⟨offset - 1, by omega⟩
            have supported := boundary.supported
            rw [position] at supported
            exact approx.roster_visited_touched current first others rosterEq later execution
              supported (boundary.untouched current rfl)
    · have rankEq : rank = current.val + 1 := isPrefix_unique boundary.ordered advanced
      subst rankEq
      have finished : current ∈ execution.application.config.cut.completed :=
        (advanced.2 current).mpr (Nat.lt_succ_self _)
      have splitPlan : rosterPlan service.setup service.rosters =
          (rosterPlanPrefix service.setup service.rosters current.val ++
            (rosterBlock service.setup service.rosters current).take offset) ++
          (rosterBlock service.setup service.rosters current).drop offset ++
            rosterPlanSuffix service.setup service.rosters (current.val + 1) := by
        rw [List.append_assoc (rosterPlanPrefix _ _ _), List.take_append_drop,
          ← rosterPlanPrefix_succ service.setup service.rosters current,
          rosterPlanPrefix_append_suffix]
      have rounds := roster_segment_rounds service.setup service.leaks service.rosters
        service.network approx.players _ _ _ splitPlan execution
        (by rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)]; exact position)
      rw [List.length_drop] at rounds
      have countSplit : service.planLength - execution.environmentRecall.length =
          ((rosterBlock service.setup service.rosters current).length - offset) +
            (service.planLength -
              (rosterPlanPrefix service.setup service.rosters (current.val + 1)).length) := by
        change (rosterPlan service.setup service.rosters).length - _ =
          _ + ((rosterPlan service.setup service.rosters).length - _)
        omega
      unfold ReactiveApplication.runToHorizon
      rw [countSplit, ReactiveApplication.runRounds_add, PMF.map_bind]
      calc
        _ = (app.runRounds service.scheduler approx.players
              ((rosterBlock service.setup service.rosters current).length - offset)
              execution).bind (fun _ =>
            (service.setup.continuationLaw approx.profile (sourceServicePrefix? service.setup
              (current.val + 1) execution.application.config)).map some) := by
          apply bind_congr_on_support _
          intro next reached
          have plan := reached
          rw [rounds] at plan
          have nextConfig := runInteractionPlan_config_quiet service.setup service.leaks
            approx.players service.network current _ execution next
            (rosterBlock_drop_quiet service.setup service.rosters current offset (by omega)
              execution.application.config finished) plan
          have nextLength := app.runRounds_environmentRecall_length service.scheduler
            approx.players _ execution next reached
          have nextPosition : next.environmentRecall.length =
              (rosterPlanPrefix service.setup service.rosters (current.val + 1)).length := by
            omega
          have nextSupported := app.roundsFrom_runRounds service.scheduler approx.players
            (initialLaw service.setup) _ _ execution next boundary.supported reached
          rw [← nextLength] at nextSupported
          have law := approx.blockStart_continuation focal (current.val + 1) current.isLt next
            nextSupported nextPosition
          unfold ReactiveApplication.runToHorizon at law
          rw [nextPosition, nextConfig] at law
          exact law
        _ = _ := PMF.bind_const _ _
  · have rankEq : rank = (graph service.setup).order.eventCount :=
      isPrefix_unique boundary.ordered done
    subst rankEq
    have position : execution.environmentRecall.length =
        (rosterPlanPrefix service.setup service.rosters
          (graph service.setup).order.eventCount).length := by
      rw [rosterPlanPrefix_eventCount]
      change (rosterPlan service.setup service.rosters).length -
        execution.environmentRecall.length = 0 at remainingZero
      change _ ≤ (rosterPlan service.setup service.rosters).length at bounded
      omega
    exact approx.blockStart_continuation focal _ le_rfl execution boundary.supported position

/-- **Calendar completion law.** On the calendar, the configuration law when
the decision's event completes is the configuration law at the end of the
event's block. -/
theorem completionConfigLaw_eq_phaseConfigLaw {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action)
    (allowed : response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    approx.completionConfigLaw phase response = approx.phaseConfigLaw phase response := by
  let app := application service.setup service.leaks
  let stop := fun final : app.Execution => phase.event ∈ final.application.config.cut.completed
  let responded := execution.respond app who response
  have position : responded.environmentRecall.length = phase.before.length + 1 := by
    change (execution.respond app who response).environmentRecall.length = _
    rw [ReactiveApplication.respond_environmentRecall]
    exact phase.position_before
  have total := congrArg List.length phase.plan_split
  simp only [List.length_append, List.length_singleton] at total
  have endingLength : (rosterPhaseEnding service.setup phase.event).length =
      phase.event.val + 3 := by
    unfold rosterPhaseEnding
    cases (graph service.setup).actor? phase.event <;> simp
  have tailLength : phase.tail.length = phase.visits.length + (phase.event.val + 3) := by
    rw [DecisionPhase.tail, List.length_append, List.length_map, endingLength]
  have segment : ∀ used, used ≤ phase.tail.length → ∀ y : app.Execution,
      y.environmentRecall.length = phase.before.length + 1 + used →
      app.runRounds service.scheduler approx.players (phase.tail.length - used) y =
        (runtime service.setup).runInteractionPlan service.leaks approx.players service.network
          (phase.tail.drop used) y := by
    intro used within y located
    have rounds := roster_segment_rounds service.setup service.leaks service.rosters
      service.network approx.players
      ((phase.before ++ [ServiceInstruction.player who]) ++ phase.tail.take used)
      (phase.tail.drop used) phase.later
      (by
        rw [phase.plan_split, List.append_assoc _ (phase.tail.take used), List.take_append_drop]
        simp only [List.append_assoc]) y
      (by rw [List.length_append, List.length_append, List.length_singleton, List.length_take,
        Nat.min_eq_left within]; exact located)
    rwa [List.length_drop] at rounds
  have prefixRounds : ∀ used, used ≤ phase.tail.length →
      app.runRounds service.scheduler approx.players used responded =
        (runtime service.setup).runInteractionPlan service.leaks approx.players service.network
          (phase.tail.take used) responded := by
    intro used within
    have rounds := roster_segment_rounds service.setup service.leaks service.rosters
      service.network approx.players (phase.before ++ [ServiceInstruction.player who])
      (phase.tail.take used) (phase.tail.drop used ++ phase.later)
      (by rw [phase.plan_split, List.append_assoc _ (phase.tail.take used),
        ← List.append_assoc (phase.tail.take used), List.take_append_drop]) responded
      (by rw [List.length_append, List.length_singleton]; exact position)
    rwa [List.length_take, Nat.min_eq_left within] at rounds
  have visitsQuiet : ∀ used, used ≤ phase.visits.length → ∀ y ∈ (app.runRounds
      service.scheduler approx.players used responded).support,
      y.application.config = execution.application.config := by
    intro used early y reached
    rw [prefixRounds used (by omega)] at reached
    have quiet := runInteractionPlan_config_quiet service.setup service.leaks approx.players
      service.network phase.event _ _ y (fun instruction member => by
        rw [DecisionPhase.tail,
          List.take_append_of_le_length (by rw [List.length_map]; exact early)] at member
        obtain ⟨visitor, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take member)
        exact True.intro) reached
    rw [quiet]
    exact ((runtime service.setup).reactive_respond_application service.leaks execution who
      response).1
  have prefixLength : (rosterPlanPrefix service.setup service.rosters
      (phase.event.val + 1)).length = phase.before.length + 1 + phase.tail.length := by
    rw [phase.prefix_split]
    simp only [List.length_append, List.length_cons]
    omega
  have blockEnd : ∀ y ∈ (app.runRounds service.scheduler approx.players phase.tail.length
      responded).support, phase.event ∈ y.application.config.cut.completed := by
    intro y reached
    have supported := service.menu.fullyMixed_response_rounds_support (initialLaw service.setup)
      service.planLength service.scheduler approx.players approx.covered approx.assessment
      approx.strategy approx.mixed who remaining execution trace response allowed _ y reached
    have length := app.runRounds_environmentRecall_length service.scheduler approx.players _
      responded y reached
    rw [position] at length
    by_cases last : phase.event.val + 1 < (graph service.setup).order.eventCount
    · have ordered := approx.blockStart_ordered ⟨phase.event.val + 1, last⟩ y supported
        (by rw [length]; exact prefixLength.symm)
      exact (ordered.2 phase.event).mpr (Nat.lt_succ_self _)
    · have final : phase.event.val + 1 = (graph service.setup).order.eventCount := by
        have := phase.event.isLt
        omega
      rw [final, rosterPlanPrefix_eventCount] at prefixLength
      have bounded : y.environmentRecall.length ≤ service.planLength := by
        change _ ≤ (rosterPlan service.setup service.rosters).length
        omega
      obtain ⟨yTrace⟩ := service.menu.trace_roundsFrom_of_admissible (initialLaw service.setup)
        service.planLength service.scheduler approx.players approx.covered _ bounded y supported
      have terminal := roster_completesPlay (service := service) _
        (service.menu.toRawTrace _ _ _ yTrace) (by
          change service.planLength - y.environmentRecall.length = 0 ∧ _
          refine ⟨?_, rfl⟩
          change (rosterPlan service.setup service.rosters).length - _ = 0
          omega)
      change y.application.config.cut.completed = Finset.univ at terminal
      rw [terminal]
      exact Finset.mem_univ _
  have stopped : ∀ y ∈ (app.runUntil service.scheduler approx.players stop phase.tail.length
      responded).support, stop y ∧
        (app.runRounds service.scheduler approx.players (phase.tail.length -
          (y.environmentRecall.length - responded.environmentRecall.length)) y).map
            (fun final => final.application.config) = PMF.pure y.application.config := by
    intro y reached
    obtain ⟨used, within, rounds, length⟩ := app.runUntil_runRounds service.scheduler
      approx.players stop _ responded y reached
    have halted : stop y := by
      rcases app.runUntil_stopped service.scheduler approx.players stop _ responded y reached with
        done | spent
      · exact done
      · have usedEq : used = phase.tail.length := by omega
        subst usedEq
        exact blockEnd y rounds
    refine ⟨halted, ?_⟩
    have afterVisits : phase.visits.length < used := by
      by_contra early
      have same := visitsQuiet used (by omega) y rounds
      exact phase.ready.1 (same ▸ halted)
    have usedEq : y.environmentRecall.length - responded.environmentRecall.length = used := by
      omega
    have quietTail : ∀ instruction ∈ phase.tail.drop used,
        QuietInstruction service.setup phase.event y.application.config instruction := by
      intro instruction member
      rw [DecisionPhase.tail, List.drop_append,
        List.drop_eq_nil_of_le (by rw [List.length_map]; omega), List.nil_append,
        List.length_map] at member
      exact rosterPhaseEnding_drop_quiet service.setup phase.event _ (by omega)
        y.application.config halted instruction member
    rw [usedEq, segment used within y (by rw [length, position])]
    rw [map_congr_on_support _ (g := fun _ => y.application.config) (fun next member =>
      runInteractionPlan_config_quiet service.setup service.leaks approx.players service.network
        phase.event _ y next quietTail member)]
    exact PMF.map_const _ _
  have phaseRounds : (runtime service.setup).runInteractionPlan service.leaks approx.players
      service.network phase.tail responded =
        app.runRounds service.scheduler approx.players phase.tail.length responded := by
    have rounds := segment 0 (Nat.zero_le _) responded (by rw [position])
    rw [List.drop_zero, Nat.sub_zero] at rounds
    exact rounds.symm
  have decomposed : app.runRounds service.scheduler approx.players phase.tail.length responded =
      (app.runUntil service.scheduler approx.players stop phase.tail.length responded).bind
        (fun y => app.runRounds service.scheduler approx.players (phase.tail.length -
          (y.environmentRecall.length - responded.environmentRecall.length)) y) := by
    have markov := app.runToHorizon_eq_runUntilHorizon_bind service.scheduler approx.players stop
      (responded.environmentRecall.length + phase.tail.length) responded
    unfold ReactiveApplication.runToHorizon ReactiveApplication.runUntilHorizon at markov
    rw [Nat.add_sub_cancel_left] at markov
    rw [markov]
    apply bind_congr_on_support _
    intro y reached
    obtain ⟨used, within, _, length⟩ := app.runUntil_runRounds service.scheduler approx.players
      stop _ responded y reached
    congr 1
    omega
  have fuel : service.planLength - responded.environmentRecall.length =
      phase.tail.length + phase.later.length := by
    rw [position]
    change (rosterPlan service.setup service.rosters).length - _ = _
    omega
  have early : app.runUntilHorizon service.scheduler approx.players stop service.planLength
      responded = app.runUntil service.scheduler approx.players stop phase.tail.length
        responded := by
    unfold ReactiveApplication.runUntilHorizon
    rw [fuel]
    exact app.runUntil_add_of_stopped service.scheduler approx.players stop _ _ responded
      (fun y member => (stopped y member).1)
  unfold completionConfigLaw completionLaw phaseConfigLaw phaseLaw
  change (app.runUntilHorizon service.scheduler approx.players stop service.planLength
    responded).map _ = ((runtime service.setup).runInteractionPlan service.leaks approx.players
      service.network phase.tail responded).map _
  rw [early, phaseRounds, decomposed, PMF.map_bind]
  conv_lhs => rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support _
  intro y member
  exact (stopped y member).2.symm

/-- The single continuation bridge: after any legal response at an actual
decision, the complete typed source terminal law is the source continuation
from the next event boundary, averaged over the actual configuration law at
that boundary, the end of the decision's event block. Responses used as
deviations are included. -/
theorem response_continuation_law {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action)
    (allowed : response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    approx.responseReadout phase response =
      (approx.phaseConfigLaw phase response).bind
        (approx.boundaryContinuation (phase.event.val + 1)) := by
  rw [approx.response_completion_law (roster_completesPlay (service := service))
    (approx.roster_boundaryContinuationLaw who) trace phase response allowed,
    approx.completionConfigLaw_eq_phaseConfigLaw trace phase response allowed]

/-- Two legal responses with the same next-boundary configuration law have the
same complete typed source terminal law. -/
theorem responseReadout_congr {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (first second : (application service.setup service.leaks).Action)
    (firstAllowed : first ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (secondAllowed : second ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (same : approx.phaseConfigLaw phase first = approx.phaseConfigLaw phase second) :
    approx.responseReadout phase first = approx.responseReadout phase second := by
  rw [approx.response_continuation_law trace phase first firstAllowed,
    approx.response_continuation_law trace phase second secondAllowed, same]

open Classical in
/-- At a site where every legal response leaves the same configuration law at
the next event boundary, every local lottery has the prescribed complete
continuation law, for every belief over the site. -/
theorem comparison_eq_of_phase_invariant (who : Player)
    (site : service.model.InformationSite who)
    (invariant : ∀ (history : (service.menu.protocol (initialLaw service.setup)
        service.planLength service.scheduler).History) remaining execution,
      history.state = some ⟨remaining, some who, execution⟩ →
      service.model.infoOf who history.trace = site.1 →
      ∀ (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
        (first second : (application service.setup service.leaks).Action),
        first ∈ service.menu.actions who (execution.recall who)
          (execution.observe (application service.setup service.leaks) who) →
        second ∈ service.menu.actions who (execution.recall who)
          (execution.observe (application service.setup service.leaks) who) →
        approx.phaseConfigLaw phase first = approx.phaseConfigLaw phase second)
    (law : PMF (service.model.Choice who site.1)) :
    let comparison := service.model.assessmentComparisonWith (service.model.truncatedRunner
        service.fuel) service.readout
      approx.assessment who (site, (approx.assessment.strategy who).withLaw site.1 law)
    comparison.alternative = comparison.prescribed := by
  intro comparison
  simp only [comparison, InformationModel.assessmentComparisonWith,
    InformationModel.assessmentLawWith, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  have active := InformationModel.InformationSite.active service.model site history
  obtain ⟨control, current⟩ : ∃ control, history.1.state = some control := by
    cases state : history.1.state with
    | none => rw [state] at active; cases active
    | some control => exact ⟨control, rfl⟩
  have actor : control.actor = some who := by rw [current] at active; exact active
  obtain ⟨remaining, actorValue, execution⟩ := control
  change actorValue = some who at actor
  subst actorValue
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    current ▸ history.1.trace
  obtain ⟨phase⟩ := service.exists_decisionPhase who remaining execution trace
  let reference := (approx.assessment.strategy who site.1).support_nonempty.choose
  have referenceAllowed := service.choice_allowed history.1 current history.2 reference
  have constant (choiceLaw : PMF (service.model.Choice who site.1)) :
      (service.model.runBehavioralFrom (Profile.update (sig := service.model.behavioralSignature)
        approx.assessment.strategy who ((approx.assessment.strategy who).withLaw site.1 choiceLaw))
          service.fuel history.1).map service.readout =
        approx.responseReadout phase (reference.1.getD ⟨none⟩) := by
    rw [approx.local_law_readout history.1 current phase history.2 choiceLaw, PMF.bind_map]
    calc
      _ = choiceLaw.bind (fun _ =>
          approx.responseReadout phase (reference.1.getD ⟨none⟩)) := by
        apply bind_congr_on_support _
        intro choice _
        have allowed := service.choice_allowed history.1 current history.2 choice
        exact approx.responseReadout_congr trace phase _ _ allowed referenceAllowed
          (invariant history.1 remaining execution current history.2 phase _ _ allowed
            referenceAllowed)
      _ = _ := PMF.bind_const _ _
  have prescribed := constant (approx.assessment.strategy who site.1)
  rw [InformationModel.BehavioralPolicy.withLaw_eq_self] at prescribed
  exact (constant law).trans prescribed.symm

end TimedApproximant

end Vegas
