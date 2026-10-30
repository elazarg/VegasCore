/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceRosterPosition
import Vegas.Game.ServiceRosterFacts
import Vegas.EventGraph.CanonicalStep
import Vegas.Pending.ReactiveEventStability
import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.ReactiveServiceOpportunity
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveRecallInvariant
import Interaction.ReactiveHistory
import Interaction.ReactiveResponseAccounting

/-! # Public calendar invariants through automatic completion

The calendar position and its entry observation determine whether a block is
obsolete. Dynamic clock bounds permit a completed prefix to jump across any
number of defaulted events and retain early responses at surviving events.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A proof certificate for a position of the public roster calendar. The
entry clock and obsolete flag describe recorded public data, not runtime state. -/
structure RosterCalendarPhase (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (event : (graph setup).EventId) (offset entryClock : Nat) (obsolete : Bool)
    (control : (application setup (Vegas.runtime setup) leaks).Control) : Prop where
  position : control.execution.environmentRecall.length =
    (rosterPlanPrefix setup rosters event.val).length + offset
  inside : offset < (rosterBlock setup rosters event).length
  remaining : control.remaining + control.execution.environmentRecall.length =
    (rosterPlan setup rosters).length
  classified : rosterBlockCompleted setup leaks rosters control.execution.environmentRecall
      (control.execution.observeEnvironment (application setup (Vegas.runtime setup) leaks))
      event ↔ obsolete = true
  prior : ∀ query : (graph setup).EventId, query.val < event.val →
    query ∈ control.execution.application.config.cut.completed
  obsolete_done : obsolete = true → event ∈ control.execution.application.config.cut.completed
  live_prefix : obsolete = false → offset ≤ (rosters event).length →
    control.execution.application.config.cut.IsPrefix event.val
  sampled : (graph setup).actor? event = none → (rosters event).length < offset →
    event ∈ control.execution.application.config.cut.completed
  clock : control.execution.application.clock =
    entryClock + (if obsolete then 0 else offset - ((rosters event).length + 1))
  entered : ∀ entered, control.execution.application.activatedAt event = some entered →
    entered ≤ entryClock ∧ entryClock ≤ entered + event.val
  future : ∀ query : (graph setup).EventId, event.val < query.val → ∀ entered,
    control.execution.application.activatedAt query = some entered →
    control.execution.application.clock ≤ entered + query.val
  future_started : obsolete = false → ∀ query : (graph setup).EventId,
    event.val < query.val → ∀ entered,
      control.execution.application.activatedAt query = some entered → entryClock ≤ entered
  opportunity : ∀ owner, (graph setup).actor? event = some owner →
    owner ∈ (rosters event).take offset → ∀ entered,
      control.execution.application.config.cut.Ready event →
      control.execution.application.activatedAt event = some entered →
      OwnerActivatedSince (runtime setup) leaks control.execution.environmentRecall event
        owner entered
  responses : ∀ who, ∀ entry ∈ control.execution.recall who, ∀ query : (graph setup).EventId,
    entry.beforeView.application.publicView.EventReady query →
    query ∉ control.execution.application.config.cut.completed →
    entry.beforeView.application.publicView.clock = entryClock ∧
      (query = event ∨ obsolete = true)
  activation : ∀ who, control.actor = some who → 0 < offset ∧ offset ≤ (rosters event).length
  inclusion : (rosters event).length < offset →
    event ∉ control.execution.application.config.cut.completed → ∀ owner,
      (graph setup).actor? event = some owner →
      ∀ (earlier later : List (application setup (Vegas.runtime setup) leaks).PlayerEntry)
        entry message,
        control.execution.recall owner = earlier ++ entry :: later →
        entry.emitted = some message → message.sender = owner →
        message.payload.call.event? (graph setup) = some event →
        (∀ other ∈ earlier ++ later,
          ¬ EmitsOtherFor (runtime setup) leaks other event message.id) →
        ∃ accepted, (message.id, accepted) ∈ control.execution.receipts

/-- A public calendar position, or a completed graph at the exhausted horizon. -/
def RosterCalendarInvariant (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) :
    (application setup (Vegas.runtime setup) leaks).ProtocolState → Prop
  | none => True
  | some control => (∃ event offset entryClock obsolete,
      RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control) ∨
      (control.remaining = 0 ∧ control.actor = none ∧
        control.execution.application.config.cut.Terminal)

/-- The initialized native service starts at the first live block or at a terminal graph. -/
theorem RosterCalendarInvariant.initial (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (state : EventGraphRuntime.State (graph setup))
    (supported : state ∈ (initialLaw setup).support) :
    RosterCalendarInvariant setup leaks rosters
      (some ⟨(rosterPlan setup rosters).length, none,
        ReactiveApplication.Execution.initial (application setup (Vegas.runtime setup) leaks)
          state⟩) := by
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
  have invariant := State.initial_invariant (setup.eventInputs initial)
  have empty : (State.initial (setup.eventInputs initial)).config.cut.IsPrefix 0 :=
    EventOrder.Cut.empty_isPrefix _
  by_cases nonempty : 0 < (graph setup).order.eventCount
  · left
    refine ⟨⟨0, nonempty⟩, 0, 0, false, ?_⟩
    exact {
      position := by
        change 0 = (rosterPlanPrefix setup rosters 0).length + 0
        simp only [rosterPlanPrefix, List.take_zero, List.flatMap_nil, List.length_nil,
          Nat.add_zero]
      inside := by rw [rosterBlock_length]; omega
      remaining := by simp [ReactiveApplication.Execution.initial]
      classified := by
        change (⟨0, nonempty⟩ ∈ ([] : List (graph setup).EventId)) ↔ false = true
        constructor
        · intro member; cases member
        · intro impossible; cases impossible
      prior := by
        intro query earlier
        change query.val < 0 at earlier
        omega
      obsolete_done := by intro impossible; cases impossible
      live_prefix := fun _ _ => empty
      sampled := fun _ late => absurd late (Nat.not_lt_zero _)
      clock := by
        change 0 = 0 + (if false = true then 0 else 0 - ((rosters ⟨0, nonempty⟩).length + 1))
        simp
      entered := by
        intro entered activated
        have bound := invariant.activated_le _ entered activated
        change entered ≤ 0 at bound
        exact ⟨bound, Nat.zero_le _⟩
      future := by intro query later entered activated; exact Nat.zero_le _
      future_started := by intro live query later entered activated; exact Nat.zero_le _
      opportunity := by
        intro owner owned member
        simp at member
      responses := by
        intro who entry member
        simp [ReactiveApplication.Execution.initial] at member
      activation := by intro who active; cases active
      inclusion := fun late => absurd late (Nat.not_lt_zero _) }
  · right
    have zero : (graph setup).order.eventCount = 0 := by omega
    refine ⟨?_, rfl, ?_⟩
    · change (rosterPlan setup rosters).length = 0
      have absent : List.finRange (graph setup).order.eventCount = [] :=
        List.eq_nil_of_length_eq_zero (by rw [List.length_finRange, zero])
      rw [rosterPlan, absent]
      rfl
    · unfold EventOrder.Cut.Terminal
      apply Finset.eq_univ_of_forall
      intro event
      have inside : event.val < (graph setup).order.eventCount := event.isLt
      omega

/-- A response retains the public calendar and records the current entry clock. -/
theorem RosterCalendarPhase.respond {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
    {offset entryClock : Nat} {obsolete : Bool}
    {control : (application setup (Vegas.runtime setup) leaks).Control}
    (phase : RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control)
    (who : Player) (active : control.actor = some who)
    (action : (application setup (Vegas.runtime setup) leaks).Action) :
    RosterCalendarPhase setup leaks rosters event offset entryClock obsolete
      { control with
        actor := none
        execution := control.execution.respond (application setup (Vegas.runtime setup) leaks)
          who action } := by
  obtain ⟨configEq, publicEq⟩ :=
    (runtime setup).reactive_respond_application leaks control.execution who action
  have clockEq := congrArg PublicView.clock publicEq
  have activatedEq := congrArg PublicView.activatedAt publicEq
  dsimp only [State.publicView] at clockEq activatedEq
  have recallEq := (application setup (Vegas.runtime setup) leaks).respond_environmentRecall
    control.execution who action
  obtain ⟨positive, early⟩ := phase.activation who active
  have startClock : control.execution.application.clock = entryClock := by
    rw [phase.clock]
    cases obsolete with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
    | true => simp only [↓reduceIte, Nat.add_zero]
  have recorded : (rosterPlanPrefix setup rosters event.val).length <
      control.execution.environmentRecall.length := by rw [phase.position]; omega
  have classified := rosterBlockCompleted_append setup leaks rosters
    control.execution.environmentRecall []
    (control.execution.observeEnvironment (application setup (Vegas.runtime setup) leaks))
    ((control.execution.respond _ who action).observeEnvironment
      (application setup (Vegas.runtime setup) leaks)) event recorded
  simp only [List.append_nil] at classified
  exact {
    position := by
      change (control.execution.respond _ who action).environmentRecall.length = _
      rw [recallEq]
      exact phase.position
    inside := phase.inside
    remaining := by
      change control.remaining +
        (control.execution.respond _ who action).environmentRecall.length = _
      rw [recallEq]
      exact phase.remaining
    classified := by
      change rosterBlockCompleted setup leaks rosters
        (control.execution.respond _ who action).environmentRecall _ event ↔ _
      rw [recallEq, classified]
      exact phase.classified
    prior := by
      change ∀ query, _ → query ∈
        (control.execution.respond _ who action).application.config.cut.completed
      rw [configEq]
      exact phase.prior
    obsolete_done := by
      change _ → event ∈ (control.execution.respond _ who action).application.config.cut.completed
      rw [configEq]
      exact phase.obsolete_done
    live_prefix := by
      change _ → _ → (control.execution.respond _ who action).application.config.cut.IsPrefix _
      rw [configEq]
      exact phase.live_prefix
    sampled := fun owned late => absurd late (by omega)
    clock := by
      change (control.execution.respond _ who action).application.clock = _
      rw [clockEq]
      exact phase.clock
    entered := by
      change ∀ entered, (control.execution.respond _ who action).application.activatedAt event =
        some entered → _
      rw [activatedEq]
      exact phase.entered
    future := by
      change ∀ query, _ → ∀ entered,
        (control.execution.respond _ who action).application.activatedAt query = _ →
          (control.execution.respond _ who action).application.clock ≤ _
      rw [activatedEq, clockEq]
      exact phase.future
    future_started := by
      change _ → ∀ query, _ → ∀ entered,
        (control.execution.respond _ who action).application.activatedAt query = _ → _
      rw [activatedEq]
      exact phase.future_started
    opportunity := by
      change ∀ owner, _ → _ → ∀ entered,
        (control.execution.respond _ who action).application.config.cut.Ready event →
        (control.execution.respond _ who action).application.activatedAt event = _ →
          OwnerActivatedSince (runtime setup) leaks
            (control.execution.respond _ who action).environmentRecall event owner entered
      rw [configEq, activatedEq, recallEq]
      exact phase.opportunity
    responses := by
      intro observer entry member query ready unfinished
      have unfinishedBefore : query ∉ control.execution.application.config.cut.completed := by
        simpa only [configEq] using unfinished
      rcases (application setup (Vegas.runtime setup) leaks).respond_entry_origin
        control.execution who observer action entry member with prior | ⟨_, fresh⟩
      · exact phase.responses observer entry prior query ready unfinishedBefore
      · rw [fresh] at ready ⊢
        change control.execution.application.publicView.EventReady query at ready
        refine ⟨startClock, ?_⟩
        cases same : obsolete with
        | true => exact Or.inr rfl
        | false =>
            have ordered := phase.live_prefix same early
            have readyNow := (State.publicView_eventReady _ query).mp ready
            exact Or.inl (setup.eventGraph.sequentialize_ready_unique _ readyNow
              (ordered.ready event.isLt))
    activation := by intro who noneActive; cases noneActive
    inclusion := fun late => absurd late (by omega) }

/-- A roster activation records a ready owner's opportunity without advancing the clock. -/
theorem RosterCalendarPhase.activate_step
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
    {offset entryClock : Nat} {obsolete : Bool}
    {control : (application setup (Vegas.runtime setup) leaks).Control}
    (phase : RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control)
    (early : offset < (rosters event).length) (who : Player)
    (chosen : (rosters event)[offset]? = some who) (remaining : Nat)
    (counted : control.remaining = remaining + 1)
    (next : (application setup (Vegas.runtime setup) leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep (application setup (Vegas.runtime
      setup) leaks) (.activate who)).support) :
    RosterCalendarPhase setup leaks rosters event (offset + 1) entryClock obsolete
      ⟨remaining, some who, next⟩ := by
  have effects : next.application = control.execution.application ∧
      next.environmentRecall = control.execution.environmentRecall ++
        [⟨control.execution.observeEnvironment _, .activate who⟩] ∧
      next.recall = control.execution.recall := by
    obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
    obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨applicationEq, appended, recallEq⟩ := effects
  have length : next.environmentRecall.length =
      control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have classified := rosterBlockCompleted_record setup leaks rosters
    control.execution.environmentRecall
    (control.execution.observeEnvironment (application setup (Vegas.runtime setup) leaks))
    (next.observeEnvironment (application setup (Vegas.runtime setup) leaks)) event
    (.activate who) (by rw [phase.position]; omega)
  have oldTicks : offset - ((rosters event).length + 1) = 0 := by omega
  have nextTicks : offset + 1 - ((rosters event).length + 1) = 0 := by omega
  exact {
    position := by
      change next.environmentRecall.length = _
      rw [length, phase.position]
      omega
    inside := by rw [rosterBlock_length]; omega
    remaining := by
      change remaining + next.environmentRecall.length = _
      have total := phase.remaining
      rw [counted] at total
      rw [length]
      omega
    classified := by
      change rosterBlockCompleted setup leaks rosters next.environmentRecall _ event ↔ _
      rw [appended, classified]
      exact phase.classified
    prior := by
      change ∀ query, _ → query ∈ next.application.config.cut.completed
      rw [applicationEq]
      exact phase.prior
    obsolete_done := by
      change _ → event ∈ next.application.config.cut.completed
      rw [applicationEq]
      exact phase.obsolete_done
    live_prefix := by
      intro live bound
      change next.application.config.cut.IsPrefix event.val
      rw [applicationEq]
      exact phase.live_prefix live early.le
    sampled := fun owned late => absurd late (by omega)
    clock := by
      change next.application.clock = _
      rw [applicationEq, phase.clock, oldTicks, nextTicks]
    entered := by
      change ∀ entered, next.application.activatedAt event = some entered → _
      rw [applicationEq]
      exact phase.entered
    future := by
      change ∀ query, _ → ∀ entered, next.application.activatedAt query = _ →
        next.application.clock ≤ _
      rw [applicationEq]
      exact phase.future
    future_started := by
      change _ → ∀ query, _ → ∀ entered, next.application.activatedAt query = _ → _
      rw [applicationEq]
      exact phase.future_started
    opportunity := by
      intro owner owned member entered ready activated
      change next.application.config.cut.Ready event at ready
      change next.application.activatedAt event = some entered at activated
      rw [applicationEq] at ready activated
      change OwnerActivatedSince (runtime setup) leaks next.environmentRecall event owner entered
      rw [appended]
      rw [List.take_add_one, chosen] at member
      rcases List.mem_append.mp member with prior | current
      · obtain ⟨entry, inside, command, started, seen⟩ :=
          phase.opportunity owner owned prior entered ready activated
        exact ⟨entry, List.mem_append_left _ inside, command, started, seen⟩
      · have same : owner = who := by simpa using current
        subst owner
        refine ⟨⟨control.execution.observeEnvironment _, .activate who⟩,
          List.mem_append_right _ (List.mem_singleton_self _), rfl, activated, ?_⟩
        exact (State.publicView_eventReady _ event).mpr ready
    responses := by
      change ∀ observer, ∀ entry ∈ next.recall observer, ∀ query, _ →
        query ∉ next.application.config.cut.completed → _
      rw [recallEq, applicationEq]
      exact phase.responses
    activation := by
      intro observer active
      exact ⟨Nat.succ_pos _, by omega⟩
    inclusion := fun late => absurd late (by omega) }

/-- A zero-time operation after the roster retains the public calendar certificate. -/
theorem RosterCalendarPhase.ending_step
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
    {offset entryClock : Nat} {obsolete : Bool}
    {control : (application setup (Vegas.runtime setup) leaks).Control}
    (phase : RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control)
    (atEnding : offset = (rosters event).length)
    {inputs : (graph setup).Inputs}
    (invariant : control.execution.application.Invariant inputs)
    (command : (application setup (Vegas.runtime setup) leaks).Command)
    (actorNone : command.actor? (application setup (Vegas.runtime setup) leaks) = none)
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (next : (application setup (Vegas.runtime setup) leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep (application setup (Vegas.runtime
      setup) leaks) command).support)
    (progress : State.ServiceProgress inputs 0 control.execution.application next.application)
    (origin : State.ActivationOrigin control.execution.application next.application)
    (sampled : (graph setup).actor? event = none →
      event ∈ next.application.config.cut.completed)
    (receipts : ∀ owner, (graph setup).actor? event = some owner →
      ∀ (earlier later : List (application setup (Vegas.runtime setup) leaks).PlayerEntry)
        entry message,
        next.recall owner = earlier ++ entry :: later →
        entry.emitted = some message → message.sender = owner →
        message.payload.call.event? (graph setup) = some event →
        (∀ other ∈ earlier ++ later,
          ¬ EmitsOtherFor (runtime setup) leaks other event message.id) →
        ∃ accepted, (message.id, accepted) ∈ next.receipts) :
    RosterCalendarPhase setup leaks rosters event (offset + 1) entryClock obsolete
      ⟨remaining, command.actor? (application setup (Vegas.runtime setup) leaks), next⟩ := by
  have appended : next.environmentRecall = control.execution.environmentRecall ++
      [⟨control.execution.observeEnvironment _, command⟩] := by
    unfold ReactiveApplication.Execution.environmentStep at reached
    obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ reached
    rfl
  have recallEq := (application setup (Vegas.runtime setup) leaks).environmentStep_recall
    control.execution next command reached
  have length : next.environmentRecall.length =
      control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have classified := rosterBlockCompleted_record setup leaks rosters
    control.execution.environmentRecall
    (control.execution.observeEnvironment (application setup (Vegas.runtime setup) leaks))
    (next.observeEnvironment (application setup (Vegas.runtime setup) leaks)) event
    command (by rw [phase.position]; omega)
  have oldTicks : offset - ((rosters event).length + 1) = 0 := by omega
  have nextTicks : offset + 1 - ((rosters event).length + 1) = 0 := by omega
  have startClock : control.execution.application.clock = entryClock := by
    rw [phase.clock, oldTicks]
    simp only [ite_self, Nat.add_zero]
  have nextClock : next.application.clock = entryClock := by
    rw [progress.clock, Nat.add_zero, startClock]
  have runningAfter (query : (graph setup).EventId) (entered : Nat)
      (activated : next.application.activatedAt query = some entered) :
      next.application.config.cut.Ready query :=
    ((progress.invariant.activated_iff query).mp (by rw [activated]; rfl)).1
  exact {
    position := by
      change next.environmentRecall.length = _
      rw [length, phase.position]
      omega
    inside := by rw [rosterBlock_length]; omega
    remaining := by
      change remaining + next.environmentRecall.length = _
      have total := phase.remaining
      rw [counted] at total
      rw [length]
      omega
    classified := by
      change rosterBlockCompleted setup leaks rosters next.environmentRecall _ event ↔ _
      rw [appended, classified]
      exact phase.classified
    prior := by
      intro query earlier
      exact progress.completed (phase.prior query earlier)
    obsolete_done := fun old => progress.completed (phase.obsolete_done old)
    live_prefix := by intro live bound; omega
    sampled := fun actorless late => sampled actorless
    clock := by
      change next.application.clock = _
      rw [nextClock, nextTicks]
      simp only [ite_self, Nat.add_zero]
    entered := by
      intro entered activated
      change next.application.activatedAt event = some entered at activated
      have ready := runningAfter event entered activated
      have upper := progress.invariant.activated_le event entered activated
      rw [nextClock] at upper
      refine ⟨upper, ?_⟩
      rcases origin event entered activated ready.1 with kept | created
      · exact (phase.entered entered kept).2
      · rw [startClock] at created
        omega
    future := by
      intro query later entered activated
      change next.application.activatedAt query = some entered at activated
      change next.application.clock ≤ entered + query.val
      have ready := runningAfter query entered activated
      rcases origin query entered activated ready.1 with kept | created
      · rw [progress.clock, Nat.add_zero]
        exact phase.future query later entered kept
      · rw [progress.clock, Nat.add_zero]
        omega
    future_started := by
      intro live query later entered activated
      change next.application.activatedAt query = some entered at activated
      have ready := runningAfter query entered activated
      rcases origin query entered activated ready.1 with kept | created
      · have oldReady := ((invariant.activated_iff query).mp (by rw [kept]; rfl)).1
        have ordered := phase.live_prefix live atEnding.le
        have same := setup.eventGraph.sequentialize_ready_unique _ oldReady
          (ordered.ready event.isLt)
        have sameRank := congrArg Fin.val same
        change query.val = event.val at sameRank
        omega
      · rw [startClock] at created
        exact created
    opportunity := by
      intro owner owned member entered ready activated
      change next.application.config.cut.Ready event at ready
      change next.application.activatedAt event = some entered at activated
      have oldReady : control.execution.application.config.cut.Ready event :=
        ⟨fun done => ready.1 (progress.completed done), fun prior dependency =>
          phase.prior prior ((graph setup).order.predecessor_lt dependency)⟩
      obtain ⟨oldEntered, oldStamp⟩ := invariant.activatedAt_eq_some_of_ready_actor event
        oldReady (by rw [owned]; rfl)
      have kept := progress.activated event oldEntered oldStamp ready.1
      have same : oldEntered = entered := Option.some.inj (kept.symm.trans activated)
      subst oldEntered
      have sameTake : (rosters event).take (offset + 1) = (rosters event).take offset := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [sameTake] at member
      obtain ⟨entry, inside, selected, started, seen⟩ :=
        phase.opportunity owner owned member entered oldReady oldStamp
      change OwnerActivatedSince (runtime setup) leaks next.environmentRecall event owner entered
      rw [appended]
      exact ⟨entry, List.mem_append_left _ inside, selected, started, seen⟩
    responses := by
      intro observer entry member query ready unfinished
      change entry ∈ next.recall observer at member
      rw [recallEq] at member
      exact phase.responses observer entry member query ready
        (fun done => unfinished (progress.completed done))
    activation := by
      intro who active
      change command.actor? (application setup (Vegas.runtime setup) leaks) = some who at active
      rw [actorNone] at active
      cases active
    inclusion := by
      intro late unfinished owner owned earlier later entry message split emitted authored
        addressed sole
      exact receipts owner owned earlier later entry message split emitted authored addressed sole }

/-- Native sampling completes the actorless target and retains the roster calendar. -/
theorem RosterCalendarPhase.sample_step
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
    {offset entryClock : Nat} {obsolete : Bool}
    {control : (application setup (Vegas.runtime setup) leaks).Control}
    (phase : RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control)
    (atEnding : offset = (rosters event).length)
    (actorless : (graph setup).actor? event = none)
    {inputs : (graph setup).Inputs}
    (invariant : control.execution.application.Invariant inputs)
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (next : (application setup (Vegas.runtime setup) leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep (application setup (Vegas.runtime
      setup) leaks) (.application (.executeSample event))).support) :
    RosterCalendarPhase setup leaks rosters event (offset + 1) entryClock obsolete
      ⟨remaining, none, next⟩ := by
  have progress : State.ServiceProgress inputs 0 control.execution.application next.application :=
    (runtime setup).reactive_environment_progress leaks inputs control.execution next
      (.application (.executeSample event)) invariant reached
  have origin := (runtime setup).reactive_environmentStep_activationOrigin leaks
    control.execution next (.application (.executeSample event)) reached
  have completed : event ∈ next.application.config.cut.completed := by
    by_cases already : event ∈ control.execution.application.config.cut.completed
    · exact progress.completed already
    · have ready : control.execution.application.config.cut.Ready event :=
        ⟨already, fun prior dependency =>
          phase.prior prior ((graph setup).order.predecessor_lt dependency)⟩
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ ((environmentStep (runtime setup) control.execution.application
        (.executeSample event)).map State.drain).support at changed
      obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
      exact (State.drainFuel_completed_subset native.config.remaining native)
        (environmentStep_sample_complete (runtime setup) control.execution.application native
          event ready actorless moved)
  apply phase.ending_step atEnding invariant (.application (.executeSample event)) rfl
    remaining counted next reached progress origin (fun _ => completed)
  intro owner owned
  rw [actorless] at owned
  cases owned

/-- Native inclusion preserves the calendar and receipts for a sole owner response. -/
theorem RosterCalendarPhase.include_step
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
    {offset entryClock : Nat} {obsolete : Bool}
    {control : (application setup (Vegas.runtime setup) leaks).Control}
    (phase : RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control)
    (atEnding : offset = (rosters event).length) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    {inputs : (graph setup).Inputs} (invariant : control.execution.application.Invariant inputs)
    (origins : control.execution.Provenance (application setup (Vegas.runtime setup) leaks))
    (recalled : control.execution.InputRecall (application setup (Vegas.runtime setup) leaks))
    (retained : control.execution.network.PendingOrPublished)
    (sound : control.execution.ReceiptsSound (application setup (Vegas.runtime setup) leaks)
      (fun _ => True))
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (next : (application setup (Vegas.runtime setup) leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep
      (application setup (Vegas.runtime setup) leaks)
      ((runtime setup).reactiveLatest leaks event owner
        (control.execution.observeEnvironment
          (application setup (Vegas.runtime setup) leaks)))).support) :
    RosterCalendarPhase setup leaks rosters event (offset + 1) entryClock obsolete
      ⟨remaining, none, next⟩ := by
  let app := application setup (Vegas.runtime setup) leaks
  let command := (runtime setup).reactiveLatest leaks event owner
    (control.execution.observeEnvironment app)
  have reachedCommand : next ∈ (control.execution.environmentStep app command).support := reached
  have commandCases : command = .wait ∨ ∃ id, command = .include id := by
    dsimp only [command]
    unfold reactiveLatest
    split
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  have actorNone : command.actor? app = none := by
    rcases commandCases with wait | ⟨id, included⟩
    · rw [wait]; rfl
    · rw [included]; rfl
  have ticks : (runtime setup).reactiveTicks leaks command = 0 := by
    rcases commandCases with wait | ⟨id, included⟩
    · rw [wait]; rfl
    · rw [included]; rfl
  have progress : State.ServiceProgress inputs 0 control.execution.application
      next.application := by
    simpa only [ticks] using (runtime setup).reactive_environment_progress leaks inputs
      control.execution next command invariant reachedCommand
  have origin := (runtime setup).reactive_environmentStep_activationOrigin leaks
    control.execution next command reachedCommand
  have sampled : (graph setup).actor? event = none →
      event ∈ next.application.config.cut.completed := by
    intro actorless
    rw [owned] at actorless
    cases actorless
  have recallEq := app.environmentStep_recall control.execution next command reachedCommand
  have receiptsPrefix := app.environmentStep_receipts_prefix control.execution next command
    reachedCommand
  have receipts : ∀ responder, (graph setup).actor? event = some responder →
      ∀ (earlier later : List app.PlayerEntry) entry message,
      next.recall responder = earlier ++ entry :: later →
      entry.emitted = some message → message.sender = responder →
      message.payload.call.event? (graph setup) = some event →
      (∀ other ∈ earlier ++ later,
        ¬ EmitsOtherFor (runtime setup) leaks other event message.id) →
      ∃ accepted, (message.id, accepted) ∈ next.receipts := by
    intro responder owns earlier later entry message split emitted authored addressed sole
    have same : responder = owner := Option.some.inj (owns.symm.trans owned)
    rw [same] at split authored
    rw [recallEq] at split
    by_cases published : message.id ∈ control.execution.network.ledger.map Message.id
    · obtain ⟨accepted, member⟩ := receipt_of_published control.execution sound _ published
      exact ⟨accepted, receiptsPrefix.subset member⟩
    · obtain ⟨pending, latest⟩ := reactiveLatest_sole (runtime setup) leaks control.execution
        origins recalled retained event owner earlier later entry message split emitted
        authored addressed sole published
      have included : command = .include message.id := latest
      have includedReached := reachedCommand
      rw [included] at includedReached
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        at includedReached
      cases (PMF.mem_support_pure_iff _ _).mp includedReached
      exact includePending_receipt_of_pending (runtime setup) leaks control.execution message
        pending
  change command.actor? (application setup (Vegas.runtime setup) leaks) = none at actorNone
  simpa only [actorNone] using phase.ending_step atEnding invariant command actorNone
    remaining counted next reachedCommand progress origin sampled receipts

/-- A completed expiry target enters the next calendar block or exhausts the plan. -/
theorem RosterCalendarPhase.expire_boundary
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
    {offset entryClock : Nat} {obsolete : Bool}
    {control : (application setup (Vegas.runtime setup) leaks).Control}
    (phase : RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control)
    (atExpiry : offset = (rosters event).length + event.val + 2)
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (next : (application setup (Vegas.runtime setup) leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep
      (application setup (Vegas.runtime setup) leaks) (.application (.expire event))).support)
    {inputs : (graph setup).Inputs}
    (progress : State.ServiceProgress inputs 0 control.execution.application next.application)
    (origin : State.ActivationOrigin control.execution.application next.application)
    (stable : EntryEventStable (runtime setup) leaks control.execution)
    (done : event ∈ next.application.config.cut.completed) :
    RosterCalendarInvariant setup leaks rosters (some ⟨remaining, none, next⟩) := by
  have appended := (application setup (Vegas.runtime setup) leaks).environmentStep_environmentRecall
    control.execution next _ reached
  have recallEq := (application setup (Vegas.runtime setup) leaks).environmentStep_recall
    control.execution next _ reached
  have length : next.environmentRecall.length = control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have clockEq : next.application.clock = control.execution.application.clock := by
    simpa only [Nat.add_zero] using progress.clock
  have position : next.environmentRecall.length =
      (rosterPlanPrefix setup rosters (event.val + 1)).length := by
    rw [length, phase.position, rosterPlanPrefix_succ, List.length_append,
      List.length_map, rosterBlock_length]
    omega
  have total : remaining + next.environmentRecall.length = (rosterPlan setup rosters).length := by
    have before := phase.remaining
    rw [counted] at before
    omega
  have prior : ∀ query : (graph setup).EventId, query.val < event.val + 1 →
      query ∈ next.application.config.cut.completed := by
    intro query earlier
    by_cases strict : query.val < event.val
    · exact progress.completed (phase.prior query strict)
    · have same : query = event := Fin.ext (by omega)
      simpa only [same] using done
  by_cases more : event.val + 1 < (graph setup).order.eventCount
  · let following : (graph setup).EventId := ⟨event.val + 1, more⟩
    let stale : Bool := decide (following ∈ next.application.config.cut.completed)
    have livePrefix : following ∉ next.application.config.cut.completed →
        next.application.config.cut.IsPrefix following.val := by
      intro unfinished
      have ready : next.application.config.cut.Ready following :=
        ⟨unfinished, fun query member => prior query
          ((graph setup).order.predecessor_lt member)⟩
      exact ⟨following.isLt.le, fun query =>
        setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
    have starting : next.environmentRecall.length =
        (rosterPlanPrefix setup rosters following.val).length := position
    have bound : ∀ query : (graph setup).EventId, event.val < query.val → ∀ entered,
        next.application.activatedAt query = some entered →
        next.application.clock ≤ entered + query.val := by
      intro query later entered activated
      have ready := (progress.invariant.activated_iff query).mp
        (by simp only [activated, Option.isSome_some]) |>.1
      rcases origin query entered activated ready.1 with retained | fresh
      · rw [clockEq]
        exact phase.future query later entered retained
      · rw [clockEq]
        omega
    left
    refine ⟨following, 0, next.application.clock, stale, ?_⟩
    exact {
      position := by simpa only [Nat.add_zero] using starting
      inside := by rw [rosterBlock_length]; omega
      remaining := total
      classified := by
        rw [rosterBlockCompleted_at_start setup leaks rosters next.environmentRecall
          (next.observeEnvironment (application setup (Vegas.runtime setup) leaks))
          following starting]
        change following ∈ next.application.publicView.observation.completionOrder ↔
          decide (following ∈ next.application.config.cut.completed) = true
        rw [decide_eq_true_eq]
        exact next.application.config.history_exact following
      prior := fun query earlier => prior query earlier
      obsolete_done := fun old => of_decide_eq_true old
      live_prefix := fun live _ => livePrefix (of_decide_eq_false live)
      sampled := fun _ late => absurd late (Nat.not_lt_zero _)
      clock := by simp
      entered := by
        intro entered activated
        exact ⟨progress.invariant.activated_le following entered activated,
          bound following (by change event.val < event.val + 1; omega) entered activated⟩
      future := by
        intro query later entered activated
        exact bound query (by change event.val + 1 < query.val at later; omega) entered activated
      future_started := by
        intro live query later entered activated
        have readyNext : next.application.config.cut.Ready following :=
          (livePrefix (of_decide_eq_false live)).ready following.isLt
        have queryReady : next.application.config.cut.Ready query :=
          ((progress.invariant.activated_iff query).mp (by rw [activated]; rfl)).1
        have same := setup.eventGraph.sequentialize_ready_unique _ queryReady readyNext
        have rank : query.val = following.val := congrArg Fin.val same
        omega
      opportunity := by
        intro owner owned member
        simp at member
      responses := by
        intro who entry member query ready unfinished
        change entry ∈ next.recall who at member
        rw [recallEq] at member
        have unfinishedBefore : query ∉ control.execution.application.config.cut.completed :=
          fun completed => unfinished (progress.completed completed)
        obtain ⟨sent, sameOrObsolete⟩ :=
          phase.responses who entry member query ready unfinishedBefore
        have old : obsolete = true := by
          rcases sameOrObsolete with same | old
          · subst query
            exact (unfinished done).elim
          · exact old
        have now : next.application.clock = entryClock := by
          rw [clockEq, phase.clock]
          simp [old]
        refine ⟨sent.trans now.symm, ?_⟩
        by_cases same : query = following
        · exact Or.inl same
        · right
          apply decide_eq_true
          by_contra unfinishedNext
          have readyNext : next.application.config.cut.Ready following :=
            (livePrefix unfinishedNext).ready following.isLt
          obtain ⟨extra, history, _⟩ := stable who entry member query ready unfinishedBefore
          have readyBefore := ready_of_eventReady_extends history ready unfinishedBefore
          have readyAfter := (progress.ready_or_completed query readyBefore).resolve_left unfinished
          exact same (setup.eventGraph.sequentialize_ready_unique _ readyAfter readyNext)
      activation := by intro who active; cases active
      inclusion := fun late => absurd late (Nat.not_lt_zero _) }
  · right
    have last : event.val + 1 = (graph setup).order.eventCount := by
      have inside := event.isLt
      omega
    refine ⟨?_, rfl, ?_⟩
    · change remaining = 0
      have whole : rosterPlanPrefix setup rosters (event.val + 1) = rosterPlan setup rosters := by
        rw [last]
        exact rosterPlanPrefix_eventCount setup rosters
      rw [position, whole] at total
      omega
    · unfold EventOrder.Cut.Terminal
      apply Finset.eq_univ_of_forall
      intro query
      apply prior query
      have inside := query.isLt
      omega

/-- The actual expiry command completes its block target and crosses the
calendar boundary under the unchanged rank deadline. -/
theorem RosterCalendarPhase.expire_step
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
    {offset entryClock : Nat} {obsolete : Bool}
    {control : (application setup (Vegas.runtime setup) leaks).Control}
    (phase : RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control)
    (atExpiry : offset = (rosters event).length + event.val + 2)
    {inputs : (graph setup).Inputs} (invariant : control.execution.application.Invariant inputs)
    (stable : EntryEventStable (runtime setup) leaks control.execution)
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (next : (application setup (Vegas.runtime setup) leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep
      (application setup (Vegas.runtime setup) leaks) (.application (.expire event))).support) :
    RosterCalendarInvariant setup leaks rosters (some ⟨remaining, none, next⟩) := by
  have progress : State.ServiceProgress inputs 0 control.execution.application next.application :=
    (runtime setup).reactive_environment_progress leaks inputs control.execution next
      (.application (.expire event)) invariant reached
  have origin := (runtime setup).reactive_environmentStep_activationOrigin leaks
    control.execution next (.application (.expire event)) reached
  have done : event ∈ next.application.config.cut.completed := by
    by_cases finished : event ∈ control.execution.application.config.cut.completed
    · exact progress.completed finished
    have live : obsolete = false := by
      cases obsolete with
      | false => rfl
      | true => exact (finished (phase.obsolete_done rfl)).elim
    have ready : control.execution.application.config.cut.Ready event :=
      ⟨finished, fun query member => phase.prior query
        ((graph setup).order.predecessor_lt member)⟩
    cases owned : (graph setup).actor? event with
    | none => exact (finished (phase.sampled owned (by omega))).elim
    | some owner =>
        have strategic : ((graph setup).actor? event).isSome = true := by rw [owned]; rfl
        obtain ⟨entered, activated⟩ :=
          invariant.activatedAt_eq_some_of_ready_actor event ready strategic
        have bounds := phase.entered entered activated
        have endClock : control.execution.application.clock = entryClock + (event.val + 1) := by
          rw [phase.clock]
          simp only [live, Bool.false_eq_true, ↓reduceIte]
          omega
        have due : (runtime setup).deadline event ≤
            control.execution.application.clock - entered := by
          change event.val + 1 ≤ _
          omega
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
        change state ∈ ((environmentStep (runtime setup) control.execution.application
          (.expire event)).map State.drain).support at changed
        obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
        have completed := environmentStep_expire_complete (runtime setup)
          control.execution.application native event ready strategic entered activated due moved
        exact State.drainFuel_completed_subset native.config.remaining native completed
  exact phase.expire_boundary atExpiry remaining counted next reached progress origin stable done

/-- Live blocks advance the clock; blocks completed at entry preserve it. -/
theorem RosterCalendarPhase.tick_step
    {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
  {offset entryClock : Nat} {obsolete : Bool}
  {control : (application setup (Vegas.runtime setup) leaks).Control}
    (phase : RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control)
    (late : (rosters event).length < offset)
    (ticking : offset < (rosters event).length + event.val + 2)
    (quiescent : ∀ query, ¬ control.execution.application.AutomaticReady query)
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (next : (application setup (Vegas.runtime setup) leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep
      (application setup (Vegas.runtime setup) leaks)
      (if obsolete then .wait else .application .advanceClock)).support) :
    RosterCalendarPhase setup leaks rosters event (offset + 1) entryClock obsolete
      ⟨remaining, none, next⟩ := by
  let app := application setup (Vegas.runtime setup) leaks
  let command : app.Command := if obsolete then .wait else .application .advanceClock
  have native : next.application = { control.execution.application with
      clock := control.execution.application.clock + (if obsolete then 0 else 1) } := by
    cases obsolete with
    | true =>
        change next ∈ (control.execution.environmentStep app .wait).support at reached
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        simp only [↓reduceIte, Nat.add_zero]
        cases control.execution.application
        rfl
    | false =>
        change next ∈ (control.execution.environmentStep app (.application .advanceClock)).support
          at reached
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨state, moved, rfl⟩ := PMF.support_map .. ▸ supported
        rw [reactiveApplication_tick_eq_pure (runtime setup) leaks _ quiescent] at moved
        cases (PMF.mem_support_pure_iff _ _).mp moved
        rfl
  have cfg : next.application.config = control.execution.application.config := by rw [native]
  have activated : next.application.activatedAt = control.execution.application.activatedAt := by
    rw [native]
  have clock : next.application.clock = control.execution.application.clock +
      (if obsolete then 0 else 1) := by rw [native]
  have recalled := app.environmentStep_recall control.execution next command reached
  have receipts := app.environmentStep_receipts_prefix control.execution next command reached
  have history : next.environmentRecall = control.execution.environmentRecall ++
      [⟨control.execution.observeEnvironment app, command⟩] := by
    unfold ReactiveApplication.Execution.environmentStep at reached
    obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ reached
    rfl
  refine {
    position := by
      simp only [history, List.length_append, List.length_singleton]
      have h := phase.position
      omega
    inside := by rw [rosterBlock_length]; omega
    remaining := by
      simp only [history, List.length_append, List.length_singleton]
      have h := phase.remaining
      omega
    classified := by
      change rosterBlockCompleted setup leaks rosters next.environmentRecall
        (next.observeEnvironment app) event ↔ _
      rw [history]
      exact (rosterBlockCompleted_record setup leaks rosters control.execution.environmentRecall
        (control.execution.observeEnvironment app) (next.observeEnvironment app) event command
        (by rw [phase.position]; omega)).trans phase.classified
    prior := by intro query smaller; rw [cfg]; exact phase.prior query smaller
    obsolete_done := by intro old; rw [cfg]; exact phase.obsolete_done old
    live_prefix := by intro _ early; omega
    sampled := by intro actor _; rw [cfg]; exact phase.sampled actor late
    clock := by
      change next.application.clock = _
      rw [clock, phase.clock]
      cases obsolete with
      | true => simp
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          omega
    entered := by
      change ∀ entered, next.application.activatedAt event = _ → _
      rw [activated]
      exact phase.entered
    future := by
      intro query later entered stamp
      change next.application.clock ≤ _
      rw [activated] at stamp
      cases old : obsolete with
      | true => simpa only [clock, old, Bool.true_eq, ↓reduceIte, Nat.add_zero]
          using phase.future query later entered stamp
      | false =>
          have born := phase.future_started old query later entered stamp
          have now := phase.clock
          simp only [old, Bool.false_eq_true, ↓reduceIte] at now
          rw [clock]
          simp only [old, Bool.false_eq_true, ↓reduceIte]
          omega
    future_started := by
      intro live query later entered stamp
      rw [activated] at stamp
      exact phase.future_started live query later entered stamp
    opportunity := by
      intro owner actor member entered ready stamp
      rw [List.take_of_length_le (by omega)] at member
      have memberOld : owner ∈ (rosters event).take offset := by
        rwa [List.take_of_length_le (by omega)]
      rw [cfg] at ready
      rw [activated] at stamp
      obtain ⟨entry, inside, rest⟩ := phase.opportunity owner actor memberOld entered ready stamp
      exact ⟨entry, by rw [history]; exact List.mem_append_left _ inside, rest⟩
    responses := by
      intro who entry member query ready unfinished
      rw [recalled] at member
      rw [cfg] at unfinished
      exact phase.responses who entry member query ready unfinished
    activation := by intro who active; cases active
    inclusion := by
      intro _ unfinished owner actor earlier later entry message split emitted authored
        addressed sole
      rw [cfg] at unfinished
      rw [recalled] at split
      obtain ⟨accepted, member⟩ := phase.inclusion late unfinished owner actor earlier later
        entry message split emitted authored addressed sole
      exact ⟨accepted, receipts.subset member⟩ }

end Vegas
