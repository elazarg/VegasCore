/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingCompletion
import Vegas.Pending.PhaseRequestOrigin

/-! # Owner opportunities on every actual raw service history -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private abbrev originalInput : graph.Inputs :=
  encodeInputs (Env.empty (CellVal simpleExpr))

private def serviceIndex (execution : app.Execution) : Nat :=
  if execution.application.attempt = originalAttempt then execution.environmentRecall.length
  else tailIndex execution.environmentRecall (execution.observeEnvironment app)

private def firstTurn (coordinate : CommitAttemptEvent graph) : Nat :=
  if coordinate.attempt = originalAttempt then
    if coordinate.event = aliceBinding then 0 else 1
  else if coordinate.event.val < 2 then 0
  else if coordinate.event = aliceReveal then 0 else 2

private theorem firstTurn_le_two (coordinate : CommitAttemptEvent graph) :
    firstTurn coordinate ≤ 2 := by
  unfold firstTurn
  split_ifs <;> omega

private theorem request_block (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (request : current.execution.application.SeedRequest owner coordinate) :
    ∃ phase, current.execution.application.phases.head? = some phase ∧
      (phase = commitmentPhase ∨ phase = publicationPhase) ∧ coordinate.event ∈ phase.events := by
  obtain ⟨phase, installed, inside⟩ := request.2.1
  have head := Option.mem_def.mp installed
  refine ⟨phase, head, ?_, inside⟩
  rcases raw_phases_cases (family seeds) current trace with all | reveal | empty
  · rw [all] at head
    exact Or.inl (Option.some.inj head).symm
  · rw [reveal] at head
    exact Or.inr (Option.some.inj head).symm
  · rw [empty] at head
    cases head

private theorem ready_of_request (execution : app.Execution) (owner : Player)
    (event : graph.EventId) (valid : execution.application.Invariant originalInput)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, event⟩) :
    ready owner event (execution.observeEnvironment app) = true := by
  classical
  unfold ready
  rw [decide_eq_true_eq]
  exact (execution.application.requests_publicView valid owner _).mpr request

private theorem survivor_of_request (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (retired : current.execution.application.attempt ≠ originalAttempt)
    (installed : current.execution.application.phases.head? = some commitmentPhase)
    (owner : Player) (survives : owner ∉ current.execution.application.current.excluded) :
    survivor (current.execution.observeEnvironment app) = owner := by
  classical
  have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon
    (family seeds) (by
      intro state supported
      rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
      subst state
      exact PhaseRuntimeState.initial_seedBudget plan originalInput) trace
  have positive : 0 < current.execution.application.generation := by
    by_contra absent
    have zero : current.execution.application.generation = 0 := by omega
    apply retired
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some, zero]
    rfl
  obtain ⟨failed, member⟩ := Finset.card_pos.mp
    (lt_of_lt_of_le positive budget.current_generation)
  change (if alice ∈ current.execution.application.current.excluded then bob else alice) = owner
  fin_cases owner <;> fin_cases failed <;> simp_all [alice, bob]

private theorem callback_at_firstTurn (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (request : current.execution.application.SeedRequest owner coordinate)
    (position : serviceIndex current.execution = firstTurn coordinate) :
    choose seeds current.execution.environmentRecall
      (current.execution.observeEnvironment app) = .activate owner := by
  classical
  rcases coordinate with ⟨attempt, event⟩
  obtain ⟨phase, installed, block, inside⟩ := request_block seeds current trace
    ⟨attempt, event⟩ owner request
  have valid := raw_native_valid (family seeds) current trace
  have currentAttempt : attempt = current.execution.application.attempt := request.1
  have chosenReady : ready owner event
      (current.execution.observeEnvironment app) = true := by
    apply ready_of_request _ _ _ valid
    simpa only [currentAttempt] using request
  have interval := (RuntimePhase.mem_events phase event).mp inside
  have actor := request.2.2.2.1
  by_cases original : current.execution.application.attempt = originalAttempt
  · have phases := original_phases (family seeds) current trace original
    rw [phases] at installed
    have phaseEq : phase = commitmentPhase := (Option.some.inj installed).symm
    subst phase
    change 0 ≤ event.val ∧ event.val < 2 at interval
    rw [serviceIndex, ite_eq_left original, firstTurn,
      ite_eq_left (currentAttempt.trans original)] at position
    rw [choose_original seeds _ _ original]
    change Fin 4 at event
    fin_cases event
    · have ownerEq : owner = alice := Option.some.inj (actor.symm.trans binding_actors.1)
      subst owner
      have index : current.execution.environmentRecall.length = 0 := by
        simpa [aliceBinding] using position
      rw [index]
      exact congrArg (fun selected => if selected then (.activate alice : app.Command) else .wait)
        chosenReady
    · have ownerEq : owner = bob := Option.some.inj (actor.symm.trans binding_actors.2)
      subst owner
      have index : current.execution.environmentRecall.length = 1 := by
        simpa [aliceBinding] using position
      rw [index]
      exact congrArg (fun selected => if selected then (.activate bob : app.Command) else .wait)
        chosenReady
    · change 0 ≤ 2 ∧ 2 < 2 at interval
      omega
    · change 0 ≤ 3 ∧ 3 < 2 at interval
      omega
  · have notOriginal : attempt ≠ originalAttempt := by
      rwa [currentAttempt]
    rw [serviceIndex, ite_eq_right original, firstTurn, ite_eq_right notOriginal] at position
    change tailIndex current.execution.environmentRecall
        (current.execution.observeEnvironment app) =
      (if event.val < 2 then 0 else if event = aliceReveal then 0 else 2) at position
    have phaseView : (current.execution.observeEnvironment app).application.phase =
        some (phase.kind, phase.low, phase.high) := by
      change current.execution.application.phases.head?.map
        (fun installed => (installed.kind, installed.low, installed.high)) = _
      rw [installed]
      rfl
    have retiredView : (current.execution.observeEnvironment app).application.attempt ≠
        originalAttempt := original
    rw [choose, ite_eq_right retiredView, phaseView]
    rcases block with rfl | rfl
    · change retryCommand (tailIndex current.execution.environmentRecall
          (current.execution.observeEnvironment app)) current.execution.environmentRecall
          (current.execution.observeEnvironment app) = .activate owner
      change 0 ≤ event.val ∧ event.val < 2 at interval
      have index : tailIndex current.execution.environmentRecall
          (current.execution.observeEnvironment app) = 0 := by
        rw [ite_eq_left interval.2] at position
        exact position
      have ownerEq := survivor_of_request seeds current trace original installed owner
        request.2.2.2.2
      have eventEq : event = bindingEvent owner := by
        change Fin 4 at event
        fin_cases event
        · have same : owner = alice := Option.some.inj (actor.symm.trans binding_actors.1)
          rw [same]
          simp only [bindingEvent]
          rfl
        · have same : owner = bob := Option.some.inj (actor.symm.trans binding_actors.2)
          rw [same]
          simp only [bindingEvent, ite_eq_right (by decide : bob ≠ alice)]
          rfl
        · change 0 ≤ 2 ∧ 2 < 2 at interval
          omega
        · change 0 ≤ 3 ∧ 3 < 2 at interval
          omega
      rw [index]
      change activateReady (survivor (current.execution.observeEnvironment app))
        (bindingEvent (survivor (current.execution.observeEnvironment app)))
        (current.execution.observeEnvironment app) = .activate owner
      rw [ownerEq, ← eventEq]
      unfold activateReady
      rw [chosenReady]
      rfl
    · change revealCommand (tailIndex current.execution.environmentRecall
          (current.execution.observeEnvironment app)) current.execution.environmentRecall
          (current.execution.observeEnvironment app) = .activate owner
      change 2 ≤ event.val ∧ event.val < 4 at interval
      rw [ite_eq_right (by omega)] at position
      change Fin 4 at event
      fin_cases event
      · change 2 ≤ 0 ∧ 0 < 4 at interval
        omega
      · change 2 ≤ 1 ∧ 1 < 4 at interval
        omega
      · have same : owner = alice := Option.some.inj (actor.symm.trans reveal_actors.1)
        subst owner
        have index : tailIndex current.execution.environmentRecall
            (current.execution.observeEnvironment app) = 0 := by
          change tailIndex current.execution.environmentRecall
              (current.execution.observeEnvironment app) =
            (if aliceReveal = aliceReveal then 0 else 2) at position
          rw [ite_eq_left rfl] at position
          exact position
        rw [index]
        change activateReady alice aliceReveal (current.execution.observeEnvironment app) =
          .activate alice
        change ready alice aliceReveal (current.execution.observeEnvironment app) = true
          at chosenReady
        unfold activateReady
        rw [chosenReady]
        rfl
      · have same : owner = bob := Option.some.inj (actor.symm.trans reveal_actors.2)
        subst owner
        have index : tailIndex current.execution.environmentRecall
            (current.execution.observeEnvironment app) = 2 := by
          change tailIndex current.execution.environmentRecall
              (current.execution.observeEnvironment app) =
            (if bobReveal = aliceReveal then 0 else 2) at position
          rw [ite_eq_right (by decide : bobReveal ≠ aliceReveal)] at position
          exact position
        rw [index]
        change activateReady bob bobReveal (current.execution.observeEnvironment app) =
          .activate bob
        change ready bob bobReveal (current.execution.observeEnvironment app) = true
          at chosenReady
        unfold activateReady
        rw [chosenReady]
        rfl

private theorem responseCommand_ticks (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks (responseCommand owner past view) = 0 := by
  cases last : past.getLast? with
  | none => simp only [responseCommand, last, PhaseSeedCalendar.commandTicks]
  | some entry =>
      simp only [responseCommand, last]
      split
      · unfold pendingCommand
        split <;> rfl
      · rfl

private theorem ticks_before_callback (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (request : current.execution.application.SeedRequest owner coordinate)
    (early : serviceIndex current.execution ≤ firstTurn coordinate) :
    PhaseSeedCalendar.commandTicks runtime leaks
      (choose seeds current.execution.environmentRecall
        (current.execution.observeEnvironment app)) = 0 := by
  have bounded := firstTurn_le_two coordinate
  by_cases original : current.execution.application.attempt = originalAttempt
  · rw [choose_original seeds _ _ original, originalCommand_ticks]
    have turnBound : firstTurn coordinate ≤ 1 := by
      unfold firstTurn
      rw [ite_eq_left (request.1.trans original)]
      split <;> omega
    have index : current.execution.environmentRecall.length ≤ 1 := by
      simpa only [serviceIndex, ite_eq_left original] using early.trans turnBound
    unfold originalTick
    rw [ite_eq_right]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · obtain ⟨phase, installed, block, inside⟩ := request_block seeds current trace coordinate owner
      request
    have phaseView : (current.execution.observeEnvironment app).application.phase =
        some (phase.kind, phase.low, phase.high) := by
      change current.execution.application.phases.head?.map
        (fun installed => (installed.kind, installed.low, installed.high)) = _
      rw [installed]
      rfl
    have small : tailIndex current.execution.environmentRecall
        (current.execution.observeEnvironment app) ≤ 2 := by
      simpa only [serviceIndex, ite_eq_right original] using early.trans bounded
    have retiredView : (current.execution.observeEnvironment app).application.attempt ≠
        originalAttempt := original
    rw [choose, ite_eq_right retiredView, phaseView]
    rcases block with rfl | rfl
    · change PhaseSeedCalendar.commandTicks runtime leaks
        (retryCommand (tailIndex current.execution.environmentRecall
          (current.execution.observeEnvironment app)) current.execution.environmentRecall
          (current.execution.observeEnvironment app)) = 0
      have interval := (RuntimePhase.mem_events commitmentPhase coordinate.event).mp inside
      change 0 ≤ coordinate.event.val ∧ coordinate.event.val < 2 at interval
      have zero : firstTurn coordinate = 0 := by
        rw [firstTurn, ite_eq_right (by rwa [request.1]), ite_eq_left interval.2]
      have index : tailIndex current.execution.environmentRecall
          (current.execution.observeEnvironment app) = 0 := by
        simpa only [serviceIndex, ite_eq_right original, zero, Nat.le_zero] using early
      rw [index]
      change PhaseSeedCalendar.commandTicks runtime leaks
        (activateReady (survivor (current.execution.observeEnvironment app))
          (bindingEvent (survivor (current.execution.observeEnvironment app)))
          (current.execution.observeEnvironment app)) = 0
      unfold activateReady
      split <;> rfl
    · change PhaseSeedCalendar.commandTicks runtime leaks
        (revealCommand (tailIndex current.execution.environmentRecall
          (current.execution.observeEnvironment app)) current.execution.environmentRecall
          (current.execution.observeEnvironment app)) = 0
      generalize tailIndex current.execution.environmentRecall
        (current.execution.observeEnvironment app) = position at small ⊢
      interval_cases position
      · change PhaseSeedCalendar.commandTicks runtime leaks
          (activateReady alice aliceReveal (current.execution.observeEnvironment app)) = 0
        unfold activateReady
        split <;> rfl
      · exact responseCommand_ticks _ _ _
      · change PhaseSeedCalendar.commandTicks runtime leaks
          (activateReady bob bobReveal (current.execution.observeEnvironment app)) = 0
        unfold activateReady
        split <;> rfl

private theorem request_before (seeds : Seeds) (before after : app.Control)
    (beforeTrace : (app.protocol initial horizon (family seeds)).Trace (some before))
    (afterTrace : (app.protocol initial horizon (family seeds)).Trace (some after))
    (same : before.execution.application.attempt = after.execution.application.attempt)
    (ticks : Nat)
    (progress : EventGraphRuntime.State.ServiceProgress originalInput ticks
      before.execution.application.current.native after.execution.application.current.native)
    (coordinate : CommitAttemptEvent graph) (owner : Player) (entered : Nat)
    (request : after.execution.application.SeedRequest owner coordinate)
    (stamp : after.execution.application.current.native.activatedAt coordinate.event =
      some entered) :
    before.execution.application.SeedRequest owner coordinate ∧
      before.execution.application.current.native.activatedAt coordinate.event = some entered := by
  obtain ⟨phase, installed, block, inside⟩ := request_block seeds after afterTrace coordinate owner
    request
  have phases := raw_same_attempt_phases (family seeds) before after beforeTrace afterTrace same
  have installedBefore : before.execution.application.phases.head? = some phase := by
    rw [phases]
    exact installed
  have unfinished : coordinate.event ∉
      before.execution.application.current.native.config.cut.completed :=
    fun done => request.2.2.1.1 (progress.completed done)
  have asked := raw_phase_event_request (family seeds) before beforeTrace phase installedBefore
    block coordinate.event inside owner request.2.2.2.1 unfinished
  have coordinateEq : (⟨before.execution.application.attempt, coordinate.event⟩ :
      CommitAttemptEvent graph) = coordinate := by
    exact congrArg (fun attempt =>
      (⟨attempt, coordinate.event⟩ : CommitAttemptEvent graph)) (same.trans request.1.symm)
  rw [coordinateEq] at asked
  have valid := raw_native_valid (family seeds) before beforeTrace
  obtain ⟨oldEntered, oldStamp⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff coordinate.event).mpr
      ⟨asked.2.2.1, by rw [asked.2.2.2.1]; rfl⟩)
  have retained := progress.activated coordinate.event oldEntered oldStamp request.2.2.1.1
  have enteredEq := Option.some.inj (retained.symm.trans stamp)
  exact ⟨asked, enteredEq ▸ oldStamp⟩

private def PendingOpportunity (execution : app.Execution) : Prop :=
  ∀ coordinate owner entered, execution.application.SeedRequest owner coordinate →
    execution.application.current.native.activatedAt coordinate.event = some entered →
    PhaseService.OwnerActivatedSince runtime leaks execution.environmentRecall coordinate owner
      entered ∨ (serviceIndex execution ≤ firstTurn coordinate ∧
        execution.application.current.native.clock ≤ entered)

private theorem carry_activation (before after : app.Execution)
    (isPrefix : before.environmentRecall <+: after.environmentRecall)
    (coordinate : CommitAttemptEvent graph) (owner : Player) (entered : Nat)
    (recorded : PhaseService.OwnerActivatedSince runtime leaks before.environmentRecall
      coordinate owner entered) :
    PhaseService.OwnerActivatedSince runtime leaks after.environmentRecall coordinate owner
      entered := by
  obtain ⟨entry, member, facts⟩ := recorded
  exact ⟨entry, isPrefix.subset member, facts⟩

private theorem append_activation (before after : app.Execution) (owner : Player)
    (coordinate : CommitAttemptEvent graph) (entered : Nat)
    (request : before.application.SeedRequest owner coordinate)
    (stamp : before.application.current.native.activatedAt coordinate.event = some entered)
    (moved : after ∈ (before.environmentStep app (.activate owner)).support) :
    PhaseService.OwnerActivatedSince runtime leaks after.environmentRecall coordinate owner
      entered := by
  have entries := app.environmentStep_environmentRecall before after (.activate owner) moved
  rw [entries]
  refine ⟨⟨before.observeEnvironment app, .activate owner⟩,
    List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl, request.1.symm, ?_, stamp⟩
  exact (State.publicView_eventReady _ _).mpr request.2.2.1

/-- Every still-unserved raw readiness episode has zero physical age. The
recorded callback alternative retains its original full attempt and stamp. -/
theorem raw_pending_opportunity (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => PendingOpportunity current.execution) := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      have targetTrace := prior.extend joint legal reached
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
          rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
          subst state
          intro coordinate owner entered _request _stamp
          right
          refine ⟨?_, ?_⟩
          · change serviceIndex initialExecution ≤ firstTurn coordinate
            have zero : serviceIndex initialExecution = 0 := by
              unfold serviceIndex
              change (if initialState.attempt = originalAttempt then 0 else _) = 0
              rw [ite_eq_left initialState_attempt]
            rw [zero]
            omega
          · change initialState.current.native.clock ≤ entered
            rw [initialState_clock]
            omega
      | some before =>
          rcases before with ⟨remaining, active, execution⟩
          have valid := raw_native_valid (family seeds) ⟨remaining, active, execution⟩ prior
          have geometry := raw_phase_geometry (family seeds) ⟨remaining, active, execution⟩ prior
          have ordered : execution.application.Ordered := geometry.1.adjacent
          cases active with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              let action := (joint who).getD (⟨none⟩ : app.Action)
              let after := execution.respond app who action
              have same : execution.application.attempt = after.application.attempt := by
                rcases action with ⟨submission⟩
                cases submission <;> rfl
              obtain ⟨ticks, progress⟩ := (phaseApplication_serviceProgress runtime leaks).respond
                execution who action originalInput valid ordered same
              intro coordinate owner entered request stamp
              have earlier := request_before seeds ⟨remaining, some who, execution⟩ _ prior
                targetTrace same ticks progress coordinate owner entered request stamp
              rcases ih coordinate owner entered earlier.1 earlier.2 with recorded | unserved
              · left
                apply carry_activation execution after _ coordinate owner entered recorded
                rw [app.respond_environmentRecall]
              · right
                have index : serviceIndex after = serviceIndex execution := by
                  unfold serviceIndex
                  rw [app.respond_environmentRecall, ← same]
                  split
                  · rfl
                  · exact tailIndex_congr_attempt _ _ _ same.symm
                have clockBefore := raw_clock_history (family seeds)
                  ⟨remaining, some who, execution⟩ prior
                have clockAfter := raw_clock_history (family seeds)
                  ⟨remaining, none, after⟩ targetTrace
                rw [app.respond_environmentRecall] at clockAfter
                exact ⟨index.trans_le unserved.1, clockAfter.trans_le
                  (clockBefore.symm.le.trans unserved.2)⟩
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have selectedEq : command = choose seeds execution.environmentRecall
                      (execution.observeEnvironment app) :=
                    (PMF.mem_support_pure_iff _ _).mp selected
                  have entries := app.environmentStep_environmentRecall execution next command
                    supported
                  have isPrefix : execution.environmentRecall <+: next.environmentRecall := by
                    rw [entries]
                    exact List.prefix_append _ _
                  have physicalClock := PhaseSeedCalendar.environmentStep_clock runtime leaks
                    execution next command valid supported
                  intro coordinate owner entered request stamp
                  change PhaseService.OwnerActivatedSince runtime leaks next.environmentRecall
                      coordinate owner entered ∨
                    (serviceIndex next ≤ firstTurn coordinate ∧
                      next.application.current.native.clock ≤ entered)
                  by_cases same : execution.application.attempt = next.application.attempt
                  · obtain ⟨ticks, progress⟩ :=
                      (phaseApplication_serviceProgress runtime leaks).environmentStep
                        execution next command supported originalInput valid ordered same
                    have earlier := request_before seeds ⟨remaining + 1, none, execution⟩ _ prior
                      targetTrace same ticks progress coordinate owner entered request stamp
                    rcases ih coordinate owner entered earlier.1 earlier.2 with recorded | unserved
                    · exact Or.inl (carry_activation execution next isPrefix coordinate owner
                        entered recorded)
                    · change serviceIndex execution ≤ firstTurn coordinate ∧
                        execution.application.current.native.clock ≤ entered at unserved
                      have index : serviceIndex next = serviceIndex execution + 1 := by
                        unfold serviceIndex
                        rw [← same]
                        split
                        · rw [entries, List.length_append, List.length_singleton]
                        · exact tailIndex_after_same_attempt execution next command supported
                            same.symm
                      by_cases atTurn : serviceIndex execution = firstTurn coordinate
                      · left
                        have callback := callback_at_firstTurn seeds
                          ⟨remaining + 1, none, execution⟩ prior coordinate owner earlier.1 atTurn
                        have chosen : command = .activate owner := selectedEq.trans callback
                        exact append_activation execution next owner coordinate entered earlier.1
                          earlier.2 (chosen ▸ supported)
                      · right
                        have zero := ticks_before_callback seeds
                          ⟨remaining + 1, none, execution⟩ prior coordinate owner
                            earlier.1 unserved.1
                        rw [← selectedEq] at zero
                        rw [zero, Nat.add_zero] at physicalClock
                        exact ⟨by rw [index]; omega, physicalClock.trans_le unserved.2⟩
                  · right
                    have newIndex := tailIndex_after_retirement seeds
                      ⟨remaining + 1, none, execution⟩ prior next command supported same
                    have notOriginal : next.application.attempt ≠ originalAttempt := by
                      intro original
                      have namespaces := phaseApplication_namespace_progress runtime leaks
                      have bounds := namespaces.environmentStep execution next command
                        supported ordered
                      apply same
                      rw [original]
                      rw [original] at bounds
                      generalize idEq : execution.application.attempt = identifier at bounds ⊢
                      rcases identifier with ⟨phase, generation⟩
                      change generation ≤ 0 ∧ phase ≤ 0 at bounds
                      have phaseEq : phase = 0 := by omega
                      have generationEq : generation = 0 := by omega
                      subst phase
                      subst generation
                      rfl
                    refine ⟨?_, ?_⟩
                    · simp only [serviceIndex, ite_eq_right notOriginal, newIndex]
                      omega
                    · by_cases advancing : command = .application .advanceClock
                      · have origin := PhaseSeedScheduler.advanceClock_request_origin runtime leaks
                          execution next
                          (serviceGraph_revealRelaxedOrdered setup .concurrentReveals) valid
                          geometry.1 geometry.2.1 geometry.2.2.1 geometry.2.2.2
                          (advancing ▸ supported) owner coordinate entered request stamp
                        rcases origin with old | recent
                        · exact (same (old.1.1.symm.trans request.1)).elim
                        · rw [advancing] at physicalClock
                          change next.application.current.native.clock =
                            execution.application.current.native.clock + 1 at physicalClock
                          omega
                      · have origin := PhaseSeedScheduler.environmentStep_request_origin
                          runtime leaks execution next command
                          (serviceGraph_revealRelaxedOrdered setup .concurrentReveals) valid
                          geometry.1 geometry.2.1 geometry.2.2.1 geometry.2.2.2 supported owner
                          coordinate entered request stamp
                        rcases origin with old | recent
                        · exact (same (old.1.1.symm.trans request.1)).elim
                        · have zero : PhaseSeedCalendar.commandTicks runtime leaks command = 0 := by
                            cases command with
                            | wait => rfl
                            | activate who => rfl
                            | «include» identifier => rfl
                            | application command =>
                                cases command with
                                | advanceClock => exact (advancing rfl).elim
                                | executeSample event => rfl
                                | expire event => rfl
                          rw [zero, Nat.add_zero] at physicalClock
                          exact physicalClock.trans_le recent

/-- The concrete fixed-seed service supplies zero-delay owner opportunities
on all legal raw histories, with no packet-admission restriction. -/
theorem family_opportunity (seeds : Seeds) :
    PhaseService.Opportunity runtime leaks initial horizon (family seeds) (fun _ => 0) := by
  intro current trace event owner entered actor ready stamp late
  have geometry := raw_phase_geometry (family seeds) current trace
  have actualReady := (State.publicView_eventReady _ _).mp ready
  have request := current.execution.application.request_of_ready
    (serviceGraph_revealRelaxedOrdered setup .concurrentReveals) geometry.1 geometry.2.1
    geometry.2.2.1 geometry.2.2.2 event actualReady owner actor
  rcases raw_pending_opportunity seeds trace _ owner entered request stamp with recorded | unserved
  · exact recorded
  · change entered + 0 < current.execution.application.current.native.clock at late
    omega

end Vegas.Examples.CommitSeedSignalling
