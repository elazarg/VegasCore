module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ServiceRosterAsync

@[expose] public section

/-! # Roster service that offers only the tagged event -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
  (rosters : setup.informationGraph.EventId → List Player)

local notation "app" => application setup (Vegas.timeouts setup) leaks

/-- Execute the public calendar, skipping a roster entry when its tagged event
is no longer ready. -/
def readyRosterScheduler (network : (NetworkPolicy (timeouts setup)) leaks) : (app).Scheduler :=
  fun past view => match (rosterPlan setup rosters)[past.length]? with
    | some (event, .player who) => PMF.pure
        (if view.application.EventReady event then .activate who else .wait)
    | _ => rosterScheduler setup leaks rosters network past view

instance readyRoster_finiteNature [setup.FiniteInitialLaw] [leaks.FiniteSupport]
    (network : (NetworkPolicy (timeouts setup)) leaks) :
    (app).FiniteNature (initialLaw setup) (readyRosterScheduler setup leaks rosters network) where
  toFiniteEnvironment := inferInstance
  initial_finite := serviceInitialLaw_support_finite setup setup.informationDependencies
  scheduler_finite past view := by
    have finite := (rosterScheduler_finiteNature setup leaks rosters network).scheduler_finite
      past view
    cases found : (rosterPlan setup rosters)[past.length]? with
    | none => simpa only [readyRosterScheduler, found] using finite
    | some pair =>
      obtain ⟨tag, instruction⟩ := pair
      cases instruction <;> try exact (by simpa only [readyRosterScheduler, found] using finite)
      simp only [readyRosterScheduler, found, PMF.support_pure]
      exact Set.finite_singleton _

variable {setup leaks rosters}

private theorem skippedRosterEntry {event : setup.informationGraph.EventId}
    {offset entryClock : Nat} {obsolete : Bool} {control : (app).Control}
    (phase : RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control)
    (early : offset < (rosters event).length)
    (unready : ¬control.execution.application.publicView.EventReady event)
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (next : (app).Execution)
    (reached : next ∈ (control.execution.environmentStep (app) .wait).support) :
    RosterCalendarPhase setup leaks rosters event (offset + 1) entryClock obsolete
      ⟨remaining, none, next⟩ := by
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
  cases (PMF.mem_support_pure_iff _ _).mp supported
  have classified := rosterBlockCompleted_record setup leaks rosters
    control.execution.environmentRecall (control.execution.observeEnvironment app)
    (control.execution.observeEnvironment app) event .wait (by rw [phase.position]; omega)
  have oldTicks : offset - ((rosters event).length + 1) = 0 := by omega
  have nextTicks : offset + 1 - ((rosters event).length + 1) = 0 := by omega
  exact {
    position := by simp [phase.position, Nat.add_assoc]
    inside := by rw [rosterBlock_length]; omega
    remaining := by
      have total := phase.remaining
      rw [counted] at total
      change remaining + (control.execution.environmentRecall ++ [_]).length = _
      simp only [List.length_append, List.length_singleton]
      omega
    classified := classified.trans phase.classified
    prior := phase.prior
    obsolete_done := phase.obsolete_done
    live_prefix := fun live _ => phase.live_prefix live early.le
    sampled := fun _ late => absurd late (by omega)
    clock := by simpa only [oldTicks, nextTicks] using phase.clock
    entered := phase.entered
    future := phase.future
    future_started := phase.future_started
    opportunity := fun _ _ _ _ ready _ => (unready
      ((control.execution.application.publicView_eventReady event).mpr ready)).elim
    responses := phase.responses
    activation := by intros; contradiction
    inclusion := fun late => absurd late (by omega) }



private theorem readyRoster_environment {event : setup.informationGraph.EventId}
    {offset entryClock : Nat} {obsolete : Bool} {control : (app).Control}
    (network : (NetworkPolicy (timeouts setup)) leaks)
    (phase : RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control)
    {inputs : setup.informationGraph.Inputs} (invariant : control.execution.application.Invariant
      inputs)
    (stable : EntryEventStable (timeouts setup) leaks control.execution)
    (quiescent : ∀ query, ¬ control.execution.application.AutomaticReady query)
    (origins : control.execution.Provenance app)
    (recalled : control.execution.InputRecall app)
    (retained : control.execution.network.PendingOrPublished)
    (sound : control.execution.ReceiptsSound app (fun _ => True))
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (command : (app).Command)
    (selected : command ∈ (readyRosterScheduler setup leaks rosters network
      control.execution.environmentRecall (control.execution.observeEnvironment app)).support)
    (next : (app).Execution)
    (reached : next ∈ (control.execution.environmentStep app command).support) :
    RosterCalendarInvariant setup leaks rosters
      (some ⟨remaining, command.actor? app, next⟩) := by
  classical
  let past := control.execution.environmentRecall
  let view := control.execution.observeEnvironment app
  by_cases skip : ∃ tag who, (rosterPlan setup rosters)[past.length]? = some (tag, .player who)
      ∧ ¬view.application.EventReady tag
  · obtain ⟨tag, who, found, unready⟩ := skip
    change command ∈ (readyRosterScheduler setup leaks rosters network past view).support
      at selected
    simp only [readyRosterScheduler, found, unready, ↓reduceIte,
      PMF.mem_support_pure_iff] at selected
    subst command
    have located := rosterPlan_getElem_block setup rosters event offset phase.inside
    rw [← phase.position] at located
    change (rosterPlan setup rosters)[control.execution.environmentRecall.length]? = _ at found
    rw [found] at located
    obtain ⟨instruction, block, equal⟩ := Option.map_eq_some_iff.mp located.symm
    cases equal
    have early : offset < (rosters event).length := by
      by_contra! beyond
      have member : ServiceInstruction.player who ∈ rosterPhaseEnding setup event := by
        obtain ⟨k, eq⟩ := Nat.exists_eq_add_of_le beyond
        rw [eq, rosterBlock_ending] at block
        exact List.mem_of_getElem? block
      unfold rosterPhaseEnding at member
      cases actor : setup.informationGraph.actor? event <;> simp [actor] at member
    exact Or.inl ⟨event, offset + 1, entryClock, obsolete,
      skippedRosterEntry phase early unready remaining counted next reached⟩
  · apply phase.environment network invariant stable quiescent origins recalled retained sound
      remaining counted command _ next reached
    change command ∈ (readyRosterScheduler setup leaks rosters network past view).support
      at selected
    change command ∈ (rosterScheduler setup leaks rosters network past view).support
    cases found : (rosterPlan setup rosters)[past.length]? with
    | none => simpa only [readyRosterScheduler, found] using selected
    | some pair =>
      obtain ⟨tag, instruction⟩ := pair
      cases instruction <;> try exact (by simpa only [readyRosterScheduler, found] using selected)
      rename_i who
      have ready : view.application.EventReady tag := by
        by_contra absent
        exact skip ⟨tag, who, found, absent⟩
      simpa only [readyRosterScheduler, rosterScheduler, found, ready, ↓reduceIte,
        interactionInstruction] using selected

variable (setup leaks rosters)
theorem readyRoster_transition
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (rosters : setup.informationGraph.EventId → List Player)
    (network : (NetworkPolicy (timeouts setup)) leaks)
    (before after : (application setup (Vegas.timeouts setup) leaks).ProtocolState)
    (prior : ((application setup (Vegas.timeouts setup) leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (readyRosterScheduler setup leaks rosters network)).Trace
        before)
    (valid : RosterCalendarInvariant setup leaks rosters before)
    (joint : Player → Option (application setup (Vegas.timeouts setup) leaks).Action)
    (reached : after ∈ ((application setup (Vegas.timeouts setup) leaks).transition (initialLaw
      setup) (rosterPlan setup rosters).length (readyRosterScheduler setup leaks rosters network)
        before joint).support) :
    RosterCalendarInvariant setup leaks rosters after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact RosterCalendarInvariant.initial setup leaks rosters state supported
  | some control =>
      obtain ⟨⟨inputs, invariant⟩, origins, recalled, retained, sound⟩ :=
        roster_trace_facts setup leaks _ _ prior
      have facts := legalFacts setup leaks (rosterPlan setup rosters).length
        (readyRosterScheduler setup leaks rosters network) control prior
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          rcases valid with ⟨event, offset, entryClock, obsolete, phase⟩ | ⟨_, idle, _⟩
          · exact Or.inl ⟨event, offset, entryClock, obsolete, phase.respond who rfl _⟩
          · cases idle
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact valid
          | succ remaining =>
              obtain ⟨command, selected, moved⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              rcases valid with ⟨event, offset, entryClock, obsolete, phase⟩ | ⟨done, _, _⟩
              · exact readyRoster_environment network phase invariant facts.eventStable
                    facts.quiescent origins
                  recalled retained sound remaining rfl command selected next supported
              · cases done

/-- Every initialized raw history retains the public roster calendar certificate. -/
theorem readyRoster_history
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (rosters : setup.informationGraph.EventId → List Player)
    (network : (NetworkPolicy (timeouts setup)) leaks) :
    ∀ {state} (_trace : ((application setup (Vegas.timeouts setup) leaks).protocol (initialLaw
      setup)
      (rosterPlan setup rosters).length (readyRosterScheduler setup leaks rosters network)).Trace
        state),
      RosterCalendarInvariant setup leaks rosters state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      readyRoster_transition setup leaks rosters network _ _ prior
        (readyRoster_history setup leaks rosters network prior) joint reached



theorem readyRoster_contract (network : (NetworkPolicy (timeouts setup)) leaks)
    (opportunities : ActorOpportunities setup rosters) :
    AsyncContract (timeouts setup) leaks (initialLaw setup) (rosterPlan setup rosters).length
      (readyRosterScheduler setup leaks rosters network) (fun event => event.val) (fun _ => 0) where
  opportunity := RosterCalendarInvariant.opportunity setup leaks rosters _
    (fun _ trace => readyRoster_history setup leaks rosters network trace) opportunities
  inclusion := RosterCalendarInvariant.protectedInclusion setup leaks rosters _
    (fun _ trace => readyRoster_history setup leaks rosters network trace)
  completes := RosterCalendarInvariant.completesPlay setup leaks rosters _
    (fun _ trace => readyRoster_history setup leaks rosters network trace)

end Vegas
