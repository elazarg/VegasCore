module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ServiceRosterInvariant
public import Vegas.Pending.ExecutionFacts

@[expose] public section

/-! # The public roster calendar at every initialized history

Supported scheduler commands preserve the native calendar certificate. Induction
through initialization, responses and environment commands supplies the
certificate for arbitrary raw player strategies and pending observations.
-/

noncomputable section

namespace Vegas

open Interaction EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every supported tagged scheduler command preserves the native calendar. -/
theorem RosterCalendarPhase.environment
    {graph : EventGraph Player L}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize)}
    {rosters : graph.EventId → List Player} {event :
      graph.EventId}
    {offset entryClock : Nat} {obsolete : Bool}
    {control : (rosterApplication graph leaks).Control}
    (network : (NetworkPolicy (rosterTimeouts graph)) leaks)
    (phase : RosterCalendarPhase graph leaks rosters event offset entryClock obsolete control)
    {inputs : graph.sequentialize.Inputs} (invariant : control.execution.application.Invariant
      inputs)
    (stable : EntryEventStable (rosterTimeouts graph) leaks control.execution)
    (quiescent : ∀ query, ¬ control.execution.application.AutomaticReady query)
    (origins : control.execution.Provenance (rosterApplication graph leaks))
    (recalled : control.execution.InputRecall (rosterApplication graph leaks))
    (retained : control.execution.network.PendingOrPublished)
    (sound : control.execution.ReceiptsSound (rosterApplication graph leaks)
      (fun _ => True))
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (command : (rosterApplication graph leaks).Command)
    (selected : command ∈ (rosterScheduler graph leaks rosters network
      control.execution.environmentRecall
      (control.execution.observeEnvironment
        (rosterApplication graph leaks))).support)
    (next : (rosterApplication graph leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep
      (rosterApplication graph leaks) command).support) :
    RosterCalendarInvariant graph leaks rosters
      (some ⟨remaining, command.actor? (rosterApplication graph leaks), next⟩)
        := by
  have found : (rosterPlan graph rosters)[control.execution.environmentRecall.length]? =
      ((rosterBlock graph rosters event)[offset]?).map (Prod.mk event) := by
    rw [phase.position]
    exact rosterPlan_getElem_block graph rosters event offset phase.inside
  have blockLength := rosterBlock_length graph rosters event
  have inside := phase.inside
  rw [blockLength] at inside
  rcases (by omega : offset < (rosters event).length ∨ offset = (rosters event).length ∨
      ((rosters event).length < offset ∧ offset < (rosters event).length + event.val + 2) ∨
      offset = (rosters event).length + event.val + 2) with
    early | atEnding | ⟨late, ticking⟩ | atExpiry
  · have roster := rosterBlock_roster graph rosters event offset early
    simp only [rosterScheduler, found, roster, Option.map_some, interactionInstruction,
      PMF.mem_support_pure_iff] at selected
    subst command
    exact Or.inl ⟨event, offset + 1, entryClock, obsolete,
      phase.activate_step early _ (List.getElem?_eq_getElem early) remaining counted next reached⟩
  · have atEnd := rosterBlock_ending graph rosters event 0
    rw [rosterPhaseEnding_first, Nat.add_zero, ← atEnding] at atEnd
    cases owned : graph.sequentialize.actor? event with
    | none =>
        simp only [rosterScheduler, found, atEnd, owned, Option.map_some, interactionInstruction,
          PMF.mem_support_pure_iff] at selected
        subst command
        exact Or.inl ⟨event, offset + 1, entryClock, obsolete,
          phase.sample_step atEnding owned invariant remaining counted next reached⟩
    | some owner =>
        simp only [rosterScheduler, found, atEnd, owned, Option.map_some, interactionInstruction,
          PMF.mem_support_pure_iff] at selected
        subst command
        have actorNone : ((reactiveLatest (rosterTimeouts graph)) leaks event owner
            (control.execution.observeEnvironment
              (rosterApplication graph leaks))).actor?
            (rosterApplication graph leaks) = none := by
          unfold reactiveLatest
          split <;> rfl
        rw [actorNone]
        exact Or.inl ⟨event, offset + 1, entryClock, obsolete,
          phase.include_step atEnding owner owned invariant origins recalled retained sound
            remaining counted next reached⟩
  · have atTick := rosterBlock_ending graph rosters event
      (offset - (rosters event).length - 1 + 1)
    rw [rosterPhaseEnding_tick graph event _ (by omega),
      show (rosters event).length + (offset - (rosters event).length - 1 + 1) = offset by omega]
      at atTick
    simp only [rosterScheduler, found, atTick, Option.map_some,
      PMF.mem_support_pure_iff] at selected
    let tickCommand : (rosterApplication graph leaks).Command :=
      if obsolete then .wait else .application .advanceClock
    have selectedTick : command = tickCommand := by
      simpa only [tickCommand, phase.classified] using selected
    have tickReached : next ∈ (control.execution.environmentStep
        (rosterApplication graph leaks) tickCommand).support := by
      simpa only [selectedTick] using reached
    have actorNone : command.actor? (rosterApplication graph leaks) = none := by
      rw [selectedTick]
      dsimp only [tickCommand]
      cases obsolete <;> rfl
    rw [actorNone]
    exact Or.inl ⟨event, offset + 1, entryClock, obsolete,
      phase.tick_step late ticking quiescent remaining counted next tickReached⟩
  · have atEnd := rosterBlock_ending graph rosters event (event.val + 2)
    rw [rosterPhaseEnding_expire,
      show (rosters event).length + (event.val + 2) = offset by omega] at atEnd
    simp only [rosterScheduler, found, atEnd, Option.map_some, interactionInstruction,
      PMF.mem_support_pure_iff] at selected
    subst command
    exact phase.expire_step atExpiry invariant stable remaining counted next reached

theorem RosterCalendarInvariant.transition
    (graph : EventGraph Player L) (inputs : PMF graph.Inputs)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (rosters : graph.EventId → List Player)
    (network : (NetworkPolicy (rosterTimeouts graph)) leaks)
    (before after : (rosterApplication graph leaks).ProtocolState)
    (prior : ((rosterApplication graph leaks).protocol (rosterInitialDistribution graph inputs)
      (rosterPlan graph rosters).length (rosterScheduler graph leaks rosters network)).Trace before)
    (valid : RosterCalendarInvariant graph leaks rosters before)
    (joint : Player → Option (rosterApplication graph leaks).Action)
    (reached : after ∈ ((rosterApplication graph leaks).transition
      (rosterInitialDistribution graph inputs) (rosterPlan graph rosters).length
      (rosterScheduler graph leaks rosters network)
        before joint).support) :
    RosterCalendarInvariant graph leaks rosters after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact RosterCalendarInvariant.initial graph inputs leaks rosters state supported
  | some control =>
      obtain ⟨⟨_, invariant⟩, origins, recalled, retained, sound⟩ :=
        roster_trace_facts (rosterTimeouts graph) leaks inputs _ _ prior
      have facts := EventGraphRuntime.legalFacts (rosterTimeouts graph) leaks inputs
        (rosterPlan graph rosters).length
        (rosterScheduler graph leaks rosters network) control prior
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
              · exact RosterCalendarPhase.environment network phase invariant facts.eventStable
                    facts.quiescent origins
                  recalled retained sound remaining rfl command selected next supported
              · cases done

/-- Every initialized raw history retains the public roster calendar certificate. -/
theorem RosterCalendarInvariant.history
    (graph : EventGraph Player L) (inputs : PMF graph.Inputs)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (rosters : graph.EventId → List Player)
    (network : (NetworkPolicy (rosterTimeouts graph)) leaks) :
    ∀ {state} (_trace : ((rosterApplication graph leaks).protocol
      (rosterInitialDistribution graph inputs)
      (rosterPlan graph rosters).length (rosterScheduler graph leaks rosters network)).Trace state),
      RosterCalendarInvariant graph leaks rosters state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      RosterCalendarInvariant.transition graph inputs leaks rosters network _ _ prior
        (RosterCalendarInvariant.history graph inputs leaks rosters network prior) joint reached

end Vegas
