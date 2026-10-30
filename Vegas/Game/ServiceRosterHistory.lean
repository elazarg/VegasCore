/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceRosterInvariant
import Vegas.Game.SourceServiceFacts

/-! # The public roster calendar at every initialized history

Supported scheduler commands preserve the native calendar certificate. Induction
through initialization, responses and environment commands supplies the
certificate for arbitrary raw player strategies and pending observations.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every supported tagged scheduler command preserves the native calendar. -/
theorem RosterCalendarPhase.environment
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
    {offset entryClock : Nat} {obsolete : Bool}
    {control : (application setup (Vegas.runtime setup) leaks).Control}
    (network : (runtime setup).NetworkPolicy leaks)
    (phase : RosterCalendarPhase setup leaks rosters event offset entryClock obsolete control)
    {inputs : (graph setup).Inputs} (invariant : control.execution.application.Invariant inputs)
    (stable : EntryEventStable (runtime setup) leaks control.execution)
    (quiescent : ∀ query, ¬ control.execution.application.AutomaticReady query)
    (origins : control.execution.Provenance (application setup (Vegas.runtime setup) leaks))
    (recalled : control.execution.InputRecall (application setup (Vegas.runtime setup) leaks))
    (retained : control.execution.network.PendingOrPublished)
    (sound : control.execution.ReceiptsSound (application setup (Vegas.runtime setup) leaks)
      (fun _ => True))
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (command : (application setup (Vegas.runtime setup) leaks).Command)
    (selected : command ∈ (rosterScheduler setup leaks rosters network
      control.execution.environmentRecall
      (control.execution.observeEnvironment
        (application setup (Vegas.runtime setup) leaks))).support)
    (next : (application setup (Vegas.runtime setup) leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep
      (application setup (Vegas.runtime setup) leaks) command).support) :
    RosterCalendarInvariant setup leaks rosters
      (some ⟨remaining, command.actor? (application setup (Vegas.runtime setup) leaks), next⟩) := by
  have found : (rosterPlan setup rosters)[control.execution.environmentRecall.length]? =
      ((rosterBlock setup rosters event)[offset]?).map (Prod.mk event) := by
    rw [phase.position]
    exact rosterPlan_getElem_block setup rosters event offset phase.inside
  have blockLength := rosterBlock_length setup rosters event
  have inside := phase.inside
  rw [blockLength] at inside
  rcases (by omega : offset < (rosters event).length ∨ offset = (rosters event).length ∨
      ((rosters event).length < offset ∧ offset < (rosters event).length + event.val + 2) ∨
      offset = (rosters event).length + event.val + 2) with
    early | atEnding | ⟨late, ticking⟩ | atExpiry
  · have roster := rosterBlock_roster setup rosters event offset early
    simp only [rosterScheduler, found, roster, Option.map_some, interactionInstruction,
      PMF.mem_support_pure_iff] at selected
    subst command
    exact Or.inl ⟨event, offset + 1, entryClock, obsolete,
      phase.activate_step early _ (List.getElem?_eq_getElem early) remaining counted next reached⟩
  · have atEnd := rosterBlock_ending setup rosters event 0
    rw [rosterPhaseEnding_first, Nat.add_zero, ← atEnding] at atEnd
    cases owned : (graph setup).actor? event with
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
        have actorNone : ((runtime setup).reactiveLatest leaks event owner
            (control.execution.observeEnvironment
              (application setup (Vegas.runtime setup) leaks))).actor?
            (application setup (Vegas.runtime setup) leaks) = none := by
          unfold reactiveLatest
          split <;> rfl
        rw [actorNone]
        exact Or.inl ⟨event, offset + 1, entryClock, obsolete,
          phase.include_step atEnding owner owned invariant origins recalled retained sound
            remaining counted next reached⟩
  · have atTick := rosterBlock_ending setup rosters event
      (offset - (rosters event).length - 1 + 1)
    rw [rosterPhaseEnding_tick setup event _ (by omega),
      show (rosters event).length + (offset - (rosters event).length - 1 + 1) = offset by omega]
      at atTick
    simp only [rosterScheduler, found, atTick, Option.map_some,
      PMF.mem_support_pure_iff] at selected
    let tickCommand : (application setup (Vegas.runtime setup) leaks).Command :=
      if obsolete then .wait else .application .advanceClock
    have selectedTick : command = tickCommand := by
      simpa only [tickCommand, phase.classified] using selected
    have tickReached : next ∈ (control.execution.environmentStep
        (application setup (Vegas.runtime setup) leaks) tickCommand).support := by
      simpa only [selectedTick] using reached
    have actorNone : command.actor? (application setup (Vegas.runtime setup) leaks) = none := by
      rw [selectedTick]
      dsimp only [tickCommand]
      cases obsolete <;> rfl
    rw [actorNone]
    exact Or.inl ⟨event, offset + 1, entryClock, obsolete,
      phase.tick_step late ticking quiescent remaining counted next tickReached⟩
  · have atEnd := rosterBlock_ending setup rosters event (event.val + 2)
    rw [rosterPhaseEnding_expire,
      show (rosters event).length + (event.val + 2) = offset by omega] at atEnd
    simp only [rosterScheduler, found, atEnd, Option.map_some, interactionInstruction,
      PMF.mem_support_pure_iff] at selected
    subst command
    exact phase.expire_step atExpiry invariant stable remaining counted next reached

private theorem RosterCalendarInvariant.transition
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (before after : (application setup (Vegas.runtime setup) leaks).ProtocolState)
    (prior : ((application setup (Vegas.runtime setup) leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace before)
    (valid : RosterCalendarInvariant setup leaks rosters before)
    (joint : Player → Option (application setup (Vegas.runtime setup) leaks).Action)
    (reached : after ∈ ((application setup (Vegas.runtime setup) leaks).transition (initialLaw
      setup) (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
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
        (rosterScheduler setup leaks rosters network) control prior
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
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) :
    ∀ {state} (_trace : ((application setup (Vegas.runtime setup) leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace state),
      RosterCalendarInvariant setup leaks rosters state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      RosterCalendarInvariant.transition setup leaks rosters network _ _ prior
        (RosterCalendarInvariant.history setup leaks rosters network prior) joint reached

end Vegas
