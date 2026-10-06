/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceReachedDecoding
import Vegas.Game.IntendedPreservation
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Source debts read through the native decoding

Every native configuration reached under any players and any scheduler decodes
to a point of the source program at its completed prefix
(`Vegas.SourceResidual`). The decoding advances by one source step whenever the
native configuration completes an event (`Vegas.SourceResidual.step`), whatever
action completes it: a sample, any binding including a failed one, or any
disclosure decision. A property of source points closed under every source
step therefore persists along every native protocol transition, under arbitrary
responses and scheduler choices (`Vegas.decodedHolds_transition`).

A source debt is such a property
(`Vegas.SourceProgram.ProtocolState.indebted_step`). If the configuration of a
native history decodes to a point at which a player is indebted, every terminal
history of terminal play from it, under any players, has a readout recording a
failed reveal of that player, provided the scheduler completes play
(`Vegas.decoded_indebted_failedReveals`).

From a decoding in the intended game, one native completion either stays in the
intended game or is a departure of the event's actor, who is then indebted
unless the departure is a failed binding (`Vegas.SourceResidual.intended_or_departure`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {profile : BehavioralProfile setup.program}

/-- A property of source points closed under every source step, whatever the
joint action. -/
def StepClosed (setup : Setup (Player := Player) (L := L))
    (property : ProtocolState setup.program → Prop) : Prop :=
  ∀ state joint target, property state →
    target ∈ (ProtocolState.step setup.program state joint).support → property target

/-- A property holds at the decoding of a configuration at a prefix. -/
def DecodedHolds (property : ProtocolState setup.program → Prop) (rank : Nat)
    (config : (graph setup).Config) : Prop :=
  ∀ state, sourceServicePrefix? setup rank config = some state → property state

/-- A configuration step keeps a step-closed property of the decoding, at
whichever prefix the step reaches. -/
theorem SourceResidual.decodedHolds_configStep
    {property : ProtocolState setup.program → Prop} (closed : StepClosed setup property)
    {rank : Nat} {before after : (graph setup).Config}
    (residual : SourceResidual setup profile rank before)
    (holds : DecodedHolds property rank before)
    (step : ConfigStep setup before after) {next : Nat} (ordered : after.cut.IsPrefix next) :
    DecodedHolds property next after := by
  rcases step with same | ⟨event, ready, action, member⟩
  · subst same
    rw [isPrefix_unique ordered residual.checkpoint.ordered]
    exact holds
  · have advanced : after.cut.IsPrefix (rank + 1) := by
      rw [before.step_cut event ready action after member]
      exact residual.checkpoint.ordered.complete_at event ready
        ((ready_iff_rank setup before rank residual.checkpoint.ordered event).mp ready)
    rw [isPrefix_unique ordered advanced]
    obtain ⟨successor, reached⟩ := residual.step event ready action after member
    intro state decoded
    rw [successor.decode, Option.some.injEq] at decoded
    subst decoded
    exact closed _ _ _ (holds _ residual.decode) reached

/-- **Leaving the intended game at a native completion.** Completing the ready
event of a configuration whose decoding is a point of the intended game
reaches a configuration whose decoding is again a point of the intended game,
unless the event's actor departs: its decoded action is not offered by the
intended game there, and, when it is a source action under the value interface
(any binding value or disclosure decision, but not a failed binding), the actor
is indebted at the new decoding. -/
theorem SourceResidual.intended_or_departure {rank : Nat}
    {before : (graph setup).Config} (residual : SourceResidual setup profile rank before)
    (intended : ProtocolState.Intended setup.program
      (residual.lift (ProtocolState.entry residual.program residual.source)))
    (event : (graph setup).EventId) (ready : before.cut.Ready event)
    (action : (graph setup).Action event) (after : (graph setup).Config)
    (member : after ∈ (before.step event ready action).support) :
    ∃ next : SourceResidual setup profile (rank + 1) after,
      ProtocolState.Intended setup.program
          (next.lift (ProtocolState.entry next.program next.source)) ∨
        ∃ who, ProtocolView.actor who setup.program (ProtocolState.observe who setup.program
            (residual.lift (ProtocolState.entry residual.program residual.source))) = some who ∧
          ∀ chosen, decodeEventAction setup.program event action = some chosen →
            chosen ∉ ProtocolView.intendedAvailable who setup.program
              (ProtocolState.observe who setup.program
                (residual.lift (ProtocolState.entry residual.program residual.source))) ∧
            (chosen ∈ ProtocolView.available who setup.program
                (CommitmentInterface.values setup.program)
                (ProtocolState.observe who setup.program
                  (residual.lift (ProtocolState.entry residual.program residual.source))) →
              ProtocolState.Indebted who setup.program
                (next.lift (ProtocolState.entry next.program next.source))) := by
  obtain ⟨next, reached⟩ := residual.step event ready action after member
  refine ⟨next, ?_⟩
  rcases ProtocolState.intended_or_departure setup.program _ _ _ intended reached with
    kept | ⟨who, acts, departs⟩
  · exact Or.inl kept
  · refine Or.inr ⟨who, acts, fun chosen decoded => ⟨departs chosen decoded, fun available => ?_⟩⟩
    exact ProtocolState.indebted_of_deviation who setup.program _ (fun _ => rfl) _ intended _
      chosen decoded acts available (departs chosen decoded) _ reached

variable (setup) in
/-- An initialized native protocol state whose configuration has a source
residual at a prefix where a step-closed property holds of its decoding. -/
def DecodedState (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : BehavioralProfile setup.program)
    (property : ProtocolState setup.program → Prop) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control => ∃ rank,
      Nonempty (SourceResidual setup profile rank control.execution.application.config) ∧
        DecodedHolds property rank control.execution.application.config

/-- One protocol transition changes the configuration by one configuration
step, under arbitrary responses and scheduler choices. -/
theorem transition_configStep
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (before after : (application setup leaks).Control)
    (joint : Player → Option (application setup leaks).Action)
    (reached : some after ∈ ((application setup leaks).transition initial horizon scheduler
      (some before) joint).support) :
    ConfigStep setup before.execution.application.config after.execution.application.config := by
  rcases before with ⟨remaining, current, execution⟩
  cases current with
  | some who =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
      exact Or.inl ((runtime setup).reactive_respond_application leaks execution who _).1
  | none =>
      cases remaining with
      | zero =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
          exact Or.inl rfl
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
          cases Option.some.inj same
          exact environmentStep_configStep setup leaks execution next command supported

/-- **Decoded properties persist.** A step-closed property of the decoding of an
initialized native state holds after every protocol transition, under arbitrary
responses and scheduler choices. -/
theorem decodedHolds_transition
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {property : ProtocolState setup.program → Prop} (closed : StepClosed setup property)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (before after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (holds : DecodedState setup leaks profile property before)
    (reached : after ∈ ((application setup leaks).transition initial horizon scheduler before
      joint).support) :
    DecodedState setup leaks profile property after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨rank, ⟨residual⟩, decoded⟩ := holds
      have stays : ∃ next, after = some next := by
        rcases control with ⟨remaining, current, execution⟩
        cases current with
        | some who => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
        | none =>
            cases remaining with
            | zero => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
            | succ remaining =>
                obtain ⟨command, _, moved⟩ :=
                  Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                obtain ⟨next, _, same⟩ := PMF.support_map .. ▸ moved
                exact ⟨_, same.symm⟩
      obtain ⟨next, rfl⟩ := stays
      have step := transition_configStep initial horizon scheduler control next joint reached
      rcases step.prefix rank residual.checkpoint.ordered with same | advanced
      · refine ⟨rank, residual.configStep step rank ?_, ?_⟩
        · rw [same]
          exact residual.checkpoint.ordered
        · exact residual.decodedHolds_configStep closed decoded step (by
            rw [same]
            exact residual.checkpoint.ordered)
      · exact ⟨rank + 1, residual.configStep step (rank + 1) advanced,
          residual.decodedHolds_configStep closed decoded step advanced⟩

/-- A terminal cut is a prefix only of the full event count. -/
theorem isPrefix_eventCount_of_terminal {cut : (graph setup).order.Cut} {rank : Nat}
    (ordered : cut.IsPrefix rank) (terminal : cut.Terminal) :
    rank = (graph setup).order.eventCount := by
  apply le_antisymm ordered.1
  by_contra short
  push Not at short
  have completed : (⟨rank, short⟩ : Fin (graph setup).order.eventCount) ∈ cut.completed := by
    rw [terminal]
    exact Finset.mem_univ _
  exact Nat.lt_irrefl _ ((ordered.2 _).mp completed)

/-- A player's debt is closed under every source step. -/
theorem indebted_stepClosed (who : Player) :
    StepClosed setup (ProtocolState.Indebted who setup.program) :=
  fun state joint target indebted reached =>
    ProtocolState.indebted_step who setup.program state joint target indebted reached

/-- **Decoded debts are paid.** Suppose a native history of a response menu,
under a scheduler that completes play, has a configuration that decodes at its
prefix to a source point at which `who` is indebted. Then every terminal history
of terminal play from it, under any players, has a source readout recording at
least one failed reveal of `who`. -/
theorem decoded_indebted_failedReveals [Fintype Player]
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (certificate : (menu.protocol (initialLaw setup) horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (indebted : DecodedState setup leaks profile (ProtocolState.Indebted who setup.program)
      history.state) :
    ∀ final ∈ ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        certificate players history).support,
      ∃ terminal, sourceReadout setup leaks final.state = some terminal ∧
        1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal) := by
  intro final supported
  have reachedDebt := (menu.information (initialLaw setup) horizon
    scheduler).runBehavioralTerminalFrom_support_closed certificate players
    (DecodedState setup leaks profile (ProtocolState.Indebted who setup.program))
    (fun state joint _ target holds reached =>
      decodedHolds_transition (indebted_stepClosed who) (initialLaw setup) horizon scheduler
        state target joint holds reached)
    history indebted final supported
  have stopped := (menu.information (initialLaw setup) horizon
    scheduler).runBehavioralTerminalFrom_support_terminal certificate players history final
    supported
  cases state : final.state with
  | none =>
      rw [state] at reachedDebt
      exact reachedDebt.elim
  | some control =>
      rw [state] at reachedDebt stopped
      obtain ⟨rank, ⟨residual⟩, decoded⟩ := reachedDebt
      have trace : ((application setup leaks).protocol (initialLaw setup) horizon
          scheduler).Trace (some control) :=
        state ▸ menu.toRawTrace (initialLaw setup) horizon scheduler final.trace
      have terminalCut := completes control trace stopped
      have full := isPrefix_eventCount_of_terminal residual.checkpoint.ordered terminalCut
      subst full
      have read := sourceServicePrefix?_terminal_readout setup control.execution.application.config
      obtain ⟨point, decodedEq⟩ :
          ∃ point, sourceServicePrefix? setup (eventCount setup.program)
            control.execution.application.config = some point :=
        ⟨_, residual.decode⟩
      have pointDebt := decoded point decodedEq
      rw [decodedEq] at read
      obtain ⟨terminal, terminalRead⟩ :=
        ProtocolState.exists_readout_of_terminal setup.program point
          (decodeSourcePrefix?_terminal setup.program _ _ _ _ _ _ point decodedEq)
      refine ⟨terminal, ?_, ProtocolState.failedReveals_pos_of_indebted who setup.program point
        pointDebt terminalRead⟩
      rw [sourceReadout_eq_decode, ← read]
      exact terminalRead

end Vegas
