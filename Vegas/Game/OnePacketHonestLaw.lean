/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Game.IntendedEffectiveOpening
import Vegas.Source.IntendedDeparture
import Vegas.Game.ServiceOpeningHonestLaw

/-! # The intended game along first-turn clients of the effective opening

**Decoded debts reach the readout.** Under any players and any scheduler that
completes play, if an execution reached by rounds from initialization decodes
to a point at which a player owes a failed reveal, every execution the rounds
reach from it at the horizon reads out a terminal store recording a failed
reveal of that player (`Vegas.runRounds_owesFailure_failedReveals`).

**The first-turn clients stay in the intended game.** Under the asynchronous
contract, the first-turn clients of the intended effective opening
(`Vegas.openingClients`) read out the intended law of typed readouts
(`Vegas.openingClients_readout_law`). That law records no failed reveal, while
a decoded debt would record one with positive probability; and every source step
from the intended game stays in it or leaves a debt. So every execution the
clients reach within the horizon decodes to a point of the intended game
(`Vegas.openingClients_intended`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Debts

variable (setup leaks) in
/-- An execution whose configuration has a source residual at a prefix where a
property holds of its decoding. -/
def DecodedExecution (profile : BehavioralProfile setup.program)
    (property : ProtocolState setup.program → Prop)
    (execution : (application setup leaks).Execution) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank execution.application.config) ∧
    DecodedHolds property rank execution.application.config

variable {profile : BehavioralProfile setup.program}

/-- A round keeps a step-closed property of the decoding. -/
theorem DecodedExecution.round {property : ProtocolState setup.program → Prop}
    (closed : StepClosed setup property) {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    {execution next : (application setup leaks).Execution}
    (holds : DecodedExecution setup leaks profile property execution)
    (moved : next ∈ ((application setup leaks).round scheduler players execution).support) :
    DecodedExecution setup leaks profile property next := by
  obtain ⟨rank, ⟨residual⟩, decoded⟩ := holds
  have step := round_configStep setup leaks scheduler players execution next moved
  rcases step.prefix rank residual.checkpoint.ordered with same | advanced
  · refine ⟨rank, residual.configStep step rank ?_, ?_⟩
    · rw [same]
      exact residual.checkpoint.ordered
    · exact residual.decodedHolds_configStep closed decoded step (by
        rw [same]
        exact residual.checkpoint.ordered)
  · exact ⟨rank + 1, residual.configStep step (rank + 1) advanced,
      residual.decodedHolds_configStep closed decoded step advanced⟩

/-- Rounds keep a step-closed property of the decoding. -/
theorem DecodedExecution.runRounds {property : ProtocolState setup.program → Prop}
    (closed : StepClosed setup property) (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) :
    ∀ (more : Nat) (execution : (application setup leaks).Execution),
      DecodedExecution setup leaks profile property execution →
      ∀ final ∈ ((application setup leaks).runRounds scheduler players more execution).support,
        DecodedExecution setup leaks profile property final := by
  intro more
  induction more with
  | zero =>
      intro execution holds final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact holds
  | succ more ih =>
      intro execution holds final reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact ih middle (holds.round closed moved) final rest

omit [IExpr.ResultTypes L] in
/-- Rounds continue a run from initialization. -/
theorem mem_roundsFrom_of_runRounds {app : ReactiveApplication Player} {initial : PMF app.State}
    {scheduler : app.Scheduler} {players : Player → app.Policy} {count more : Nat}
    {execution final : app.Execution}
    (supported : execution ∈ (app.roundsFrom initial scheduler players count).support)
    (reached : final ∈ (app.runRounds scheduler players more execution).support) :
    final ∈ (app.roundsFrom initial scheduler players (count + more)).support := by
  unfold ReactiveApplication.roundsFrom at supported ⊢
  obtain ⟨state, stateMem, prior⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨state, stateMem, ?_⟩
  rw [ReactiveApplication.runRounds_add]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨execution, prior, reached⟩

/-- **Decoded debts reach the readout.** Under any players and a scheduler that
completes play, from an execution reached within the horizon whose decoding
leaves `who` owing a failed reveal, every execution the rounds reach at the
horizon reads out a terminal store recording a failed reveal of `who`. -/
theorem runRounds_owesFailure_failedReveals {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (players : Player → (application setup leaks).Policy) {count : Nat} (within : count ≤ horizon)
    {execution : (application setup leaks).Execution}
    (supported : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) (who : Player)
    (owed : DecodedExecution setup leaks profile (ProtocolState.OwesFailure who setup.program)
      execution) :
    ∀ final ∈ ((application setup leaks).runRounds scheduler players (horizon - count)
        execution).support,
      ∃ terminal, sourceReadout setup leaks ((application setup leaks).finished final) =
          some terminal ∧
        1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal) := by
  intro final reached
  obtain ⟨rank, ⟨residual⟩, decoded⟩ := DecodedExecution.runRounds (owesFailure_stepClosed who)
    scheduler players _ execution owed final reached
  have atHorizon := mem_roundsFrom_of_runRounds (app := application setup leaks) supported
    reached
  rw [show count + (horizon - count) = horizon by omega] at atHorizon
  obtain ⟨trace⟩ := (application setup leaks).raw_trace_roundsFrom (initialLaw setup) horizon
    scheduler players horizon le_rfl final atHorizon
  rw [Nat.sub_self] at trace
  have terminalCut := complete ⟨0, none, final⟩ trace ⟨rfl, rfl⟩
  have full := isPrefix_eventCount_of_terminal residual.checkpoint.ordered terminalCut
  subst full
  have read := sourceServicePrefix?_terminal_readout setup final.application.config
  obtain ⟨point, decodedEq⟩ :
      ∃ point, sourceServicePrefix? setup (eventCount setup.program)
        final.application.config = some point := ⟨_, residual.decode⟩
  have pointOwed := decoded point decodedEq
  rw [decodedEq] at read
  obtain ⟨terminal, terminalRead⟩ :=
    ProtocolState.exists_readout_of_terminal setup.program point
      (decodeSourcePrefix?_terminal setup.program _ _ _ _ _ _ point decodedEq)
  refine ⟨terminal, ?_, ProtocolState.failedReveals_pos_of_owesFailure who setup.program point
    pointOwed terminalRead⟩
  rw [ReactiveApplication.finished, sourceReadout_eq_decode, ← read]
  exact terminalRead

end Debts

section Clients

variable (setup leaks) in
/-- **The first-turn clients of the intended effective opening.** At its first
turn at an owned event, an owner makes the compiled decision of the effective
opening of the intended profile, if a fresh call still fits the deadline and
its recall has not submitted for the event; otherwise it is silent. -/
abbrev openingClients (bound : (graph setup).EventId → Nat) (turns : Nat)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    Player → (application setup leaks).Policy :=
  serviceTurnPolicy setup .sequential (rankDeadline setup .sequential) leaks bound turns
    (firstTurnTiming setup turns .sequential) (setup.intendedOpeningProfile intended)

/-- **The first-turn clients have the intended law.** For a well-formed setup,
under the asynchronous contract with timely delays, the first-turn clients of
the intended effective opening read out the intended law of typed readouts. -/
theorem openingClients_readout_law [Fintype Player] (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    ((application setup leaks).roundsFrom (initialLaw setup) scheduler
        (openingClients setup leaks bound turns intended) horizon).map
        (fun execution => sourceReadout setup leaks
          ((application setup leaks).finished execution)) =
      (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => setup.protocolReadout final.state) := by
  rw [setup.intendedOpeningProfile_run wellFormed intended]
  exact openingFirstTurn_readout_law setup leaks
    (serviceGraph_revealRelaxedOrdered setup .sequential) contract timely turns
    (setup.intendedOpeningProfile intended)
    (setup.intendedOpeningProfile_opensEffectively intended)

/-- **The first-turn clients stay in the intended game.** For a well-formed
setup, under the asynchronous contract with timely delays, every execution the
first-turn clients of the intended effective opening reach within the horizon
decodes to a point of the intended game. -/
theorem openingClients_intended [Finite Player] (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (profile : BehavioralProfile setup.program) :
    ∀ count, count ≤ horizon →
      ∀ execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
          (openingClients setup leaks bound turns intended) count).support,
        DecodedExecution setup leaks profile (ProtocolState.Intended setup.program)
          execution := by
  have := Fintype.ofFinite Player
  let app := application setup leaks
  let players := openingClients setup leaks bound turns intended
  intro count
  induction count with
  | zero =>
      intro _ execution supported
      obtain ⟨state, stateMem, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      cases (PMF.mem_support_pure_iff _ _).mp reached
      obtain ⟨initial, initialMem, rfl⟩ := PMF.support_map .. ▸ stateMem
      let residual := SourceResidual.initial setup profile initial
      refine ⟨0, ⟨residual⟩, fun point decoded => ?_⟩
      change sourceServicePrefix? setup 0 (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs initial)).config = some point at decoded
      rw [residual.decode, Option.some.injEq] at decoded
      subst decoded
      exact ProtocolState.intended_entry setup.program _
        (setup.initialConfig_intended wellFormed initialMem)
        (wellFormed.guardsSatisfiable initial initialMem)
  | succ count ih =>
      intro within execution supported
      rw [ReactiveApplication.roundsFrom_succ] at supported
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨rank, ⟨residual⟩, decoded⟩ := ih (by omega) prior priorMem
      have step := round_configStep setup leaks scheduler players prior execution moved
      rcases step with same | ⟨event, ready, action, member⟩
      · refine ⟨rank, ⟨same ▸ residual⟩, ?_⟩
        rw [same]
        exact decoded
      · obtain ⟨next, reachedPoint⟩ := residual.step event ready action _ member
        refine ⟨rank + 1, ⟨next⟩, fun point pointDecoded => ?_⟩
        rw [next.decode, Option.some.injEq] at pointDecoded
        subst pointDecoded
        rcases ProtocolState.intended_or_owesFailure_step setup.program _ _ _
            (decoded _ residual.decode) reachedPoint with kept | ⟨who, owed⟩
        · exact kept
        · exfalso
          have owing : DecodedExecution setup leaks profile
              (ProtocolState.OwesFailure who setup.program) execution :=
            ⟨rank + 1, ⟨next⟩, fun point pointDecoded => by
              rw [next.decode, Option.some.injEq] at pointDecoded
              subst pointDecoded
              exact owed⟩
          have current : execution ∈ (app.roundsFrom (initialLaw setup) scheduler players
              (count + 1)).support := by
            rw [ReactiveApplication.roundsFrom_succ]
            exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨prior, priorMem, moved⟩
          obtain ⟨final, finalMem⟩ :=
            (app.runRounds scheduler players (horizon - (count + 1)) execution).support_nonempty
          obtain ⟨terminal, read, failed⟩ := runRounds_owesFailure_failedReveals
            contract.completes players within current who owing final finalMem
          have atHorizon := mem_roundsFrom_of_runRounds (app := app) current finalMem
          rw [show count + 1 + (horizon - (count + 1)) = horizon by omega] at atHorizon
          have inLaw : some terminal ∈ ((app.roundsFrom (initialLaw setup) scheduler players
              horizon).map (fun execution => sourceReadout setup leaks
                (app.finished execution))).support :=
            (PMF.mem_support_map_iff _ _ _).mpr ⟨final, atHorizon, read⟩
          rw [openingClients_readout_law wellFormed contract timely turns intended] at inLaw
          obtain ⟨history, _, intendedRead⟩ := (PMF.mem_support_map_iff _ _ _).mp inLaw
          have zero := setup.failedReveals_eq_zero_of_intendedState
            (setup.intendedState_trace wellFormed history.trace) who intendedRead
          omega

end Clients

end Vegas
