/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketReplayExists
import Vegas.Game.SourceDebtObservation
import Vegas.Game.OnePacketDisclosureResolves

/-! # Own completions are intended where the player owes nothing

A player's actual decoded prefixes are intended for it whenever the endpoint
owes it no failure. An owned primitive completion between such points has an
intended source action
(`Vegas.SourceProgram.ProtocolState.intendedAvailable_of_decode_intendedFor`).
Every decoded point is intended for the player or has the player owing
(`Vegas.decodedState_intendedFor_or_owes`), and debts persist. So along every
native history of the one-packet game whose decoded point has `who` owing
nothing, `who`'s own completions decode to intended actions
(`Vegas.ownCompletionsIntended_of_notOwes`), with no regularity of the history.
At a decision input where `who` owes nothing at any history, this holds at
every history (`Vegas.ownCompletionsIntended_of_siteNotOwes`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- Owing no source failure reaches back along a native transition, including
its complete automatic-completion path. -/
theorem notOwes_of_transition {who : Player} {before after : (application setup runtime
  leaks).Control}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some before))
    (joint : Player → Option (application setup runtime leaks).Action)
    (realized : some after ∈ ((application setup runtime leaks).transition (initialLaw setup)
      horizon scheduler (some before) joint).support)
    (notOwed : ∀ point, decodedPoint setup after.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point) :
    ∀ point, decodedPoint setup before.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point := by
  intro point decoded owes
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime)
    (failureProfile setup.program) (bounds.onePacketMenu runtime leaks) horizon scheduler
    prior before rfl
  have holds : DecodedState setup runtime leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure who setup.program) (some before) := by
    refine ⟨rank, ⟨residual⟩, ?_⟩
    intro found read
    have foundEq : decodedPoint setup before.execution.application.config = some found :=
      (decodedPoint_eq residual).trans (residual.decode.symm.trans read)
    cases Option.some.inj (foundEq.symm.trans decoded)
    exact owes
  obtain ⟨_, ⟨next⟩, owed⟩ := decodedHolds_transition (owesFailure_stepClosed who)
    (initialLaw setup) horizon scheduler (some before) (some after) joint holds realized
  exact notOwed _ (decodedPoint_eq next) (owed _ next.decode)

/-- If the endpoint owes no failure, every actual initialized prefix is intended
for the player. No restriction is imposed on another player's response policy. -/
theorem ownCompletionsIntended_of_notOwes (wellFormed : setup.WellFormed) (who : Player) :
    ∀ {state} (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
      (control : (application setup runtime leaks).Control), state = some control →
      (∀ point, decodedPoint setup control.execution.application.config = some point →
        ¬ ProtocolState.OwesFailure who setup.program point) →
      OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler) who trace
  | _, .start, _, current, _ => by cases current
  | _, .extend (source := before) prior joint legal realized, control, current, notOwed => by
      have recursive := fun previous same notOwedPrevious =>
        ownCompletionsIntended_of_notOwes wellFormed who prior previous same notOwedPrevious
      subst current
      have here : ∀ found : (application setup runtime leaks).Control, some control = some found →
          ∀ point, decodedPoint setup found.execution.application.config = some point →
            ProtocolState.IntendedFor who setup.program point := by
        intro found same point decoded
        cases Option.some.inj same
        obtain ⟨_, ⟨residual⟩, holds⟩ := decodedState_intendedFor_or_owes (runtime := runtime)
          wellFormed who (failureProfile setup.program) (bounds.onePacketMenu runtime leaks)
          horizon scheduler (prior.extend joint legal realized) control rfl
        have residualPoint := decodedPoint_eq residual
        have samePoint := Option.some.inj (residualPoint.symm.trans decoded)
        rcases holds _ residual.decode with intended | owes
        · exact samePoint ▸ intended
        · exact (notOwed _ residualPoint owes).elim
      cases before with
      | none =>
          obtain rfl := trace_eq_start_of_none (runtime := runtime) prior
          exact ⟨trivial, here⟩
      | some previous =>
          exact ⟨recursive previous rfl
            (notOwes_of_transition prior joint realized notOwed), here⟩

/-- **Own completions are intended at sites where the player owes nothing.** For
a well-formed setup, at a decision input of `who` at whose histories `who` owes
no failure at the decoded point, `who`'s own completions along every history of
the input decode to intended actions. -/
theorem ownCompletionsIntended_of_siteNotOwes (wellFormed : setup.WellFormed) {who : Player}
    {info : (onePacketInformation setup runtime leaks bounds horizon scheduler).InfoState who}
    (notOwed : ∀ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who info,
      ∀ point, nativeDecodedState setup runtime leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point)
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      info) :
    OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon) (scheduler
      := scheduler) who
      history.1.trace := by
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  cases state with
  | none =>
      obtain rfl := trace_eq_start_of_none (runtime := runtime) trace
      trivial
  | some control =>
      exact ownCompletionsIntended_of_notOwes (runtime := runtime) wellFormed who trace control rfl
        (notOwed ⟨⟨some control, trace⟩, seen⟩)

end Vegas
