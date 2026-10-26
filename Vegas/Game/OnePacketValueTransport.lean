/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCommitmentCompletion

/-! # Regular histories owe nothing

At a forced site, a regular history along which the owner's own completions are
intended decodes to a point at which no player owes a failure
(`Vegas.not_owesFailure_of_regular`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

variable {setup runtime leaks bounds horizon scheduler} in
omit [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Regular histories owe nothing.** For a well-formed setup, at a forced
decision site of who, a regular history along which who's own completions decode
to intended actions decodes to a point at which no player owes a failure. -/
theorem not_owesFailure_of_regular (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment) {who : Player}
    {site : (onePacketN).InformationSite who} {past : List (application setup runtime
      leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup) horizon
      scheduler who site.1)
    (history : (onePacketN).InformationHistory who site.1)
    (regular : RegularTrace setup runtime leaks bounds horizon scheduler assessment who
      history.1.trace)
    (ownIntended : OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon :=
      horizon)
      (scheduler := scheduler) who history.1.trace) :
    ∀ point, nativeDecodedState setup runtime leaks history.1.state = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
  intro point decodedState player
  have forcedState := forcedState_of_regular (runtime := runtime) wellFormed assessment atSite
    forced history regular
    ownIntended
  cases state : history.1.state with
  | none =>
      rw [state] at decodedState
      cases decodedState
  | some control =>
      rw [state] at forcedState decodedState
      have record := publicRecord_of_forced (runtime := runtime) who history.1.trace control state
        forcedState
      obtain ⟨found, foundDecoded, intendedFound⟩ := intended_of_regular (runtime := runtime)
        wellFormed assessment who
        history.1.trace control state record regular ownIntended
      change decodedPoint setup control.execution.application.config = some point at decodedState
      rw [foundDecoded, Option.some.injEq] at decodedState
      subst decodedState
      exact ProtocolState.Intended.not_owesFailure player setup.program found intendedFound

end Vegas
