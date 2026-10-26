/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceFailureReadout
import Vegas.Game.IntendedOpeningContinuation
import Vegas.Game.OnePacketFirstActivationCompletion

/-! # Honest continuation laws exclude latent source failures -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- An honest source continuation law rules out latent debt at every reached
native history, without a global native completion assumption. -/
theorem honest_reached_intended_of_readout_law
    (bounds : MessageBounds (graph setup)) (wellFormed : setup.WellFormed)
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (point : ProtocolState setup.program)
    (static : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) point)
    (intended : ProtocolState.Intended setup.program point)
    (law : (InformationModel.runBehavioralTerminalFrom
      (onePacketModel (runtime := runtime) setup leaks bounds (initialLaw setup) horizon
        scheduler) certificate
        (honestProfile (runtime := runtime) setup leaks bounds (initialLaw setup) horizon
          scheduler assessment)
        start).map (fun final => sourceReadout setup runtime leaks final.state) =
          (setup.continuationLaw (setup.intendedOpeningProfile assessment.strategy)
            (some point)).map some)
    (fuel : Nat)
    (history : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (reached : history ∈ ((onePacketModel (runtime := runtime) setup leaks bounds (initialLaw
      setup) horizon
      scheduler).runBehavioralFrom
        (honestProfile (runtime := runtime) setup leaks bounds (initialLaw setup) horizon
          scheduler assessment)
        fuel start).support)
    (control : (application setup runtime leaks).Control) (current : history.state = some control) :
    ∃ decoded, decodedPoint setup control.execution.application.config = some decoded ∧
      ProtocolState.Intended setup.program decoded := by
  let menu := bounds.onePacketMenu runtime leaks
  let model := onePacketModel (runtime := runtime) setup leaks bounds (initialLaw setup)
    horizon scheduler
  let honest := honestProfile (runtime := runtime) setup leaks bounds (initialLaw setup)
    horizon scheduler assessment
  let opening := setup.intendedOpeningProfile assessment.strategy
  obtain ⟨rank, ⟨residual⟩, holds⟩ := decodedState_intended_or_owes (runtime := runtime)
    wellFormed opening menu
    horizon scheduler history.trace control current
  have noDebt : ∀ player, ¬ ProtocolState.OwesFailure player setup.program
      (residual.lift (ProtocolState.entry residual.program residual.source)) := by
    intro player debt
    have owing : DecodedState setup runtime leaks opening (ProtocolState.OwesFailure player
      setup.program)
        history.state := by
      rw [current]
      refine ⟨rank, ⟨residual⟩, fun decodedPoint decoded => ?_⟩
      rw [residual.decode, Option.some.injEq] at decoded
      exact decoded ▸ debt
    obtain ⟨final, supported⟩ :=
      (model.runBehavioralTerminalFrom certificate honest history).support_nonempty
    have inLaw : final ∈ (model.runBehavioralTerminalFrom certificate honest start).support := by
      rw [model.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom certificate honest fuel start]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨history, reached, supported⟩
    have readInLaw : sourceReadout setup runtime leaks final.state ∈
        ((setup.continuationLaw opening (some point)).map some).support := by
      rw [← law]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, inLaw, rfl⟩
    obtain ⟨terminal, sourceMem, read⟩ := (PMF.mem_support_map_iff _ _ _).mp readInLaw
    have reachedOwing := model.runBehavioralTerminalFrom_support_closed certificate honest
      (DecodedState setup runtime leaks opening (ProtocolState.OwesFailure player setup.program))
      (fun before joint _ after holds member =>
        decodedHolds_transition (runtime := runtime) (owesFailure_stepClosed player)
          (initialLaw setup) horizon
          scheduler before after joint holds member)
      history owing final supported
    have failed := decoded_owesFailure_failedReveals_of_readout player final.state reachedOwing
      terminal read.symm
    have zero := setup.intendedOpening_continuation_failedReveals assessment.strategy _ point
      le_rfl static intended terminal sourceMem player
    omega
  refine ⟨_, (decodedPoint_eq_of_isPrefix residual.checkpoint.ordered).trans residual.decode, ?_⟩
  rcases holds _ residual.decode with preserved | ⟨player, debt⟩
  · exact preserved
  · exact (noDebt player debt).elim

end Vegas
