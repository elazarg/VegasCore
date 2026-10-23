/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryHonestContinuation
import Vegas.Game.HonestContinuationIntended

/-! # Honest continuations do not stop at exclusion or latent debt -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

/-- An honest continuation with the intended source law cannot encounter a
public exclusion or hidden own debt, so stopping there leaves its terminal law unchanged. -/
theorem honest_debt_stopped_terminal_law_of_readout_law
    (bounds : MessageBounds (graph setup)) (wellFormed : setup.WellFormed)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (point : ProtocolState setup.program)
    (static : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) point)
    (intended : ProtocolState.Intended setup.program point)
    (law : (InformationModel.runBehavioralTerminalFrom
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler) certificate
        (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment)
        start).map (fun final => sourceReadout setup leaks final.state) =
          (setup.continuationLaw (setup.intendedOpeningProfile assessment.strategy)
            (some point)).map some)
    (who : Player) :
    let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
    let honest := honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment
    let stopped := fun history => ¬ Clear history.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) history.state
    model.runBehavioralUntil certificate honest stopped start =
        model.runBehavioralTerminalFrom certificate honest start ∧
      ∀ final ∈ (model.runBehavioralUntil certificate honest stopped start).support,
        ¬ stopped final := by
  classical
  intro model honest stopped
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let reachable := fun history => ∃ fuel,
    history ∈ (model.runBehavioralFrom honest fuel start).support
  have notStopped : ∀ history, reachable history → ¬ stopped history := by
    rintro history ⟨fuel, reached⟩
    cases current : history.state with
    | none => simp [stopped, current, ReactiveApplication.stateInvariant, DecodedState]
    | some control =>
      obtain ⟨decoded, decodedEq, intendedDecoded⟩ := honest_reached_intended_of_readout_law
        bounds wellFormed assessment certificate start point static intended law fuel history
          reached control current
      have clear : Clear history.state := by
        rw [current]
        exact publicExclusionRecord_of_decodedIntended
          (menu.toRawTrace (initialLaw setup) horizon scheduler (current ▸ history.trace)) decodedEq
          intendedDecoded
      refine fun stop => ?_
      rcases stop with notClear | owed
      · exact notClear clear
      · rw [current] at owed
        obtain ⟨rank, ⟨residual⟩, holds⟩ := owed
        have atRank : sourceServicePrefix? setup rank control.execution.application.config =
            some decoded :=
          (decodedPoint_eq_of_isPrefix residual.checkpoint.ordered).symm.trans decodedEq
        exact ProtocolState.Intended.not_owesFailure who setup.program decoded intendedDecoded
          (holds decoded atRank)
  have reachableAtStop := model.runBehavioralUntil_support_history_closed certificate honest
    stopped reachable (by
      rintro history _ _ ⟨fuel, reached⟩ next member
      refine ⟨fuel + 1, ?_⟩
      rw [model.runBehavioralFrom_add honest fuel 1, PMF.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨history, reached, member⟩)
    start ⟨0, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  refine ⟨?_, fun final member => notStopped final (reachableAtStop final member)⟩
  have terminal : ∀ final ∈ (model.runBehavioralUntil certificate honest stopped start).support,
      (menu.protocol (initialLaw setup) horizon scheduler).terminal final.state := by
    intro final member
    exact (model.mem_support_runBehavioralUntil certificate honest stopped start final
      member).resolve_left (notStopped final (reachableAtStop final member))
  rw [model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate honest stopped]
  change _ = (model.runBehavioralUntil certificate honest stopped start).bind _
  refine (PMF.bind_pure _).symm.trans ?_
  apply bind_congr_on_support
  intro final member
  exact (ExecutionProtocol.randomizedBackwardLaw_of_terminal _ (terminal final member)).symm

end Vegas
