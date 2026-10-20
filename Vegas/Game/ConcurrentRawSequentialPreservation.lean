/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.IntendedPreservation
import Vegas.Game.PhaseRawReadoutLaw
import Vegas.Pending.ReservedEpochResources
import Vegas.Source.InitialState
import Interaction.CompletePendingObservation

/-! # Concurrent raw sequential-equilibrium preservation contract

This proposition states the required end-to-end result; it supplies no proof of
preservation. The initial law is the original arbitrary joint setup law.
The fixed initial-state reader recovers immutable source inputs from the typed
terminal store. `PhaseProposalInitializedTerminal` identifies that reader with
the literal original draw in its supported initialized coupling.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

/-- Every selected intended equilibrium has a concurrent raw equilibrium with
the same joint initial inputs, typed and public results, and realized net payoff
vector, and with no permanent exclusion or collected audit charge. Runtime,
service and economic parameters are fixed before selecting the assessment. -/
def ConcurrentRawSequentialPreservation
    {Player : Type} [DecidableEq Player] [Fintype Player]
    {L : IExpr} [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (bounds : MessageBounds (serviceGraph setup .concurrent))
    (plan : RuntimePhasePlan (serviceGraph setup .concurrent))
    {tapeLength : Nat} (prior : PMF (ReservedEpoch.Tape Player tapeLength))
    (activationGap processingGap : Nat)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff lowerUtility upperUtility : Player → ℝ)
    (service : EvidenceReportService (PhaseCount.Evidence (serviceGraph setup .concurrent)))
    (observationRate deliveryRate deposit : Player → ℝ) : Prop :=
  let app := phaseApplication runtime leaks
  let initial := setup.initialLaw.map fun theta =>
    PhaseRuntimeState.initial plan (encodeInputs theta)
  let horizon := ReservedEpoch.executionHorizon runtime
  let scheduler := (ReservedEpoch.implementation runtime leaks
    (ReservedEpoch.packetCapacity runtime) prior).scheduler
  let raw := PhaseCount.rawMenu runtime leaks bounds
  let certificate := (raw.bounded initial horizon scheduler).wellFoundedHistories
  let base := phaseExclusionBase setup .concurrent runtime leaks utility excludedPayoff
  let observe := app.stateTraffic
  let audit := PhaseCount.audit runtime leaks service.sample
  let payoff := TerminalAudit.utility base observe audit deposit
  let settle := TerminalAudit.settlement base observe audit deposit
  setup.FiniteInitialLaw →
  setup.program.FiniteBindingTypes →
  setup.WellFormed →
  leaks = MessageNetwork.completePendingObservation →
  bounds.CoversOutputValues →
  plan.phases.IsChain (fun first last =>
    first.kind ≠ last.kind ∨ first.kind = .sample) →
  (∀ tape ∈ prior.support,
    tape.BoundedGaps (ReservedEpoch.completionCycles runtime) activationGap processingGap) →
  runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1) →
  horizon ≤ bounds.candidateCount →
  (∀ terminal who, lowerUtility who ≤ utility terminal who) →
  (∀ terminal who, utility terminal who ≤ upperUtility who) →
  (∀ who, excludedPayoff who ≤ 0) →
  (∀ terminal who, excludedPayoff who ≤ utility terminal who) →
  (∀ who, 0 ≤ deliveryRate who) →
  PhaseCount.EvidenceCoverage service observationRate deliveryRate →
  (∀ who, 0 ≤ deposit who) →
  (∀ who,
    max 0 (max (excludedPayoff who) (upperUtility who)) -
        min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
      observationRate who * deliveryRate who * deposit who) →
  ∀ source : setup.intendedModel.BehavioralAssessment,
    source.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun terminal => utility terminal who)) →
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain initial horizon scheduler) certificate
        (fun who final => payoff final.state who) ∧
      let nativeLaw := (raw.information initial horizon scheduler).runBehavioralTerminalFrom
        certificate target.strategy (raw.protocol initial horizon scheduler).initHistory
      let sourceLaw := setup.intendedModel.runBehavioralTerminalFrom
        setup.intended_bounded.wellFoundedHistories source.strategy
        setup.intendedProtocol.initHistory
      (sourceLaw.map fun final =>
        let terminal := setup.protocolReadout final.state
        (terminal.map (initialState setup.program), terminal,
          terminal.map (publicOutcome setup.program),
          fun who => terminal.elim 0 (fun state => utility state who))) =
        (nativeLaw.bind fun final => (settle final.state).map fun netPayoffs =>
          let terminal := phaseSourceReadout setup .concurrent runtime leaks final.state
          (terminal.map (initialState setup.program), terminal,
            terminal.map (publicOutcome setup.program), netPayoffs)) ∧
      ∀ final ∈ nativeLaw.support, ∀ who,
        ¬ PhaseExcluded setup .concurrent runtime leaks who final.state ∧
        TerminalAudit.charge observe audit final.state who = 0

end Vegas
