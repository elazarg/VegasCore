/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.IntendedPreservation
import Vegas.Game.PhaseExclusionPayoff
import Vegas.Game.PhaseOnePacketExtension
import Vegas.Pending.ReservedEpochResources
import Interaction.CompletePendingObservation

/-! # Concurrent raw sequential-equilibrium preservation contract

The implementation fixes one concurrent runtime and one unconditional tape prior
before an intended source assessment is selected. Validity separates operational
conditions, bounded exclusion payoffs and funded count enforcement. All three
use the existing runtime and audit primitives.

The conclusion preserves one joint observation: original source inputs, the
complete typed terminal state, its public result and the realized net payoff
vector. The input reader is fixed by the source program, not supplied by a caller.
This module states the preservation proposition; it does not prove it.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- One actual reserved-service implementation of the compiled concurrent graph.
The tape is sampled once for the whole execution; its prior is independent of
the source input draw and does not refresh at logical block boundaries. -/
structure ReservedConcurrentImplementation (setup : Setup (Player := Player) (L := L)) where
  runtime : EventGraphRuntime (serviceGraph setup .concurrent)
  leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket (serviceGraph setup .concurrent))
  bounds : MessageBounds (serviceGraph setup .concurrent)
  plan : RuntimePhasePlan (serviceGraph setup .concurrent)
  tapeLength : Nat
  prior : PMF (ReservedEpoch.Tape Player tapeLength)
  activationGap : Nat
  processingGap : Nat

/-- Source utility bounds and the permanent-exclusion payoff. These data are
fixed before choosing which intended source equilibrium to preserve. -/
structure ConcurrentPayoffs (setup : Setup (Player := Player) (L := L)) where
  utility : State L setup.program.terminalCtx → Player → ℝ
  excludedPayoff : Player → ℝ
  lowerUtility : Player → ℝ
  upperUtility : Player → ℝ

/-- The authentic count-evidence service and the amounts used in its terminal
settlement. Collection may be correlated across evidence and players. -/
structure ConcurrentCountAudit (setup : Setup (Player := Player) (L := L)) where
  service : EvidenceReportService (PhaseCount.Evidence (serviceGraph setup .concurrent))
  observationRate : Player → ℝ
  deliveryRate : Player → ℝ
  deposit : Player → ℝ

/-- The complete observation whose JOINT law must be preserved. The four fields
name the four outcome coordinates, including the entire payoff vector. -/
structure ConcurrentTerminalObservation (setup : Setup (Player := Player) (L := L)) where
  initialInputs : Option (State L setup.context)
  terminalState : Option (State L setup.program.terminalCtx)
  publicResult : Option (PublicOutcome setup.program)
  netPayoffs : Player → ℝ

namespace ConcurrentTerminalObservation

/-- Both games use this same fixed reader; no alternative input decoder is a
parameter of the preservation proposition. -/
def read (setup : Setup (Player := Player) (L := L))
    (terminal : Option (State L setup.program.terminalCtx)) (netPayoffs : Player → ℝ) :
    ConcurrentTerminalObservation setup where
  initialInputs := terminal.map (initialState setup.program)
  terminalState := terminal
  publicResult := terminal.map (publicOutcome setup.program)
  netPayoffs := netPayoffs

end ConcurrentTerminalObservation

namespace ConcurrentPayoffs

variable {setup : Setup (Player := Player) (L := L)} (payoffs : ConcurrentPayoffs setup)

/-- Source terminal bounds and the global exclusion floor. The audit spread
also accounts for the default-zero readout. -/
structure Bounded : Prop where
  lower_le : ∀ terminal who, payoffs.lowerUtility who ≤ payoffs.utility terminal who
  le_upper : ∀ terminal who, payoffs.utility terminal who ≤ payoffs.upperUtility who
  excluded_nonpositive : ∀ who, payoffs.excludedPayoff who ≤ 0
  excluded_le : ∀ terminal who, payoffs.excludedPayoff who ≤ payoffs.utility terminal who

/-- The actual exclusion-base spread used by terminal count enforcement. -/
def auditSpread (who : Player) : ℝ :=
  max 0 (max (payoffs.excludedPayoff who) (payoffs.upperUtility who)) -
    min 0 (min (payoffs.excludedPayoff who) (payoffs.lowerUtility who))

/-- The intended source assessment uses the original terminal-state utility. -/
def SourceEquilibrium (source : setup.intendedModel.BehavioralAssessment) : Prop :=
  source.IsSequentialEquilibrium setup.intended_decision_antichain
    setup.intended_bounded.wellFoundedHistories
    (fun who final => (setup.protocolReadout final.state).elim 0
      (fun terminal => payoffs.utility terminal who))

/-- The original initialized source law, with all four coordinates retained. -/
def jointLaw (source : setup.intendedModel.BehavioralAssessment) :
    PMF (ConcurrentTerminalObservation setup) :=
  (setup.intendedModel.runBehavioralTerminalFrom
    setup.intended_bounded.wellFoundedHistories source.strategy
    setup.intendedProtocol.initHistory).map fun final =>
      let terminal := setup.protocolReadout final.state
      ConcurrentTerminalObservation.read setup terminal
        (fun who => terminal.elim 0 (fun state => payoffs.utility state who))

end ConcurrentPayoffs

namespace ConcurrentCountAudit

variable {setup : Setup (Player := Player) (L := L)} (audit : ConcurrentCountAudit setup)

/-- Existing evidence coverage and the exact deposit-spread inequality fund
the terminal audit. No independence of observation and delivery is imposed. -/
structure Funded (payoffs : ConcurrentPayoffs setup) : Prop where
  delivery_nonnegative : ∀ who, 0 ≤ audit.deliveryRate who
  coverage : PhaseCount.EvidenceCoverage audit.service audit.observationRate audit.deliveryRate
  deposit_nonnegative : ∀ who, 0 ≤ audit.deposit who
  sufficient : ∀ who, payoffs.auditSpread who ≤
    audit.observationRate who * audit.deliveryRate who * audit.deposit who

end ConcurrentCountAudit

namespace ReservedConcurrentImplementation

variable {setup : Setup (Player := Player) (L := L)}
  (implementation : ReservedConcurrentImplementation setup)

abbrev application := phaseApplication implementation.runtime implementation.leaks

def initial := setup.initialLaw.map fun theta =>
  PhaseRuntimeState.initial implementation.plan (encodeInputs theta)

abbrev horizon := ReservedEpoch.executionHorizon implementation.runtime

def scheduler := (ReservedEpoch.implementation implementation.runtime implementation.leaks
  (ReservedEpoch.packetCapacity implementation.runtime) implementation.prior).scheduler

abbrev rawMenu := PhaseCount.rawMenu implementation.runtime implementation.leaks
  implementation.bounds

abbrev model := implementation.rawMenu.information implementation.initial
  implementation.horizon implementation.scheduler

/-- The original source finiteness and well-formedness conditions, complete
pending observation and the concrete reserved-service resource conditions. -/
structure Operational : Prop where
  finiteInitial : setup.FiniteInitialLaw
  finiteBindings : setup.program.FiniteBindingTypes
  wellFormed : setup.WellFormed
  completePending : implementation.leaks = MessageNetwork.completePendingObservation
  outputValues : implementation.bounds.CoversOutputValues
  maximalPhases : implementation.plan.phases.IsChain (fun first last =>
    first.kind ≠ last.kind ∨ first.kind = .sample)
  boundedGaps : ∀ tape ∈ implementation.prior.support,
    tape.BoundedGaps (ReservedEpoch.completionCycles implementation.runtime)
      implementation.activationGap implementation.processingGap
  timely : implementation.runtime.AsyncTimely
    (fun _ => implementation.activationGap + 1) (fun _ => implementation.processingGap + 1)
  candidateReserve : implementation.horizon ≤ implementation.bounds.candidateCount

/-- Validity is precisely operational validity, bounded payoffs and a funded
authentic audit. It introduces no conditional scheduler or likelihood premise. -/
structure Valid (payoffData : ConcurrentPayoffs setup)
    (auditData : ConcurrentCountAudit setup) : Prop where
  operational : implementation.Operational
  payoffs : payoffData.Bounded
  audit : auditData.Funded payoffData

def terminalLaw (target : implementation.model.BehavioralAssessment) :
    PMF (implementation.rawMenu.protocol implementation.initial implementation.horizon
      implementation.scheduler).History :=
  implementation.model.runBehavioralTerminalFrom
    (implementation.rawMenu.bounded implementation.initial implementation.horizon
      implementation.scheduler).wellFoundedHistories target.strategy
    (implementation.rawMenu.protocol implementation.initial implementation.horizon
      implementation.scheduler).initHistory

def base (payoffs : ConcurrentPayoffs setup) :=
  phaseExclusionBase setup .concurrent implementation.runtime implementation.leaks
    payoffs.utility payoffs.excludedPayoff

def audit (countAudit : ConcurrentCountAudit setup) :=
  PhaseCount.audit implementation.runtime implementation.leaks countAudit.service.sample

def auditedUtility (payoffs : ConcurrentPayoffs setup) (countAudit : ConcurrentCountAudit setup) :=
  TerminalAudit.utility (implementation.base payoffs) implementation.application.stateTraffic
    (implementation.audit countAudit) countAudit.deposit

/-- The native law includes the audit's actual randomized settlement, rather
than replacing its whole realized payoff vector by expected utilities. -/
def jointLaw (payoffs : ConcurrentPayoffs setup) (countAudit : ConcurrentCountAudit setup)
    (target : implementation.model.BehavioralAssessment) :
    PMF (ConcurrentTerminalObservation setup) :=
  (implementation.terminalLaw target).bind fun final =>
    (TerminalAudit.settlement (implementation.base payoffs) implementation.application.stateTraffic
      (implementation.audit countAudit) countAudit.deposit final.state).map fun netPayoffs =>
        ConcurrentTerminalObservation.read setup
          (phaseSourceReadout setup .concurrent implementation.runtime implementation.leaks
            final.state) netPayoffs

/-- The actual raw equilibrium, exact joint-law equality and supportwise clean
settlement required for one selected intended source assessment. -/
structure PreservesAssessment (payoffs : ConcurrentPayoffs setup)
    (countAudit : ConcurrentCountAudit setup)
    (source : setup.intendedModel.BehavioralAssessment)
    (target : implementation.model.BehavioralAssessment) : Prop where
  equilibrium : target.IsSequentialEquilibrium
    (implementation.rawMenu.decisionInformationAntichain implementation.initial
      implementation.horizon implementation.scheduler)
    (implementation.rawMenu.bounded implementation.initial implementation.horizon
      implementation.scheduler).wellFoundedHistories
    (fun who final => implementation.auditedUtility payoffs countAudit final.state who)
  jointLaw : payoffs.jointLaw source = implementation.jointLaw payoffs countAudit target
  noExclusions : ∀ final ∈ (implementation.terminalLaw target).support, ∀ who,
    ¬ PhaseExcluded setup .concurrent implementation.runtime implementation.leaks who final.state
  noCharges : ∀ final ∈ (implementation.terminalLaw target).support, ∀ who,
    TerminalAudit.charge implementation.application.stateTraffic
      (implementation.audit countAudit) final.state who = 0

end ReservedConcurrentImplementation

/-- A valid fixed implementation preserves every intended source sequential
equilibrium, including its complete initialized joint law and clean settlement.
This is the target proposition, not a preservation theorem. -/
def ConcurrentRawSequentialPreservation (setup : Setup (Player := Player) (L := L))
    (implementation : ReservedConcurrentImplementation setup)
    (payoffs : ConcurrentPayoffs setup) (audit : ConcurrentCountAudit setup) : Prop :=
  implementation.Valid payoffs audit →
    ∀ source : setup.intendedModel.BehavioralAssessment,
      payoffs.SourceEquilibrium source →
        ∃ target : implementation.model.BehavioralAssessment,
          implementation.PreservesAssessment payoffs audit source target

end Vegas
