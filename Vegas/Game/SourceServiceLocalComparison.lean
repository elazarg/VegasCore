/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceSpec
import Vegas.Game.SourceServiceTimedContinuation
import Interaction.ReactiveStopping
import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheory.Protocol.TremblingPlans
import Vegas.Game.SourceServiceTimedPolicy

/-! # Decision phases and timed approximants in the full-source service

Every actual decision has a `DecisionPhase`: its event, roster slot and the
instructions left in that event's phase. A fully mixed timed approximant is a
source profile compiled with a common timing law, its admissibility, and a
fully mixed native assessment whose strategy is that compilation
(`Vegas.TimedApproximant`); the compiled native policies are
`Vegas.TimedApproximant.players`.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The position of an actual activation of `who`: its event, its slot in that
event's roster, and the event's readiness. -/
structure DecisionPhase (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (execution : (application setup (Vegas.runtime setup) leaks).Execution) where
  event : (graph setup).EventId
  slot : Nat
  selected : (rosters event)[slot]? = some who
  position : execution.environmentRecall.length =
    (rosterPlanPrefix setup rosters event.val).length + slot + 1
  ready : execution.application.config.cut.Ready event

namespace DecisionPhase

variable {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {rosters : (graph setup).EventId → List Player} {who : Player}
  {execution : (application setup (Vegas.runtime setup) leaks).Execution}
  (phase : DecisionPhase setup leaks rosters who execution)

/-- The phase's event is the only ready event. -/
theorem sole : execution.application.publicView.SoleReady phase.event :=
  soleReady_of_ready setup execution.application phase.ready

/-- The roster visits of the phase that follow the current one. -/
def visits : List Player := (rosters phase.event).drop (phase.slot + 1)

/-- The service plan up to the current activation. -/
def before : List (ServiceInstruction (graph setup)) :=
  rosterPlanPrefix setup rosters phase.event.val ++
    ((rosters phase.event).take phase.slot).map ServiceInstruction.player

/-- The instructions left in the current event's phase. -/
def tail : List (ServiceInstruction (graph setup)) :=
  phase.visits.map ServiceInstruction.player ++ rosterPhaseEnding setup phase.event

/-- The service plan after the current event's phase. -/
def later : List (ServiceInstruction (graph setup)) :=
  rosterPlanSuffix setup rosters (phase.event.val + 1)

end DecisionPhase

variable [Fintype Player]

/-- One fully mixed timed approximant: a source profile compiled with a common
timing law, its admissibility, and a fully mixed native assessment whose
strategy is exactly that compilation. -/
structure TimedApproximant (service : SourceServiceSpec Player L) where
  timing : TimingLaw service.setup service.rosters
  timingFull : ∀ event who owned, FullSupport (timing event who owned)
  profile : BehavioralProfile service.setup.program
  admitted : ∀ who, (profile who).Admitted service.setup.program
    (CommitmentInterface.values service.setup.program)
  covered : ∀ who, service.menu.Admissible (initialLaw service.setup) service.planLength
    service.scheduler who
      (sourceServiceTimedPolicy service.setup service.leaks service.rosters timing profile who)
  effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
    (Revelations.initial service.setup.context)
  supports : ∀ who, (profile who).SupportsEffectiveChoices service.setup.program
    (CommitmentInterface.values service.setup.program) []
      (Revelations.initial service.setup.context)
  assessment : service.model.BehavioralAssessment
  strategy : assessment.strategy = fun who =>
    service.menu.restrictPolicy (initialLaw service.setup) service.planLength service.scheduler
      who (sourceServiceTimedPolicy service.setup service.leaks service.rosters timing profile who)
  mixed : assessment.IsFullyMixed

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

/-- The native timed compilation of the approximant's source profile. -/
abbrev players : Player → (application service.setup (runtime service.setup)
  service.leaks).Policy :=
  sourceServiceTimedPolicy service.setup service.leaks service.rosters approx.timing
    approx.profile

end TimedApproximant

end Vegas
