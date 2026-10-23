/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSpec
import Vegas.Game.SourceServiceTimedContinuation
import Interaction.ReactiveStopping
import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheory.Protocol.TremblingPlans

/-! # Decision phases and timed approximants in the full-source service

Every actual decision has a `DecisionPhase`: its event, roster slot and the
instructions left in that event's phase. A fully mixed timed approximant is a
source profile compiled with a common timing law, its admissibility, and a
fully mixed native assessment whose strategy is that compilation
(`Vegas.TimedApproximant`); its readout after one current response is the
complete typed source terminal law (`Vegas.TimedApproximant.responseReadout`).
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
    (execution : (application setup leaks).Execution) where
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
  {execution : (application setup leaks).Execution}
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

theorem tail_no_wire : ServiceInstruction.wire ∉ phase.tail := by
  simp [tail, rosterPhaseEnding_no_wire]

/-- The service plan after the current event's phase. -/
def later : List (ServiceInstruction (graph setup)) :=
  rosterPlanSuffix setup rosters (phase.event.val + 1)

theorem roster_split : rosters phase.event =
    (rosters phase.event).take phase.slot ++ who :: phase.visits := by
  have inside := (List.getElem?_eq_some_iff.mp phase.selected).1
  have drop := List.drop_eq_getElem_cons inside
  rw [(List.getElem?_eq_some_iff.mp phase.selected).2] at drop
  simpa only [visits, drop] using ((rosters phase.event).take_append_drop phase.slot).symm

theorem prefix_split :
    rosterPlanPrefix setup rosters (phase.event.val + 1) =
      phase.before ++ .player who :: phase.tail := by
  rw [rosterPlanPrefix_succ, rosterBlock_eq_ending]
  conv_lhs => rw [phase.roster_split]
  simp only [before, tail, List.map_append, List.map_cons, List.append_assoc,
    List.cons_append]

theorem plan_split :
    rosterPlan setup rosters = (phase.before ++ [.player who]) ++ (phase.tail ++ phase.later) := by
  rw [← rosterPlanPrefix_append_suffix setup rosters (phase.event.val + 1), phase.prefix_split]
  simp only [later, List.append_assoc, List.cons_append, List.nil_append]

theorem position_before :
    execution.environmentRecall.length = phase.before.length + 1 := by
  have inside := (List.getElem?_eq_some_iff.mp phase.selected).1
  simp only [before, List.length_append, List.length_map,
    List.length_take_of_le inside.le]
  exact phase.position

end DecisionPhase

variable [Fintype Player]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- The native information of the acting player at an actual decision is its
recall and current view. -/
theorem infoOf_decision {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (history : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).History)
    (current : history.state = some ⟨remaining, some who, execution⟩) :
    service.model.infoOf who history.trace =
      some (execution.recall who,
        execution.observe (application service.setup service.leaks) who) := by
  change (service.menu.signals (initialLaw service.setup) service.planLength
    service.scheduler).infoOf who history.trace = _
  rw [service.menu.info, current]
  simp only [ReactiveApplication.observe, ↓reduceIte]

/-- Every choice available at an actual decision is a legal current response. -/
theorem choice_allowed {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (history : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).History)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    {info : service.model.InfoState who}
    (observed : service.model.infoOf who history.trace = info)
    (choice : service.model.Choice who info) :
    choice.1.getD ⟨none⟩ ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who) := by
  subst info
  have allowed := Eq.mp (congrArg (fun input => choice.1 ∈ service.model.menu who input)
    (service.infoOf_decision history current)) choice.2
  obtain ⟨response, allowed, same⟩ := allowed
  simpa only [same, Option.getD_some] using allowed

end SourceServiceSpec

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

variable {service : SourceServiceSpec Player L}

end TimedApproximant

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

/-- The native timed compilation of the approximant's source profile. -/
abbrev players : Player → (application service.setup service.leaks).Policy :=
  sourceServiceTimedPolicy service.setup service.leaks service.rosters approx.timing
    approx.profile

/-- The complete typed source terminal law after one current response: the
prescribed players and the service's scheduler run to the horizon. -/
def responseReadout {who : Player}
    {execution : (application service.setup service.leaks).Execution}
    (_phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action) :
    PMF (Option (State L service.setup.program.terminalCtx)) :=
  ((application service.setup service.leaks).runToHorizon service.scheduler approx.players
    service.planLength
    (execution.respond (application service.setup service.leaks) who response)).map
      (fun final => sourceReadout service.setup service.leaks
        ((application service.setup service.leaks).finished final))

/-- The source continuation from the event boundary after a phase. -/
def boundaryContinuation (count : Nat) (config : (graph service.setup).Config) :
    PMF (Option (State L service.setup.program.terminalCtx)) :=
  (service.setup.continuationLaw approx.profile
    (sourceServicePrefix? service.setup count config)).map some

end TimedApproximant

end Vegas
