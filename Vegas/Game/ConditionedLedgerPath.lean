module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedLedgerAssessment
public import Vegas.Game.ClientCompiler

@[expose] public section

/-! # Supported outcomes of locally selected raw ledger assessments -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol EventGraphRuntime
open GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {setup : Setup (Player := Player) (L := L)} {Signal : Type*}
    {signal : State L setup.context → Signal}
    {timeouts : EventTimeouts setup.informationGraph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
    {scheduler : (application setup timeouts leaks).Scheduler} {horizon : Nat}
    (menu : (application setup timeouts leaks).ResponseMenu)
    (supported : ∀ key, key ∈ (setup.initialLaw.map signal).support)
    (read : Player → (application setup timeouts leaks).Info → Signal)
    (observed : ∀ draw ∈ setup.initialLaw.support,
      ∀ execution : (application setup timeouts leaks).Execution,
      EventGraphRuntime.State.Invariant (graph := setup.informationGraph)
        (setup.eventInputs draw) execution.application → ∀ who,
        read who (some (execution.logs who,
          execution.observe (application setup timeouts leaks) who)) = signal draw)
    (viewRead : Player → (application setup timeouts leaks).PlayerView → Signal)
    (same : ∀ who past view, read who (some (past, view)) = viewRead who view)

local notation "app" => application setup timeouts leaks
local notation "globalLaw" => Vegas.initialLaw setup
local notation "law" k => Vegas.initialLaw (setup.conditionInitial signal k)

include same in
/-- The complete physical terminal-state law of the global raw assessment is the
mixture of the component assessments' terminal-state laws. -/
theorem ledger_componentAssessment_stateLaw [Finite Player]
    (assessments : ∀ k, (menu.information (law k) horizon scheduler).BehavioralAssessment) :
    ((menu.run globalLaw horizon scheduler
      (ledger_componentAssessment menu supported read observed assessments).strategy).map
        (fun h => (h.state : (app).ProtocolState))) =
      (setup.initialLaw.map signal).bind fun k =>
        (menu.run (law k) horizon scheduler (assessments k).strategy).map
          (fun h => (h.state : (app).ProtocolState)) := by
  let clients := fun k => menu.decodeProfile (law k) horizon scheduler (assessments k).strategy
  have finish (init : PMF (app).State) (profile : Player → (app).Policy) :
      (app).finish init horizon scheduler profile none =
        ((app).roundsFrom init scheduler profile horizon).map (app).finished := by
    simp only [ReactiveApplication.finish, ReactiveApplication.roundsFrom, PMF.map_bind]
  have knows draw (member : draw ∈ setup.initialLaw.support) (execution : (app).Execution)
      (valid : State.Invariant (graph := setup.informationGraph) (setup.eventInputs draw)
        execution.application) (who : Player) :
      viewRead who (execution.observe (app) who) = signal draw :=
    (same who (execution.logs who) _).symm.trans (observed draw member execution valid who)
  trans (app).finish globalLaw horizon scheduler
    (menu.decodeProfile globalLaw horizon scheduler
      (ledger_componentAssessment menu supported read observed assessments).strategy) none
  · exact menu.runFrom_stateLaw globalLaw horizon scheduler _
      (menu.protocol globalLaw horizon scheduler).initHistory
  rw [decodeProfile_componentAssessment menu supported read observed viewRead same assessments,
    finish, roundsFrom_signalClients (scheduler := scheduler) viewRead knows clients horizon,
    PMF.map_bind]
  apply bind_congr_on_support _
  intro key _
  exact (finish _ _).symm.trans (menu.runFrom_stateLaw (law key) horizon scheduler _
    (menu.protocol (law key) horizon scheduler).initHistory).symm

variable [Fintype Player] {bounds : MessageBounds setup.informationGraph}
  {Parameter : Type} {parameter : State L setup.context → Parameter}
  {utility : Parameter × PublicOutcome setup.program → Player → ℝ} {exit : Player → ℝ}
  {spec : ∀ k, ClientSpec (setup.conditionInitial signal k) timeouts leaks bounds horizon
    scheduler parameter utility exit}
  {intended : ∀ k, (setup.conditionInitial signal k).intendedModel.BehavioralAssessment}

local notation "raw" => bounds.rawMenu timeouts leaks

include same in
/-- Supported global raw histories of compiled component clients end without public
defaults and incur no charge under the common count-evidence service. -/
theorem ledger_componentCompilation_clean
    (compiled : ∀ k, ClientCompilation (spec k) (intended k))
    (evidence : EvidenceReportService (CountEvidence setup.informationGraph))
    (audit : ∀ k, (spec k).evidenceService = evidence)
    (h : ((raw).protocol globalLaw horizon scheduler).History)
    (reached : h ∈ ((raw).run globalLaw horizon scheduler
      (ledger_componentAssessment (raw) supported read observed
        (fun k => (compiled k).assessment)).strategy).support) :
    (∀ control, h.state = some control → control.execution.application.config.defaulted = ∅) ∧
    ∀ who, TerminalAudit.charge (app).stateTraffic ((countAudit timeouts) leaks evidence.sample)
      h.state who = 0 := by
  have mix := ledger_componentAssessment_stateLaw (raw) supported read observed viewRead same
    (fun k => (compiled k).assessment)
  have member := (PMF.mem_support_map_iff
    (fun t : ((raw).protocol globalLaw horizon scheduler).History => t.state) _ h.state).mpr
    ⟨h, reached, rfl⟩
  rw [mix, PMF.support_bind] at member
  obtain ⟨key, _, localMember⟩ := Set.mem_iUnion₂.mp member
  obtain ⟨t, localReached, eq⟩ := (PMF.mem_support_map_iff _ _ _).mp localMember
  constructor
  · intro control atControl
    exact (compiled key).noDefaults t localReached control (eq.trans atControl)
  · intro who
    rw [← audit key, ← eq]
    exact (compiled key).noCharges t localReached who

end Vegas.SourceProgram.Setup
