module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ClientCompiler

@[expose] public section

/-! # Intended assessment fidelity of the decoded physical clients -/

noncomputable section

namespace Vegas.ClientCompilation

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {Parameter : Type} {parameter : State L setup.context → Parameter}
  {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
  {excludedPayoff : Player → ℝ}
  {spec : ClientSpec setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff}
  {intended : setup.intendedModel.BehavioralAssessment} (compiled : ClientCompilation spec intended)

local notation "Initial" => initialLaw setup
local notation "app" => application setup timeouts leaks
local notation "raw" => bounds.rawMenu timeouts leaks
local notation "one" => bounds.onePacketMenu timeouts leaks
local notation "N" => onePacketModel setup timeouts leaks bounds Initial horizon scheduler

/-- At every realized source decision, restricting the physical client and normalizing its
response gives precisely the intended decision law retained by the audit extension. -/
theorem clients_strategy_at_sourceDecision
    {who : Player} (sourceSite : setup.intendedModel.InformationSite who)
    (nativeSite : (N).InformationSite who)
    (realization : SourceDecisionRealization setup timeouts leaks bounds horizon scheduler
      sourceSite nativeSite)
    (rawInfo : ((raw).information Initial horizon scheduler).InfoState who)
    (same : ((reactiveNormalization timeouts) leaks).info who rawInfo =
      (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).information who
        nativeSite.1) :
    (((raw).restrictPolicy Initial horizon scheduler who (compiled.clients who)) rawInfo).map
      (fun choice => Eq.mp (congrArg (((bounds.menu timeouts leaks).information Initial horizon
        scheduler).Choice who) same)
          (((reactiveNormalization timeouts) leaks).choice (raw)
            (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler who rawInfo choice)) =
    (honestChoice setup timeouts leaks bounds Initial horizon scheduler intended who
      nativeSite.1).map
        ((bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).choice who
          nativeSite.1) := by
  rw [compiled.clients_strategy who]
  have transported := MessageBounds.ExtendsOnePacketAssessment.strategy_map bounds timeouts leaks
    Initial horizon scheduler compiled.refinement.extension who nativeSite rawInfo same
  rw [compiled.refinement.fidelity.strategy sourceSite nativeSite realization] at transported
  exact transported

/-- The ordinary physical clients retain the exact intended continuation law from every clean
decoded source boundary, including a boundary outside equilibrium play. -/
theorem clients_continuation_at_sourceBoundary
    (rank : Nat)
    (nativeStart : ((one).protocol Initial horizon scheduler).History)
    (rawStart : ((raw).protocol Initial horizon scheduler).History)
    (same : ((reactiveNormalization timeouts) leaks).history (raw)
      (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler rawStart =
      (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history nativeStart)
    (anchor : (app).Execution)
    (state : nativeStart.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (pointIntended : ProtocolState.Intended setup.program point) :
    ((app).finish Initial horizon scheduler compiled.clients rawStart.state).map
        (sourceReadout setup timeouts leaks) =
      sourceContinuation setup (setup.intendedOpeningProfile intended.strategy) rank
        anchor.application.config := by
  have transported := MessageBounds.ExtendsOnePacketAssessment.runFrom_history_map bounds timeouts
    leaks Initial horizon scheduler compiled.refinement.extension nativeStart rawStart same
  have readouts := congrArg (fun law => law.map (fun final =>
    sourceReadout setup timeouts leaks final.state)) transported
  have normalRead (history : ((raw).protocol Initial horizon scheduler).History) :
      sourceReadout setup timeouts leaks
          (((reactiveNormalization timeouts) leaks).history (raw)
            (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler history).state =
        sourceReadout setup timeouts leaks history.state := by
    change sourceReadout setup timeouts leaks
      (((reactiveNormalization timeouts) leaks).state history.state) =
        sourceReadout setup timeouts leaks history.state
    cases history.state <;> rfl
  have retainedRead (history : ((one).protocol Initial horizon scheduler).History) :
      sourceReadout setup timeouts leaks
          ((bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history
            history).state = sourceReadout setup timeouts leaks history.state := rfl
  have physical := congrArg (fun law => law.map (sourceReadout setup timeouts leaks))
    ((raw).runFrom_stateLaw Initial horizon scheduler compiled.assessment.strategy rawStart)
  simp only [PMF.map_comp, Function.comp_def, normalRead, retainedRead] at readouts physical
  exact physical.symm.trans (readouts.trans (compiled.refinement.fidelity.continuation rank
    nativeStart anchor state boundary point decoded pointIntended))

end Vegas.ClientCompilation
