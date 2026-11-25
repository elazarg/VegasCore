module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ClientCompiler

@[expose] public section

/-! # Intended assessment fidelity of the decoded physical clients -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
  {bounds : MessageBounds setup.informationGraph} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {Parameter : Type} {parameter : State L setup.context → Parameter}
  {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
  {excludedPayoff : Player → ℝ}
  {spec : ClientSpec setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff}
  {intended : setup.intendedModel.BehavioralAssessment} (compiled : ClientCompilation spec intended)

local notation "Initial" => initialDistribution setup
local notation "app" => application setup timeouts leaks
local notation "raw" => bounds.rawMenu timeouts leaks
local notation "one" => bounds.onePacketMenu timeouts leaks
local notation "N" => onePacketModel setup timeouts leaks bounds Initial horizon scheduler

variable (setup timeouts leaks bounds horizon scheduler) in
/-- Replay a raw execution prefix by normalizing its responses, recovering the
one-packet history when it exists, and replaying its completed source steps. -/
def rawIntendedHistory? (history : ((raw).protocol Initial horizon scheduler).History) :
    Option setup.intendedProtocol.History :=
  let effective := ((reactiveNormalization timeouts) leaks).history (raw)
    (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler history
  let embed := (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history
  (Function.partialInv embed effective).bind fun retained =>
    intendedHistory? setup timeouts leaks bounds horizon scheduler retained.trace

namespace ClientCompilation

/-- On a forced own turn displaying an intended site, replay of the raw
posterior gives the entire intended posterior, including at repeated turns. -/
theorem raw_belief_replay {who : Player} (source : setup.intendedModel.InformationSite who)
    (site : (N).InformationSite who)
    (rawSite : ((raw).information Initial horizon scheduler).InformationSite who)
    (same : ((reactiveNormalization timeouts) leaks).site (raw)
      (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler who rawSite =
      (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).site who site)
    (projected : source.1 = projectView setup timeouts leaks who site.1)
    (forced : forcedAgent (timeouts := timeouts) (one) Initial horizon scheduler who site.1)
    {past view} (shown : site.1 = some (past, view))
    {event} (ownTurn : view.application.publicView.ownTurn? who = some event) :
    (compiled.assessment.belief who rawSite).map (fun history =>
      rawIntendedHistory? setup timeouts leaks bounds horizon scheduler history.1) =
    (intended.belief who source).map (fun history => some history.1) := by
  let embed := (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history
  let replay := fun history => (Function.partialInv embed history).bind fun retained =>
    intendedHistory? setup timeouts leaks bounds horizon scheduler retained.trace
  have normalized := MessageBounds.ExtendsOnePacketAssessment.belief_history_map bounds timeouts
    leaks Initial horizon scheduler compiled.refinement.extension who site rawSite same
  have transported := congrArg (fun law => PMF.map replay law) normalized
  simp only [PMF.map_comp, Function.comp_def, replay, embed,
    Function.partialInv_left (bounds.onePacketRestriction timeouts leaks Initial horizon
      scheduler).history.injective, Option.bind_some] at transported
  exact transported.trans (compiled.refinement.fidelity.belief source site projected forced
    shown ownTurn)

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

/-- Physical continuations from represented clean source boundaries retain
the joint source-configuration and actual settled-payoff law, with no defaults,
failed reveals or audit charges, including outside equilibrium play. -/
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
    ((app).finish Initial horizon scheduler compiled.clients rawStart.state).bind
        spec.observation =
      (setup.continuationDistribution (setup.intendedOpeningProfile intended.strategy)
        (some point)).map
        (fun terminal => (some terminal, utility (setup.parameterOutcome parameter terminal))) ∧
    ∀ outcome ∈ ((app).finish Initial horizon scheduler compiled.clients rawStart.state).support,
      ∃ (control : (app).Control) (terminal : Config Player L setup.program.terminalCtx),
        outcome = some control ∧
        sourceReadout setup timeouts leaks outcome = some terminal ∧
        control.execution.application.config.defaulted = ∅ ∧
        (∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
        ∀ who, TerminalAudit.charge (app).stateTraffic
          ((countAudit timeouts) leaks spec.evidenceService.sample) outcome who = 0 := by
  refine ⟨compiled.refinement.physical_continuation_source_settlement spec nativeStart rawStart same
    rank anchor state boundary point decoded pointIntended, ?_⟩
  intro outcome supported
  obtain ⟨control, terminal, current, read, defaults, reveals⟩ :=
    compiled.refinement.physical_continuation_source_clean spec nativeStart rawStart same rank
      anchor state boundary point decoded pointIntended outcome supported
  exact ⟨control, terminal, current, read, defaults, reveals,
    compiled.refinement.physical_continuation_noCharges spec nativeStart rawStart same outcome
      supported⟩

end ClientCompilation

end Vegas
