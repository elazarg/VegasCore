/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNativeComparison
import Vegas.Game.SequentialPhaseTerminalCompletion
import Vegas.Game.RecoveryLateSourcePhase

/-! # Native binding source kernels from actual phase completion and component weights -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (oldScheduler)
local notation "N" => onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
  (nativeScheduler)
local notation "A" => application setup (oldLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

open Classical in
/-- Actual phase component weights determine native comparison laws whose
binding-completion source kernel has the original cubic error bound. Physical
phase completion supplies the counted terminal guard; no recovery service is assumed. -/
theorem native_pendingBinding_sourceKernel
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) (n : ℕ)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (initialLaw setup) horizon
      scheduler)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) :
    letI := sourceHistoryFintype setup leaks bounds horizon scheduler
    letI := sourceInfoDecidableEq setup leaks bounds horizon scheduler
    letI := nativeNature setup leaks scheduler
    letI := nativeInfoDecidableEq setup leaks bounds horizon scheduler
    ∀ {who : Player} (site : (N).InformationSite who),
    (LateDelivery setup (oldLeaks) who site.1 ∨ FirstActivation setup (oldLeaks) who site.1) →
    SiteDebtFree setup (oldLeaks) bounds horizon (nativeScheduler) site →
    ∀ {key : LateKey setup (oldLeaks)}, lateKey setup (oldLeaks) who site.1 = some key →
    ∀ {event : (graph setup).EventId}, pendingEvent setup (oldLeaks) who site.1 = some event →
    ∀ (law : PMF ((N).Choice who site.1)) (history : (N).InformationHistory who site.1),
    ∀ {remaining : Nat} {execution : (A).Execution},
    history.1.state = some ⟨remaining, some who, execution⟩ →
    site.1 = some (execution.recall who, execution.observe (A) who) →
    ForcedState setup (oldLeaks) who history.1.state →
    ∀ {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload},
    ∀ {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload},
    nodeView (graph setup) event = .bind who payload outputEq codeEq →
    execution.application.config.cut.IsPrefix (siteRank site.1) →
    ∀ {point : ProtocolState setup.program},
    sourceServicePrefix? setup (siteRank site.1) execution.application.config = some point →
    ProtocolState.Intended setup.program point →
    ((∃ option : LateOption slots, law = onePacketLate setup (oldLeaks) bounds horizon
        (nativeScheduler) source scale positive le_one n ((N).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
        (nativeScheduler) who site.1)) →
    let comparison := nativeComparisonSequence setup leaks bounds horizon scheduler source scale
      positive le_one weights n
    let installed := Profile.update (sig := (N).behavioralSignature) comparison.strategy who
      ((comparison.strategy who).withLaw site.1 law)
    let phase := (N).runBehavioralUntil
      ((bounds.onePacketMenu (runtime setup) (oldLeaks)).bounded (Vegas.initialLaw setup) horizon
        (nativeScheduler)).wellFoundedHistories installed
      (LateStopped setup (oldLeaks) bounds horizon (nativeScheduler) (siteRank site.1)) history.1
    CompletionPointLaw setup (oldLeaks) bounds horizon (nativeScheduler) installed (siteRank site.1)
      (siteFresh who site.1) history.1
      (expect phase (completionIndicator setup (oldLeaks) bounds horizon (nativeScheduler)
        (siteRank site.1) (siteFresh who site.1)))
      (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile (source n).strategy) point)
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1)) ∧
    expect phase (lateBadStop setup (oldLeaks) bounds horizon (nativeScheduler) (siteRank site.1)
      (siteFresh who site.1) event) ≤ scale n ^ 3 * (2 * horizon + 1) := by
  let := sourceHistoryFintype setup leaks bounds horizon scheduler
  let := sourceInfoDecidableEq setup leaks bounds horizon scheduler
  let := nativeNature setup leaks scheduler
  let := nativeInfoDecidableEq setup leaks bounds horizon scheduler
  intro who site pendingSite debtFree key siteKey event pending law history remaining execution
    current atSite forced payload outputEq codeEq node ordered point decoded intendedPoint lawShape
  have assembled := nativeComparisonSequence_assembled setup leaks bounds horizon scheduler source
    scale positive le_one weights
  exact Vegas.pendingBinding_sourceKernel (recoveryScheduler := oldScheduler) source scale positive
    le_one
    (fun n => RecoveryOnePacket.nativeComparisonWeights setup (oldLeaks) bounds horizon
      (oldScheduler) (recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n)))
    (nativeComparisonSequence setup leaks bounds horizon scheduler source scale positive le_one
      weights) assembled n covers capacity slotsLe site pendingSite debtFree siteKey pending law
    history current atSite forced node ordered decoded intendedPoint
    (phase_terminal_completed_of_decodedIntended setup leaks bounds horizon scheduler completes
      ordered decoded intendedPoint event) lawShape

end Vegas.SequentialPhase
