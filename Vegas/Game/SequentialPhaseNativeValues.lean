/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNativeComparison
import Vegas.Game.SequentialPhaseTerminalCompletion
import Vegas.Game.RecoveryLateSourcePhase

/-! # Native binding source kernels and continuation values from physical phase service -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler runtime
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "N" => onePacketModel (runtime := runtime) setup (RecoveryLeaks) bounds
  (Vegas.initialLaw setup) horizon
  (nativeScheduler)
local notation "A" => application (runtime := runtime) setup (RecoveryLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

open Classical in
/-- Actual phase component weights determine native comparison laws whose
binding-completion source kernel has the original cubic error bound. Physical
phase completion supplies the counted terminal guard; no recovery service is assumed. -/
theorem native_pendingBinding_sourceKernel
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p)) (n : ℕ)
    (completes : PhaseService.CompletesPlay runtime leaks (phaseInitialLaw setup) horizon
      scheduler)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) :
    ∀ {who : Player} (site : (N).InformationSite who),
    (LateDelivery (runtime := runtime) setup (RecoveryLeaks) who site.1 ∨ FirstActivation (runtime
      := runtime) setup (RecoveryLeaks) who
        site.1) →
    SiteDebtFree (runtime := runtime) setup (RecoveryLeaks) bounds horizon (nativeScheduler) site →
    ∀ {key : LateKey (runtime := runtime) setup (RecoveryLeaks)}, lateKey (runtime := runtime)
      setup (RecoveryLeaks) who site.1 = some key →
    ∀ {event : (graph setup).EventId}, pendingEvent (runtime := runtime) setup (RecoveryLeaks) who
      site.1 = some event →
    ∀ (law : PMF ((N).Choice who site.1)) (history : (N).InformationHistory who site.1),
    ∀ {remaining : Nat} {execution : (A).Execution},
    history.1.state = some ⟨remaining, some who, execution⟩ →
    site.1 = some (execution.recall who, execution.observe (A) who) →
    ForcedState (runtime := runtime) setup (RecoveryLeaks) who history.1.state →
    ∀ {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload},
    ∀ {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload},
    nodeView (graph setup) event = .bind who payload outputEq codeEq →
    execution.application.config.cut.IsPrefix (siteRank (runtime := runtime) site.1) →
    ∀ {point : ProtocolState setup.program},
    sourceServicePrefix? setup (siteRank (runtime := runtime) site.1) execution.application.config
      = some point →
    ProtocolState.Intended setup.program point →
    ((∃ option : LateOption slots, law = onePacketLate (runtime := runtime) setup (RecoveryLeaks)
      bounds horizon
        (nativeScheduler) source scale positive le_one n ((N).agentAt site) option) ∨
      law = PMF.pure (silenceChoice (runtime := runtime) setup (RecoveryLeaks) bounds
        (Vegas.initialLaw setup) horizon
        (nativeScheduler) who site.1)) →
    let comparison := nativeComparisonSequence setup runtime leaks bounds horizon scheduler source
      scale
      positive le_one weights n
    let installed := Profile.update (sig := (N).behavioralSignature) comparison.strategy who
      ((comparison.strategy who).withLaw site.1 law)
    let phase := (N).runBehavioralUntil
      ((bounds.onePacketMenu runtime (RecoveryLeaks)).bounded (Vegas.initialLaw setup)
          horizon
        (nativeScheduler)).wellFoundedHistories installed
      (LateStopped (runtime := runtime) setup (RecoveryLeaks) bounds horizon (nativeScheduler)
        (siteRank (runtime := runtime) site.1))
          history.1
    CompletionPointLaw (runtime := runtime) setup (RecoveryLeaks) bounds horizon (nativeScheduler)
      installed (siteRank (runtime := runtime)
        site.1)
      (siteFresh (runtime := runtime) who site.1) history.1
      (expect phase (completionIndicator (runtime := runtime) setup (RecoveryLeaks) bounds horizon
        (nativeScheduler)
        (siteRank (runtime := runtime) site.1) (siteFresh (runtime := runtime) who site.1)))
      (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile (source n).strategy) point)
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1)) ∧
    expect phase (lateBadStop (runtime := runtime) setup (RecoveryLeaks) bounds horizon
      (nativeScheduler) (siteRank (runtime := runtime)
        site.1)
      (siteFresh (runtime := runtime) who site.1) event) ≤ scale n ^ 3 * (2 * horizon + 1) := by
  intro who site pendingSite debtFree key siteKey event pending law history remaining execution
    current atSite forced payload outputEq codeEq node ordered point decoded intendedPoint lawShape
  have assembled := nativeComparisonSequence_assembled setup runtime leaks bounds horizon
    scheduler source
    scale positive le_one weights
  exact Vegas.pendingBinding_sourceKernel (runtime := runtime) (recoveryScheduler :=
    RecoveryScheduler) source scale
      positive
    le_one
    (fun n => RecoveryOnePacket.nativeComparisonWeights (runtime := runtime) setup (RecoveryLeaks)
      bounds horizon
      (RecoveryScheduler) (recoveryComparisonWeights setup runtime leaks bounds horizon scheduler
        (weights
          n)))
    (nativeComparisonSequence setup runtime leaks bounds horizon scheduler source scale positive
      le_one
      weights) assembled n covers capacity slotsLe site pendingSite debtFree siteKey pending law
    history current atSite forced node ordered decoded intendedPoint
    (phase_terminal_completed_of_decodedIntended setup runtime leaks bounds horizon scheduler
      completes
      ordered decoded intendedPoint event) lawShape

open Classical in
/-- The actual native comparison has the affine source-continuation value up to
the original cubic error, using physical phase completion and ordinary bounded
source readouts. No recovery service or additional payoff floor is assumed. -/
theorem native_pendingBinding_sourceValue
    (source : ℕ → setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p)) (n : ℕ)
    (completes : PhaseService.CompletesPlay runtime leaks (phaseInitialLaw setup) horizon
      scheduler)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) :
    ∀ {who : Player} (site : (N).InformationSite who),
    (LateDelivery (runtime := runtime) setup (RecoveryLeaks) who site.1 ∨ FirstActivation (runtime
      := runtime) setup (RecoveryLeaks) who
        site.1) →
    SiteDebtFree (runtime := runtime) setup (RecoveryLeaks) bounds horizon (nativeScheduler) site →
    ∀ {key : LateKey (runtime := runtime) setup (RecoveryLeaks)}, lateKey (runtime := runtime)
      setup (RecoveryLeaks) who site.1 = some key →
    ∀ {event : (graph setup).EventId}, pendingEvent (runtime := runtime) setup (RecoveryLeaks) who
      site.1 = some event →
    ∀ (law : PMF ((N).Choice who site.1)) (history : (N).InformationHistory who site.1),
    ∀ {remaining : Nat} {execution : (A).Execution},
    history.1.state = some ⟨remaining, some who, execution⟩ →
    site.1 = some (execution.recall who, execution.observe (A) who) →
    ForcedState (runtime := runtime) setup (RecoveryLeaks) who history.1.state →
    ∀ {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload},
    ∀ {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload},
    nodeView (graph setup) event = .bind who payload outputEq codeEq →
    execution.application.config.cut.IsPrefix (siteRank (runtime := runtime) site.1) →
    ∀ {point : ProtocolState setup.program},
    sourceServicePrefix? setup (siteRank (runtime := runtime) site.1) execution.application.config
      = some point →
    ProtocolState.Intended setup.program point →
    ((∃ option : LateOption slots, law = onePacketLate (runtime := runtime) setup (RecoveryLeaks)
      bounds horizon
        (nativeScheduler) source scale positive le_one n ((N).agentAt site) option) ∨
      law = PMF.pure (silenceChoice (runtime := runtime) setup (RecoveryLeaks) bounds
        (Vegas.initialLaw setup) horizon
        (nativeScheduler) who site.1)) →
    ∀ {Parameter : Type} (parameter : State L setup.context → Parameter)
      (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
      (excludedPayoff : Player → ℝ) {bound : ℝ},
    (∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) →
    |excludedPayoff who| ≤ bound →
    let profile := setup.intendedOpeningProfile (source n).strategy
    let comparison := nativeComparisonSequence setup runtime leaks bounds horizon scheduler source
      scale
      positive le_one weights n
    let installed := Profile.update (sig := (N).behavioralSignature) comparison.strategy who
      ((comparison.strategy who).withLaw site.1 law)
    let phase := (N).runBehavioralUntil
      ((bounds.onePacketMenu runtime (RecoveryLeaks)).bounded (Vegas.initialLaw setup)
          horizon
        (nativeScheduler)).wellFoundedHistories installed
      (LateStopped (runtime := runtime) setup (RecoveryLeaks) bounds horizon (nativeScheduler)
        (siteRank (runtime := runtime) site.1))
          history.1
    |expect phase (completionValue (runtime := runtime) setup (RecoveryLeaks) bounds horizon
      (nativeScheduler) parameter
        utility excludedPayoff profile (siteRank (runtime := runtime) site.1) (siteFresh (runtime
          := runtime) who site.1) who
        (fun _ => excludedPayoff who)) -
      ((1 - expect phase (fun final => if DecisionFailed (runtime := runtime) key final.state then
        (1 : ℝ) else 0)) *
          sourcePointValue setup parameter utility excludedPayoff profile who point +
        expect phase (fun final => if DecisionFailed (runtime := runtime) key final.state then (1
          : ℝ) else 0) *
          excludedPayoff who)| ≤
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * bound) := by
  intro who site pendingSite debtFree key siteKey event pending law history remaining execution
    current atSite forced payload outputEq codeEq node ordered point decoded intendedPoint lawShape
    Parameter parameter utility excludedPayoff bound readoutBounded excludedBounded
    profile comparison installed phase
  obtain ⟨kernel, badBound⟩ := native_pendingBinding_sourceKernel setup runtime leaks bounds horizon
    scheduler source scale positive le_one weights n completes covers capacity slotsLe site
    pendingSite debtFree siteKey pending law history current atSite forced node ordered decoded
    intendedPoint
    lawShape
  let menu := bounds.onePacketMenu runtime (RecoveryLeaks)
  let certificate := (menu.bounded (Vegas.initialLaw setup) horizon (nativeScheduler))
    |>.wellFoundedHistories
  have rawTrace := menu.toRawTrace (Vegas.initialLaw setup) horizon (nativeScheduler)
    (current ▸ history.1.trace)
  have initialDecoded := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := exclusionEvidence_of_decodedIntended (runtime := runtime) rawTrace initialDecoded
    intendedPoint
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨_turn, readyView, _, _⟩ := pendingEvent_spec (runtime := runtime) pendingHere
  have ready := (execution.application.publicView_eventReady event).mp readyView
  have decided := decidedEvent_eq_of_pending (runtime := runtime) setup (RecoveryLeaks) horizon
    (nativeScheduler)
      pendingHere
    rawTrace rfl (by simpa only [atSite] using siteKey)
  have freshSafe : ∀ control, siteFresh (runtime := runtime) who site.1 control →
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
    exact id
  apply completionValue_expect_affine_bound_of_completed (runtime := runtime) setup
    (RecoveryLeaks) bounds horizon
    (nativeScheduler) phase (siteRank (runtime := runtime) site.1) key event decided (siteFresh
      (runtime := runtime) who site.1) freshSafe
    ?_ profile point _ _ kernel badBound parameter utility excludedPayoff who readoutBounded
    excludedBounded
  intro final supported
  obtain ⟨anchor, state, eventCompleted, prefixed, _seen⟩ := pending_stop_completed (runtime :=
    runtime)
    (fun control trace controlClear terminal =>
      PhaseService.CompletesPlay.clear_native_counted setup runtime leaks bounds horizon scheduler
        completes
        trace controlClear terminal)
    false certificate installed history.1 current ordered clear event ready final supported
  exact ⟨_, state, prefixed, eventCompleted⟩

end Vegas.SequentialPhase
