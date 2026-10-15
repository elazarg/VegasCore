/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourcePhaseValue
import Vegas.Game.RecoveryPendingFailure

/-! # Continuation transport through a local source-event response -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

open Classical in
/-- Current-event completion potentials approximate the common stopped future
value. The remaining bad mass is the actual missing-completion-point mass on success. -/
theorem nativeComparison_local_phase_value_sub_le [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (certificate : (NP).WellFoundedHistories) (who : Player) (info : (N).InfoState who)
    (law : PMF ((N).Choice who info)) (history : (NP).History)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (observed : (N).infoOf who history.trace = info)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some who) (key : LateKey setup leaks)
    (decided : decidedEvent key = some event)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw info law)
    let phase := fun final : (NP).History =>
      LateStopped setup leaks bounds horizon (NativeScheduler) rank final ∨ ¬ Clear final.state
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let fresh := fun control : (application setup leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event
    let phaseLaw := (N).runBehavioralUntil certificate installed phase history
    let potential := fun final =>
      (completionPoint setup leaks bounds horizon (NativeScheduler) rank fresh final).elim
        (excludedPayoff who) (sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who)
    |expect ((N).runBehavioralUntil certificate installed stopped history)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup parameter utility excludedPayoff leaks final.state who) -
      expect phaseLaw potential| ≤
      (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
        (2 * horizon + 1) +
      2 * payoffBound * (phaseLaw.toOuterMeasure
        {final | completionPoint setup leaks bounds horizon (NativeScheduler) rank fresh final =
          none ∧ ¬ DecisionFailed key final.state}).toReal := by
  intro common installed phase stopped fresh phaseLaw potential
  let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
    exclusionBase setup parameter utility excludedPayoff leaks final.state who
  let later := fun final : (NP).History =>
    expect ((N).runBehavioralUntil certificate installed stopped final) payoff
  let error := (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
    (2 * horizon + 1)
  let bad := {final : (NP).History |
    completionPoint setup leaks bounds horizon (NativeScheduler) rank fresh final = none ∧
      ¬ DecisionFailed key final.state}
  have coefficientNonneg :
      0 ≤ 2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n))) := by
    have retention := slotRetention_le_one (positive n).le (le_one n)
    positivity
  have errorNonneg : 0 ≤ error := mul_nonneg coefficientNonneg (by positivity)
  have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded
    · rw [exclusionBase_eq_readout]
      exact readoutBounded _
  have laterBounded : ∀ final, |later final| ≤ payoffBound :=
    fun _ => expect_abs_le_of_bounded boundNonneg payoffBounded
  have sourceBounded : ∀ point,
      |sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile (sequence n).strategy) who point| ≤ payoffBound := by
    intro point
    unfold sourcePointValue
    exact expect_abs_le_of_bounded boundNonneg readoutBounded
  have potentialBounded : ∀ final, |potential final| ≤ payoffBound := by
    intro final
    dsimp only [potential]
    cases completionPoint setup leaks bounds horizon (NativeScheduler) rank fresh final with
    | none => exact excludedBounded
    | some point => exact sourceBounded point
  have clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅) :=
    publicExclusionRecord_of_decodedIntended
      ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
        (NativeScheduler) (current ▸ history.trace))
      ((decodedPoint_eq_of_isPrefix ordered).trans decoded) intended
  have going : ¬ phase history := by
    rintro (⟨control, state, next⟩ | unclear)
    · rw [current] at state
      cases Option.some.inj state
      have := isPrefix_unique next ordered
      omega
    · exact unclear (by rw [current]; exact clear)
  have running : ¬ (NP).terminal history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have active : (NP).active history.state who := by rw [current]; rfl
  have splitLaw := debtStopped_eq_bind_eventPhase certificate installed who history _ current
    ordered point decoded intended
  have pointwise : ∀ final ∈ phaseLaw.support,
      |later final - potential final| ≤ error +
        if final ∈ bad then 2 * payoffBound else 0 := by
    intro final member
    by_cases badFinal : final ∈ bad
    · rw [ite_eq_left badFinal]
      have := (abs_sub _ _).trans (add_le_add (laterBounded final) (potentialBounded final))
      linarith
    · rw [ite_eq_right badFinal, add_zero]
      cases found : completionPoint setup leaks bounds horizon (NativeScheduler) rank fresh final
          with
      | none =>
        have failed : DecisionFailed key final.state := by
          by_contra notFailed
          exact badFinal ⟨found, notFailed⟩
        obtain ⟨anchor, state, completed, nextPrefix, _seen⟩ := recovery_pending_stop_completed
          (initialLaw_initialized setup) (initialLaw_native setup) completes true certificate
            installed
          history current ordered clear event ready final member
        have stored : StoreEventFailed anchor.application.config.store event := by
          simpa only [state, DecisionFailed, decided, completed, true_and] using failed
        have debt := decodedDebt_of_failed_event final _ state event completed who owned stored
        have halt : stopped final := Or.inr debt
        dsimp only [later, potential]
        rw [(N).runBehavioralUntil_of_stopped certificate installed halt, expect_pure,
          show payoff final = excludedPayoff who from ite_eq_left halt, found]
        change |excludedPayoff who - excludedPayoff who| ≤ error
        simpa only [sub_self, abs_zero] using errorNonneg
      | some target =>
        obtain ⟨control, state, nextPrefix, targetDecoded, targetIntended, _fresh⟩ :=
          completionPoint_spec rank fresh final target found
        have decodedState : nativeDecodedState setup leaks final.state = some target := by
          rw [state]
          exact (decodedPoint_eq_of_isPrefix nextPrefix).trans targetDecoded
        obtain ⟨anchor, anchorState, _clear, _completed, atRank, boundary⟩ :=
          recovery_stopped_boundary_of_intended (initialLaw_initialized setup)
            (initialLaw_native setup) completes certificate installed history current ordered event
            ready final member decodedState targetIntended
        have after := runUntil_after_localLaw_eq certificate
          ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
            (NativeScheduler)).actsOnceWhereItMatters common who info law phase stopped history
          observed active running going final member
        have near := nativeComparison_stopped_boundary_value_sub_le setup leaks bounds horizon
          scheduler wellFormed covers capacity sequence scale positive le_one weights n opportunity
          inclusion timely completes certificate (rank + 1) final anchor anchorState boundary target
          atRank targetIntended parameter utility excludedPayoff who boundNonneg readoutBounded
          excludedBounded
        have depth : (application setup leaks).rank horizon final.state ≤ 2 * horizon + 1 := by
          have := (application setup leaks).trace_bound (initialLaw setup) horizon (NativeScheduler)
            ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
              (NativeScheduler) final.trace)
          omega
        dsimp only [later, potential]
        rw [after, found]
        exact near.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast depth) coefficientNonneg)
  rw [splitLaw, expect_bind_tower_bounded _ _ _ payoffBounded]
  change |expect phaseLaw later - expect phaseLaw potential| ≤ _
  rw [← expect_sub (payoffIntegrable_of_bounded _ _ laterBounded)
    (payoffIntegrable_of_bounded _ _ potentialBounded)]
  let gap := fun final => later final - potential final
  have gapIntegrable : PayoffIntegrable phaseLaw gap :=
    payoffIntegrable_sub (payoffIntegrable_of_bounded _ _ laterBounded)
      (payoffIntegrable_of_bounded _ _ potentialBounded)
  have upper := expect_le_add_event_gap phaseLaw bad (fun _ => error) gap (2 * payoffBound)
    (payoffIntegrable_constant _ _) gapIntegrable
    (fun final member outside => by
      have := (abs_le.mp (pointwise final member)).2
      rw [ite_eq_right outside, add_zero] at this
      exact this)
    (fun final member inside => by
      have := (abs_le.mp (pointwise final member)).2
      simpa only [ite_eq_left inside] using this)
  have lower := expect_le_add_event_gap phaseLaw bad (fun _ => error) (fun final => -gap final)
    (2 * payoffBound) (payoffIntegrable_constant _ _) (payoffIntegrable_neg gapIntegrable)
    (fun final member outside => by
      have := (abs_le.mp (pointwise final member)).1
      rw [ite_eq_right outside, add_zero] at this
      linarith)
    (fun final member inside => by
      have := (abs_le.mp (pointwise final member)).1
      rw [ite_eq_left inside] at this
      linarith)
  rw [expect_constant] at upper lower
  rw [expect_neg] at lower
  exact abs_le.mpr ⟨by linarith, upper⟩

end Vegas.RecoveryOnePacket
