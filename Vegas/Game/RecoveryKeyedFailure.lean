/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryKeyedRecords

/-! # Primitive late failure under the common comparison profiles -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

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
local notation "RApp" => recoveryApplication (runtime setup) leaks
local notation "RawNative" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

open Classical in
/-- The pending-event failure score depends on the late key, up to vanishing
posterior and response errors. The failure is the completed current event,
without a source terminal-readout or native completion assumption. -/
theorem nativeComparison_keyed_failure_bounds [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p)) :
    ∃ (failureScore : ℕ → LateKey setup leaks → LateOption bounds.candidateCount → ℝ)
      (drift : ℕ → ℝ), Tendsto drift atTop (nhds 0) ∧
      (∀ n key option, 0 ≤ failureScore n key option ∧ failureScore n key option ≤ 1) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ownedKeyed (Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler))
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon (NativeScheduler))
          ((N).agentAt site) →
        ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
        |localFailure (2 * horizon + 1)
            (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
              le_one weights n) site {final | DecisionFailed key final.state}
            (onePacketLate setup leaks bounds horizon (NativeScheduler) sequence scale positive
              le_one n ((N).agentAt site) option) - failureScore n key option| ≤ drift n := by
  let inputs := nativeBaseInputs setup leaks bounds horizon scheduler wellFormed independent
    sequence sourceMixed covers coversInputs capacity slots_pos
  have sameScale : scale = inputs.scale := funext scaleEq
  subst scale
  let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence inputs.scale
    positive le_one weights
  have assembled := nativeComparisonSequence_assembled setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  have mixed := nativeComparisonSequence_fullyMixed setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  have bayes := nativeComparisonSequence_bayes setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  obtain ⟨unforcedDrift, unforcedLimit, unforced⟩ := inputs.lateUnforced setup leaks bounds horizon
    (NativeScheduler) wellFormed
    (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
    target assembled mixed bayes
  obtain ⟨recordDrift, recordLimit, records⟩ := nativeComparison_keyed_record_bounds setup leaks
    bounds horizon scheduler wellFormed independent sequence sourceMixed inputs.scale positive
    le_one (fun _ => rfl) covers coversInputs capacity slots_pos weights
  let lumping := fun n who => nativeComparisonLumping setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights covers capacity n who
  let recordLaw := fun n (key : LateKey setup leaks) => (records n key.owner).choose key
  let failureOf := fun n (key : LateKey setup leaks) option record =>
    lumpedFailure setup leaks bounds horizon (NativeScheduler) (lumping n key.owner)
      (2 * horizon + 1) key option record
  let pathDrift := fun n => ((2 * horizon + 1 : ℕ) : ℝ) *
    (inputs.scale n ^ 3 + inputs.scale n ^ 3)
  have pathLimit : Tendsto pathDrift atTop (nhds 0) := by
    have cube := inputs.scale_vanishing.pow 3
    simpa [pathDrift] using (cube.add cube).const_mul ((2 * horizon + 1 : ℕ) : ℝ)
  have pathNonneg : ∀ n, 0 ≤ pathDrift n := fun n => by
    have := (positive n).le
    positivity
  refine ⟨fun n key option => expect (recordLaw n key) (failureOf n key option),
    fun n => pathDrift n + |unforcedDrift n| + |recordDrift n|,
    by simpa using (pathLimit.add unforcedLimit.abs).add recordLimit.abs, ?_, ?_⟩
  · intro n key option
    exact expect_mem_unit _ _ fun record =>
      expect_mem_unit _ _ ((lumping n key.owner).failure_unit key)
  intro n who site notFree notOwing keyed key siteKey option
  have owner : key.owner = who := by
    rcases site with ⟨_ | input, decision⟩
    · simp [lateKey] at siteKey
    · simp only [lateKey, Option.some.injEq] at siteKey
      rw [← siteKey]
  subst who
  let law := onePacketLate setup leaks bounds horizon (NativeScheduler) sequence inputs.scale
    positive le_one n ((N).agentAt site) option
  let value := fun history : (N).InformationHistory key.owner site.1 =>
    expect (localHistoryRun (2 * horizon + 1) (target n) site law history)
      (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)
  have path := expect_near_of_record ((target n).belief key.owner site)
    (fun history => operationalRecord setup leaks bounds horizon (NativeScheduler) history.1.trace)
    value (failureOf n key option)
    (fun history => ForcedState setup leaks key.owner history.1.state)
    (pathDrift n) (pathNonneg n)
    (fun history => expect_mem_unit _ _ fun final => by split <;> norm_num)
    (fun record => expect_mem_unit _ _ ((lumping n key.owner).failure_unit key))
    (fun history supported forced => by
      have near := (lumping n key.owner).pathwise (2 * horizon + 1) site
        ⟨Or.inl keyed.1,
          siteDebtFree_of_not_owing setup leaks bounds horizon (NativeScheduler) notOwing⟩
        key siteKey option history supported forced
      simpa only [value, localHistoryRun, failureOf, lumpedFailure, pathDrift] using near)
  have mass := unforced n key.owner site notFree notOwing keyed
  have recordNear := (records n key.owner).choose_spec site notFree notOwing keyed key siteKey
    option
  have bridge : localFailure (2 * horizon + 1) (target n) site
      {final | DecisionFailed key final.state} law = expect ((target n).belief key.owner site)
      value := by
    unfold localFailure
    exact expect_localRun _ _ _ _ _
  change |localFailure (2 * horizon + 1) (target n) site
    {final | DecisionFailed key final.state} law - _| ≤ _
  rw [bridge]
  have first := abs_le.mp path
  have second := abs_le.mp recordNear
  rw [abs_le]
  constructor <;> linarith [le_abs_self (unforcedDrift n), le_abs_self (recordDrift n)]

end Vegas.RecoveryOnePacket
