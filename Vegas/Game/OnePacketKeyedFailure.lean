/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateRecords
import Vegas.Game.OnePacketCertificateLumping

/-! # Keyed primitive failure under assembled native assessments -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup)
    horizon scheduler).InfoState who)]
  [Finite setup.intendedProtocol.History]
  {Public : Type*} {signal : State L setup.context → Public}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler

open Classical in
/-- On the supplied native assessment sequence, decided-event failure has one
score at each late key and option, up to a uniformly vanishing error. -/
theorem keyed_failure_bounds_of_assembled
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler bounds.candidateCount p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (targetSequence n)
      ((bounds.onePacketMenu timeouts leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) :
    ∃ (failureScore : ℕ → LateKey setup timeouts leaks → LateOption bounds.candidateCount → ℝ)
      (drift : ℕ → ℝ), Tendsto drift atTop (nhds 0) ∧
      (∀ n key option, 0 ≤ failureScore n key option ∧ failureScore n key option ≤ 1) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ¬ OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ownedKeyed (FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler)
          (LateDeliveryAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler)
          ((N).agentAt site) →
        ∀ key, lateKey setup timeouts leaks who site.1 = some key → ∀ option,
        |localFailure (2 * horizon + 1) (targetSequence n) site
            {final | DecisionFailed (timeouts := timeouts) key final.state}
            (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale
              positive le_one n ((N).agentAt site) option) - failureScore n key option| ≤
          drift n := by
  let inputs := OnePacketBaseInputs.ofSetup setup timeouts leaks bounds horizon scheduler
    wellFormed independent observable sequence sourceMixed covers coversInputs capacity slots_pos
  have sameScale : scale = inputs.scale := funext scaleEq
  subst scale
  obtain ⟨unforcedDrift, unforcedLimit, unforced⟩ := inputs.lateUnforced setup timeouts leaks
    bounds horizon scheduler wellFormed weights targetSequence assembled mixed bayes
  obtain ⟨recordDrift, recordLimit, records⟩ := inputs.lateRecords_of_keyed setup timeouts leaks
    bounds horizon scheduler wellFormed independent observable weights targetSequence
    assembled mixed bayes
  let lumping := fun n who => certificateLumping setup timeouts leaks bounds horizon scheduler
    sequence inputs.scale positive le_one inputs.covers
    (inputs.one_le_candidateCount setup timeouts leaks bounds horizon scheduler who)
    inputs.slotsLe weights targetSequence assembled n who
  let recordLaw := fun n (key : LateKey setup timeouts leaks) => (records n key.owner).choose key
  let failureOf := fun n (key : LateKey setup timeouts leaks) option record =>
    lumpedFailure setup timeouts leaks bounds horizon scheduler (lumping n key.owner)
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
  let law := onePacketLate setup timeouts leaks bounds horizon scheduler sequence
    inputs.scale
    positive le_one n ((N).agentAt site) option
  let value := fun history : (N).InformationHistory key.owner site.1 =>
    expect (localHistoryRun (2 * horizon + 1) (targetSequence n) site law history)
      (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0)
  have path := expect_near_of_record ((targetSequence n).belief key.owner site)
    (fun history => operationalRecord setup timeouts leaks bounds horizon scheduler
      history.1.trace)
    value (failureOf n key option)
    (fun history => ForcedState setup timeouts leaks key.owner history.1.state)
    (pathDrift n) (pathNonneg n)
    (fun history => expect_mem_unit _ _ fun final => by split <;> norm_num)
    (fun record => expect_mem_unit _ _ ((lumping n key.owner).failure_unit key))
    (fun history supported forced => by
      have near := (lumping n key.owner).pathwise (2 *
        horizon + 1) site
        ⟨Or.inl keyed.1,
          siteDebtFree_of_not_owing setup timeouts leaks bounds horizon scheduler notOwing⟩
        key siteKey option history supported forced
      simpa only [value, localHistoryRun, failureOf, lumpedFailure, pathDrift] using near)
  have mass := unforced n key.owner site notFree notOwing keyed
  have recordNear := (records n key.owner).choose_spec site notFree notOwing
    keyed key siteKey (failureOf n key option)
    (fun record => expect_mem_unit _ _ ((lumping n key.owner).failure_unit key))
  have bridge : localFailure (2 * horizon + 1) (targetSequence n) site
      {final | DecisionFailed (timeouts := timeouts) key final.state} law = expect ((targetSequence
        n).belief key.owner site)
      value := by
    unfold localFailure
    exact expect_localRun _ _ _ _ _
  change |localFailure (2 * horizon + 1) (targetSequence n) site
    {final | DecisionFailed (timeouts := timeouts) key final.state} law - _| ≤ _
  rw [bridge]
  have first := abs_le.mp path
  have second := abs_le.mp recordNear
  rw [abs_le]
  constructor <;> linarith [le_abs_self (unforcedDrift n), le_abs_self (recordDrift n)]

end Vegas
