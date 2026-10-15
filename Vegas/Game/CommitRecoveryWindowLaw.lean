/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNonmissingConditioning
import Vegas.Source.CommitRecoveryCommitWindow

/-! # Exact omission factorization through an actual source commitment window -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

private theorem window_prefix_atom
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (start final : setup.commitRecoveryProtocol.History) (fuel : Nat)
    (ancestral : final ∈ historyCone start) :
    setup.commitRecoveryModel.runBehavioral profile (start.trace.length + fuel) final =
      setup.commitRecoveryModel.runBehavioral profile start.trace.length start *
        setup.commitRecoveryModel.runBehavioralFrom profile fuel start final := by
  classical
  rw [GameTheory.Protocol.InformationModel.runBehavioral,
    setup.commitRecoveryModel.runBehavioralFrom_add, PMF.bind_apply]
  apply tsum_eq_single start
  intro prior different
  by_cases firstZero : setup.commitRecoveryModel.runBehavioralFrom profile start.trace.length
      setup.commitRecoveryProtocol.initHistory prior = 0
  · simp only [firstZero, zero_mul]
  by_cases restZero : setup.commitRecoveryModel.runBehavioralFrom profile fuel prior final = 0
  · simp only [restZero, mul_zero]
  have equal := setup.commitRecoveryModel.eq_of_runBehavioral_support_and_cone profile start prior
    final ((PMF.mem_support_iff _ _).mpr firstZero)
      ((PMF.mem_support_iff _ _).mpr restZero) ancestral
  exact (different equal).elim

private theorem window_clear_supported_length
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (clear : current.excluded = ∅)
    (within : fuel ≤ ProtocolState.remaining setup.program current.point)
    (final : setup.commitRecoveryProtocol.History)
    (supported : final ∈ (setup.commitRecoveryModel.runBehavioralFrom profile fuel
      ⟨some current, trace⟩).support) (finalClear : setup.CommitRecoveryClear final.state) :
    final.trace.length = trace.length + fuel := by
  have countStart := setup.protocol_history_length (CommitmentInterface.forfeiture setup.program)
    (setup.commitRecoveryClearTrace trace clear)
  rw [setup.commitRecoveryClearTrace_length] at countStart
  change trace.length + ProtocolState.remaining setup.program current.point = _ at countStart
  have bound := (setup.commitRecoveryModel.runBehavioralFrom_reachesWithin profile fuel
    ⟨some current, trace⟩ final supported).trace_length_le_add
  have shape :=
    setup.commitRecoveryModel.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom profile
      fuel ⟨some current, trace⟩ final supported
  obtain terminal | length := shape
  · have count := setup.protocol_history_length (CommitmentInterface.forfeiture setup.program)
      (setup.commitRecoveryClearTrace final.trace finalClear)
    rw [setup.commitRecoveryClearTrace_length] at count
    have zero : setup.protocolRemaining (setup.commitRecoverySourceState final.state) = 0 := by
      cases state : final.state with
      | none => rw [state] at terminal; exact terminal.elim
      | some current =>
          change ProtocolState.remaining setup.program current.point = 0
          rw [state] at terminal
          exact (ProtocolState.remaining_zero_iff_terminal setup.program current.point).mpr terminal
    rw [zero, Nat.add_zero] at count
    change final.trace.length ≤ trace.length + fuel at bound
    omega
  · exact length

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)

/-- From any genuine clear source entry, every finite initial segment of the
current commitment block has an exact no-omission factorization. The scalar
is positive and does not depend on sampled hidden values. Conditioning on all
omission bits being false gives the chronological nonmissing auxiliary law,
with the actual source histories and automatic closes retained. -/
theorem commitRecovery_commit_window_factorization (n fuel : Nat)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (clear : current.excluded = ∅)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (within : fuel + ProtocolState.commitEnd setup.program current.point ≤
      ProtocolState.remaining setup.program current.point) :
    let start : setup.commitRecoveryProtocol.History := ⟨some current, trace⟩
    let raw := setup.commitRecoveryModel.runBehavioralFrom
      (approximation.sequence n).strategy fuel start
    let conditioned := setup.commitRecoveryModel.runBehavioralFrom
      (setup.commitRecoveryNonmissingProfile (approximation.sequence n).strategy) fuel start
    let event := {history : setup.commitRecoveryProtocol.History |
      setup.CommitRecoveryClear history.state}
    ∃ reference : setup.commitRecoveryProtocol.History,
      setup.CommitRecoveryClear reference.state ∧ reference.trace.length = trace.length + fuel ∧
      let factor := setup.commitRecoveryNonmissingFactor (approximation.sequence n).strategy
        reference.trace / setup.commitRecoveryNonmissingFactor
          (approximation.sequence n).strategy trace
      0 < factor ∧
      (∀ final, event.indicator raw final = ENNReal.ofReal factor * conditioned final) ∧
      ∃ present : ∃ final ∈ event, final ∈ raw.support,
        raw.filter event present = conditioned := by
  classical
  intro start raw conditioned event
  let profile := (approximation.sequence n).strategy
  let restricted := setup.commitRecoveryNonmissingProfile profile
  have restrictedClear (final : setup.commitRecoveryProtocol.History)
      (supported : final ∈ conditioned.support) : setup.CommitRecoveryClear final.state :=
    setup.commitRecovery_run_nonmissing_commit_clear restricted
      (setup.commitRecovery_nonmissing_supported (approximation.sequence n)
        (approximation.mixed n)) fuel current trace clear committing within final supported
  obtain ⟨reference, referenceSupported⟩ := conditioned.support_nonempty
  have referenceClear := restrictedClear reference referenceSupported
  have referenceLength := window_clear_supported_length setup restricted fuel current trace clear
    (by omega) reference referenceSupported referenceClear
  let before := setup.commitRecoveryNonmissingFactor profile trace
  let after := setup.commitRecoveryNonmissingFactor profile reference.trace
  let factor := after / before
  have beforePositive : 0 < before := setup.commitRecovery_nonmissingFactor_pos
    (approximation.sequence n) (approximation.mixed n) trace
  have afterPositive : 0 < after := setup.commitRecovery_nonmissingFactor_pos
    (approximation.sequence n) (approximation.mixed n) reference.trace
  have factorPositive : 0 < factor := div_pos afterPositive beforePositive
  have startDensity := setup.commitRecovery_nonmissing_history_density (approximation.sequence n)
    (approximation.mixed n) trace clear
  change (setup.commitRecoveryModel.runBehavioral profile trace.length start).toReal =
    before * (setup.commitRecoveryModel.runBehavioral restricted trace.length start).toReal
      at startDensity
  have startPositive : 0 < (setup.commitRecoveryModel.runBehavioral profile trace.length
      start).toReal := ENNReal.toReal_pos
    ((PMF.mem_support_iff _ _).mp ((approximation.mixed n).history_supported trace))
    (PMF.apply_ne_top _ _)
  have restrictedStartPositive : 0 < (setup.commitRecoveryModel.runBehavioral restricted
      trace.length start).toReal := by
    rw [startDensity] at startPositive
    nlinarith
  have density (final : setup.commitRecoveryProtocol.History)
      (finalClear : final ∈ event) (ancestral : final ∈ historyCone start)
      (length : final.trace.length = trace.length + fuel) :
      raw final = ENNReal.ofReal factor * conditioned final := by
    have rawSplit := congrArg ENNReal.toReal (window_prefix_atom setup profile start final fuel
      ancestral)
    have restrictedSplit := congrArg ENNReal.toReal (window_prefix_atom setup restricted start
      final fuel ancestral)
    simp only [ENNReal.toReal_mul] at rawSplit restrictedSplit
    have finalDensity := (setup.commitRecovery_no_omission_factorization finite wellFormed target
      approximation n reference.trace referenceClear final.trace finalClear
        (referenceLength.trans length.symm)).2
    have sameHorizon : final.trace.length = start.trace.length + fuel := length
    rw [sameHorizon] at finalDensity
    change _ = after * _ at finalDensity
    have canceled : before * (raw final).toReal = after * (conditioned final).toReal := by
      apply mul_left_cancel₀ restrictedStartPositive.ne'
      calc
        _ = (before * (setup.commitRecoveryModel.runBehavioral restricted trace.length
            start).toReal) * (raw final).toReal := by ring
        _ = (setup.commitRecoveryModel.runBehavioral profile
            (start.trace.length + fuel) final).toReal := by rw [← startDensity]; exact rawSplit.symm
        _ = after * (setup.commitRecoveryModel.runBehavioral restricted
            (start.trace.length + fuel) final).toReal := finalDensity
        _ = _ := by rw [restrictedSplit]; ring
    have realDensity : (raw final).toReal = factor * (conditioned final).toReal := by
      change _ = after / before * _
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff beforePositive.ne').mpr
      simpa only [mul_comm] using canceled
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _))).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal factorPositive.le]
    exact realDensity
  have pointwise (final : setup.commitRecoveryProtocol.History) :
      event.indicator raw final = ENNReal.ofReal factor * conditioned final := by
    by_cases finalClear : final ∈ event
    · rw [Set.indicator_of_mem finalClear]
      by_cases rawZero : raw final = 0
      · by_cases restrictedZero : conditioned final = 0
        · rw [rawZero, restrictedZero, mul_zero]
        · have supported := (PMF.mem_support_iff _ _).mpr restrictedZero
          exact density final finalClear
            (mem_historyCone_of_reachesWithin
              (setup.commitRecoveryModel.runBehavioralFrom_reachesWithin restricted fuel start
                final supported))
            (window_clear_supported_length setup restricted fuel current trace clear (by omega)
              final supported finalClear)
      · have supported := (PMF.mem_support_iff _ _).mpr rawZero
        exact density final finalClear
          (mem_historyCone_of_reachesWithin
            (setup.commitRecoveryModel.runBehavioralFrom_reachesWithin profile fuel start
              final supported))
          (window_clear_supported_length setup profile fuel current trace clear (by omega)
            final supported finalClear)
    · rw [Set.indicator_of_notMem finalClear]
      have zero : conditioned final = 0 := (PMF.apply_eq_zero_iff _ _).mpr
        (fun supported => finalClear (restrictedClear final supported))
      rw [zero, mul_zero]
  have present : ∃ final ∈ event, final ∈ raw.support := by
    refine ⟨reference, referenceClear, (PMF.mem_support_iff _ _).mpr ?_⟩
    have value := pointwise reference
    have referenceMember : reference ∈ event := referenceClear
    rw [Set.indicator_of_mem referenceMember] at value
    rw [value]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr factorPositive).ne'
      ((PMF.mem_support_iff _ _).mp referenceSupported)
  refine ⟨reference, referenceClear, referenceLength, factorPositive, pointwise, present, ?_⟩
  have mass : (∑' final, event.indicator raw final) = ENNReal.ofReal factor := by
    simp_rw [pointwise]
    rw [ENNReal.tsum_mul_left, conditioned.tsum_coe, mul_one]
  ext final
  apply (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr factorPositive).ne'
    ENNReal.ofReal_ne_top).mp
  calc
    _ = event.indicator raw final := by rw [← mass]; exact filter_mass_mul raw event present final
    _ = _ := pointwise final


end Vegas.SourceProgram.Setup
