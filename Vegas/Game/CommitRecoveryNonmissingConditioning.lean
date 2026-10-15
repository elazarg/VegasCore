/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNonmissingPosition
import GameTheoryExtensions.Math.Probability.PresentConditional

/-! # Normalizing actual clear auxiliary source prefix laws -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Before any genuine clear reference depth, a supported clear history
cannot have stopped early: clear terminal source histories have full length. -/
private theorem clear_supported_length
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    {referenceState : setup.commitRecoveryProtocol.State}
    (referenceTrace : setup.commitRecoveryProtocol.Trace referenceState)
    (referenceClear : setup.CommitRecoveryClear referenceState)
    (history : setup.commitRecoveryProtocol.History)
    (supported : history ∈ (setup.commitRecoveryModel.runBehavioral profile
      referenceTrace.length).support) (clear : setup.CommitRecoveryClear history.state) :
    history.trace.length = referenceTrace.length := by
  have referenceCount := setup.protocol_history_length
    (CommitmentInterface.forfeiture setup.program)
    (setup.commitRecoveryClearTrace referenceTrace referenceClear)
  rw [setup.commitRecoveryClearTrace_length] at referenceCount
  have lengthBound := (setup.commitRecoveryModel.runBehavioralFrom_reachesWithin profile
    referenceTrace.length setup.commitRecoveryProtocol.initHistory history
      supported).trace_length_le_add
  have shape :=
    setup.commitRecoveryModel.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
      profile referenceTrace.length setup.commitRecoveryProtocol.initHistory history supported
  simp only [initHistory, Trace.length, Nat.zero_add] at shape lengthBound
  obtain terminal | length := shape
  · have count := setup.protocol_history_length (CommitmentInterface.forfeiture setup.program)
      (setup.commitRecoveryClearTrace history.trace clear)
    rw [setup.commitRecoveryClearTrace_length] at count
    have zero : setup.protocolRemaining (setup.commitRecoverySourceState history.state) = 0 := by
      cases state : history.state with
      | none => rw [state] at terminal; exact terminal.elim
      | some current =>
          change ProtocolState.remaining setup.program current.point = 0
          rw [state] at terminal
          exact (ProtocolState.remaining_zero_iff_terminal setup.program current.point).mpr
            terminal
    rw [zero, Nat.add_zero] at count
    omega
  · exact length

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)

/-- The unnormalized law on clear source histories is one fixed positive
scalar times the actual chronological nonmissing law on those same histories. -/
theorem commitRecovery_clear_prefix_mass_factorization (n : Nat)
    {referenceState : setup.commitRecoveryProtocol.State}
    (referenceTrace : setup.commitRecoveryProtocol.Trace referenceState)
    (referenceClear : setup.CommitRecoveryClear referenceState)
    (history : setup.commitRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state) :
    setup.commitRecoveryModel.runBehavioral (approximation.sequence n).strategy
      referenceTrace.length history =
      ENNReal.ofReal (setup.commitRecoveryNonmissingFactor
        (approximation.sequence n).strategy referenceTrace) *
      setup.commitRecoveryModel.runBehavioral
        (setup.commitRecoveryNonmissingProfile (approximation.sequence n).strategy)
        referenceTrace.length history := by
  by_cases sameLength : history.trace.length = referenceTrace.length
  · have density := (setup.commitRecovery_no_omission_factorization finite wellFormed target
      approximation n referenceTrace referenceClear history.trace clear sameLength.symm).2
    rw [sameLength] at density
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _))).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (setup.commitRecovery_nonmissingFactor_pos (approximation.sequence n)
        (approximation.mixed n) referenceTrace).le]
    exact density
  · have zero (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
        setup.commitRecoveryModel.runBehavioral profile referenceTrace.length history = 0 := by
      apply (PMF.apply_eq_zero_iff _ _).mpr
      intro supported
      exact sameLength (clear_supported_length setup profile referenceTrace referenceClear
        history supported clear)
    rw [zero, zero, mul_zero]

/-- Conditioning the actual source approximation on a clear prefix gives
the same history law as chronological nonmissing sampling conditioned on that
prefix. The common no-omission scalar is canceled, not discarded as negligible. -/
theorem commitRecovery_clear_prefix_conditioning (n : Nat)
    {referenceState : setup.commitRecoveryProtocol.State}
    (referenceTrace : setup.commitRecoveryProtocol.Trace referenceState)
    (referenceClear : setup.CommitRecoveryClear referenceState) :
    let raw := setup.commitRecoveryModel.runBehavioral (approximation.sequence n).strategy
      referenceTrace.length
    let conditioned := setup.commitRecoveryModel.runBehavioral
      (setup.commitRecoveryNonmissingProfile (approximation.sequence n).strategy)
      referenceTrace.length
    let event := {history : setup.commitRecoveryProtocol.History |
      setup.CommitRecoveryClear history.state}
    ∃ rawPresent : ∃ history ∈ event, history ∈ raw.support,
      ∃ conditionedPresent : ∃ history ∈ event, history ∈ conditioned.support,
        raw.filter event rawPresent = conditioned.filter event conditionedPresent := by
  classical
  intro raw conditioned event
  let factor := ENNReal.ofReal (setup.commitRecoveryNonmissingFactor
    (approximation.sequence n).strategy referenceTrace)
  have density (history : setup.commitRecoveryProtocol.History)
      (clear : history ∈ event) : raw history = factor * conditioned history :=
    setup.commitRecovery_clear_prefix_mass_factorization finite wellFormed target approximation n
      referenceTrace referenceClear history clear
  let reference : setup.commitRecoveryProtocol.History := ⟨referenceState, referenceTrace⟩
  have rawSupport : reference ∈ raw.support := (approximation.mixed n).history_supported _
  have conditionedSupport : reference ∈ conditioned.support := by
    apply (PMF.mem_support_iff _ _).mpr
    intro zero
    have rawZero := density reference referenceClear
    rw [zero, mul_zero] at rawZero
    exact ((PMF.mem_support_iff _ _).mp rawSupport) rawZero
  let rawPresent : ∃ history ∈ event, history ∈ raw.support :=
    ⟨reference, referenceClear, rawSupport⟩
  let conditionedPresent : ∃ history ∈ event, history ∈ conditioned.support :=
    ⟨reference, referenceClear, conditionedSupport⟩
  refine ⟨rawPresent, conditionedPresent, ?_⟩
  have indicator (history : setup.commitRecoveryProtocol.History) :
      event.indicator raw history = factor * event.indicator conditioned history := by
    by_cases clear : history ∈ event
    · rw [Set.indicator_of_mem clear, Set.indicator_of_mem clear, density history clear]
    · rw [Set.indicator_of_notMem clear, Set.indicator_of_notMem clear, mul_zero]
  have mass : (∑' history, event.indicator raw history) =
      factor * ∑' history, event.indicator conditioned history := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr indicator
  have positive : (∑' history, event.indicator raw history) ≠ 0 := by
    simpa using rawPresent
  ext history
  apply (ENNReal.mul_right_inj positive (raw.tsum_coe_indicator_ne_top event)).mp
  calc
    _ = event.indicator raw history := filter_mass_mul raw event rawPresent history
    _ = factor * event.indicator conditioned history := indicator history
    _ = factor * ((∑' item, event.indicator conditioned item) *
        conditioned.filter event conditionedPresent history) := by rw [filter_mass_mul]
    _ = (∑' item, event.indicator raw item) *
        conditioned.filter event conditionedPresent history := by rw [mass]; ac_rfl

end Vegas.SourceProgram.Setup
