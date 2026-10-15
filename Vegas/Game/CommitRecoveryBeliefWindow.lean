/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryWindowLaw
import Vegas.Game.CommitRecoveryNonmissingBelief

/-! # Commitment windows under the actual auxiliary source posterior -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
private theorem commitEnd_eq_of_observe (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : SourceProgram.ProtocolState program),
      ProtocolState.observe who program first = ProtocolState.observe who program second →
        ProtocolState.commitEnd program first = ProtocolState.commitEnd program second := by
  intro Γ O program
  induction program with
  | ret => intro first second _same; rfl
  | sample name fresh law next ih =>
      intro first second same
      cases first <;> cases second
      · rfl
      · cases same
      · cases same
      · exact ih _ _ (Sum.inr.inj same)
  | commit name owner fresh guard next ih =>
      intro first second same
      cases first <;> cases second
      · rfl
      · cases same
      · cases same
      · exact ih _ _ (Sum.inr.inj same)
  | reveal published owner name fresh source unresolved next ih =>
      intro first second same
      cases first <;> cases second
      · rfl
      · cases same
      · cases same
      · exact ih _ _ (Sum.inr.inj same)

omit [Fintype Player] in
private theorem fiber_commit_window (wellFormed : setup.WellFormed) (who : Player)
    (current : CommitRecoveryState setup.program) (fuel : Nat)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (within : fuel + ProtocolState.commitEnd setup.program current.point ≤
      ProtocolState.remaining setup.program current.point)
    (history : setup.commitRecoveryModel.InformationHistory who
      (setup.commitRecoveryClearInformation wellFormed who
        (setup.commitRecoveryPrivate who (some current)))) :
    ∃ point : CommitRecoveryState setup.program, history.1.state = some point ∧
      point.excluded = ∅ ∧ ProtocolState.atCommit setup.program point.point = true ∧
      fuel + ProtocolState.commitEnd setup.program point.point ≤
        ProtocolState.remaining setup.program point.point := by
  have privateView := setup.commitRecovery_clearInformation_fiber_private wellFormed who
    (setup.commitRecoveryPrivate who (some current)) history
  have clear := setup.commitRecovery_clearInformation_fiber_clear wellFormed who
    (setup.commitRecoveryPrivate who (some current)) history
  cases state : history.1.state with
  | none => rw [state] at privateView; cases privateView
  | some point =>
      rw [state] at privateView clear
      have same : ProtocolState.observe who setup.program point.point =
          ProtocolState.observe who setup.program current.point := Option.some.inj privateView
      have firstRank := ProtocolView.position_add_remaining who setup.program point.point
      have secondRank := ProtocolView.position_add_remaining who setup.program current.point
      have position := congrArg (ProtocolView.position who setup.program) same
      have sameRemaining : ProtocolState.remaining setup.program point.point =
          ProtocolState.remaining setup.program current.point := by omega
      have sameEnd := commitEnd_eq_of_observe who setup.program point.point current.point same
      have sameCommit := congrArg (ProtocolView.atCommit who setup.program) same
      simp only [ProtocolState.atCommit_observe] at sameCommit
      refine ⟨point, rfl, clear, sameCommit.trans committing, ?_⟩
      rw [sameEnd, sameRemaining]
      exact within

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)

/-- Conditioning a genuine auxiliary information fiber and its entire next
commitment window on no omission preserves the initial posterior. The joint
law retains the original history and actual typed source endpoint. Its
continuation after the window uses the original auxiliary profile, including
all future omission flags and repeated-owner dependence. -/
theorem commitRecovery_belief_commit_window (n fuel : Nat) (who : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (clear : current.excluded = ∅)
    (actor : ProtocolState.actor setup.program current.point = some who)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (within : fuel + ProtocolState.commitEnd setup.program current.point ≤
      ProtocolState.remaining setup.program current.point) :
    let info := setup.commitRecoveryClearInformation wellFormed who
      (setup.commitRecoveryPrivate who (some current))
    let profile := (approximation.sequence n).strategy
    let restricted := setup.commitRecoveryNonmissingProfile profile
    ∃ decision : setup.commitRecoveryModel.IsDecisionInfo who info,
      ∃ positive : 0 < setup.commitRecoveryModel.informationMass restricted who ⟨info, decision⟩,
      let posterior := (approximation.sequence n).belief who ⟨info, decision⟩
      let conditional := setup.commitRecoveryModel.bayesBelief restricted who ⟨info, decision⟩
        (setup.commitRecoveryModel_decisionAntichain who ⟨info, decision⟩) positive
      let original := bindPairLaw posterior (fun history =>
        setup.commitRecoveryModel.runBehavioralFrom profile fuel history.1)
      let normalized := bindPairLaw conditional (fun history =>
        setup.commitRecoveryModel.runBehavioralFrom restricted fuel history.1)
      let event := {pair : setup.commitRecoveryModel.InformationHistory who info ×
        setup.commitRecoveryProtocol.History | setup.CommitRecoveryClear pair.2.state}
      ∃ factor : ℝ, 0 < factor ∧
        (∀ pair, event.indicator original pair = ENNReal.ofReal factor * normalized pair) ∧
        ∃ present : ∃ pair ∈ event, pair ∈ original.support,
          original.filter event present = normalized ∧
          (original.filter event present).map
            (fun pair => (pair.1, setup.commitRecoverySourceState pair.2.state)) =
            normalized.map (fun pair => (pair.1, setup.commitRecoverySourceState pair.2.state)) ∧
          ∀ remaining,
            (original.filter event present).bind (fun pair =>
              setup.commitRecoveryModel.runBehavioralFrom profile remaining pair.2) =
            normalized.bind (fun pair =>
              setup.commitRecoveryModel.runBehavioralFrom profile remaining pair.2) := by
  classical
  intro info profile restricted
  obtain ⟨decision, positive, belief⟩ := setup.commitRecovery_nonmissing_belief finite wellFormed
    target approximation n who current trace clear actor
  refine ⟨decision, positive, ?_⟩
  intro posterior conditional original normalized event
  have windows (history : setup.commitRecoveryModel.InformationHistory who info) :
      ∃ reference : setup.commitRecoveryProtocol.History,
        setup.CommitRecoveryClear reference.state ∧
        reference.trace.length = history.1.trace.length + fuel ∧
        let factor := setup.commitRecoveryNonmissingFactor profile reference.trace /
          setup.commitRecoveryNonmissingFactor profile history.1.trace
        0 < factor ∧
        ∀ final, ({h : setup.commitRecoveryProtocol.History |
          setup.CommitRecoveryClear h.state}).indicator
            (setup.commitRecoveryModel.runBehavioralFrom profile fuel history.1) final =
          ENNReal.ofReal factor *
            setup.commitRecoveryModel.runBehavioralFrom restricted fuel history.1 final := by
    rcases history with ⟨⟨state, pointTrace⟩, sameInfo⟩
    have window := fiber_commit_window setup wellFormed who current fuel committing within
      ⟨⟨state, pointTrace⟩, sameInfo⟩
    cases state with
    | none => obtain ⟨point, impossible, _rest⟩ := window; cases impossible
    | some point =>
        obtain ⟨other, equal, pointClear, pointCommit, pointWithin⟩ := window
        cases Option.some.inj equal
        obtain ⟨reference, referenceClear, length, factorPositive, density, _present⟩ :=
          setup.commitRecovery_commit_window_factorization finite wellFormed target approximation
            n fuel point pointTrace pointClear pointCommit pointWithin
        exact ⟨reference, referenceClear, length, factorPositive, density⟩
  choose reference referenceClear length positiveFactor density using windows
  have observed := setup.commitRecoveryClearInformation_observed wellFormed who trace clear
  let start : setup.commitRecoveryModel.InformationHistory who info :=
    ⟨⟨some current, trace⟩, observed⟩
  let factor := setup.commitRecoveryNonmissingFactor profile (reference start).trace /
    setup.commitRecoveryNonmissingFactor profile start.1.trace
  have factorPositive : 0 < factor := positiveFactor start
  have constant (history : setup.commitRecoveryModel.InformationHistory who info) :
      setup.commitRecoveryNonmissingFactor profile (reference history).trace /
          setup.commitRecoveryNonmissingFactor profile history.1.trace = factor := by
    have sameLength := setup.commitRecovery_clearInformation_fiber_length wellFormed who
      (setup.commitRecoveryPrivate who (some current)) history start
    have sameBefore := setup.commitRecovery_nonmissingFactor_eq_of_clear_length finite wellFormed
      target approximation n history.1.trace start.1.trace
        (setup.commitRecovery_clearInformation_fiber_clear wellFormed who _ history)
        (setup.commitRecovery_clearInformation_fiber_clear wellFormed who _ start) sameLength
    have sameAfter := setup.commitRecovery_nonmissingFactor_eq_of_clear_length finite wellFormed
      target approximation n (reference history).trace (reference start).trace
        (referenceClear history) (referenceClear start) (by rw [length, length, sameLength])
    exact congrArg₂ (fun numerator denominator : ℝ => numerator / denominator) sameAfter sameBefore
  have pointwise (pair : setup.commitRecoveryModel.InformationHistory who info ×
      setup.commitRecoveryProtocol.History) :
      event.indicator original pair = ENNReal.ofReal factor * normalized pair := by
    have localDensity := density pair.1 pair.2
    rw [constant pair.1] at localDensity
    have jointIndicator : event.indicator original pair = posterior pair.1 *
        ({h : setup.commitRecoveryProtocol.History | setup.CommitRecoveryClear h.state}).indicator
          (setup.commitRecoveryModel.runBehavioralFrom profile fuel pair.1.1) pair.2 := by
      by_cases member : setup.CommitRecoveryClear pair.2.state
      · have jointMember : pair ∈ event := member
        have localMember : pair.2 ∈ {h : setup.commitRecoveryProtocol.History |
            setup.CommitRecoveryClear h.state} := member
        rw [Set.indicator_of_mem jointMember, Set.indicator_of_mem localMember,
          bindPairLaw_apply]
      · have jointOutside : pair ∉ event := member
        have localOutside : pair.2 ∉ {h : setup.commitRecoveryProtocol.History |
            setup.CommitRecoveryClear h.state} := member
        rw [Set.indicator_of_notMem jointOutside, Set.indicator_of_notMem localOutside, mul_zero]
    rw [jointIndicator, localDensity]
    have normalizedAtom : normalized pair = conditional pair.1 *
        setup.commitRecoveryModel.runBehavioralFrom restricted fuel pair.1.1 pair.2 :=
      bindPairLaw_apply _ _ _ _
    rw [normalizedAtom]
    change posterior = conditional at belief
    rw [belief]
    ring
  obtain ⟨pair, supported⟩ := normalized.support_nonempty
  have nonzero : ENNReal.ofReal factor * normalized pair ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr factorPositive).ne'
      ((PMF.mem_support_iff _ _).mp supported)
  have member : pair ∈ event := by
    by_contra outside
    have value := pointwise pair
    rw [Set.indicator_of_notMem outside] at value
    exact nonzero value.symm
  have present : ∃ pair ∈ event, pair ∈ original.support := by
    refine ⟨pair, member, (PMF.mem_support_iff _ _).mpr ?_⟩
    have value := pointwise pair
    rw [Set.indicator_of_mem member] at value
    exact value ▸ nonzero
  have mass : (∑' pair, event.indicator original pair) = ENNReal.ofReal factor := by
    simp_rw [pointwise]
    rw [ENNReal.tsum_mul_left, normalized.tsum_coe, mul_one]
  have filtered : original.filter event present = normalized := by
    ext pair
    apply (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr factorPositive).ne'
      ENNReal.ofReal_ne_top).mp
    calc
      _ = event.indicator original pair := by
        rw [← mass]
        exact filter_mass_mul original event present pair
      _ = _ := pointwise pair
  exact ⟨factor, factorPositive, pointwise, present, filtered,
    congrArg (fun law => law.map
      (fun pair => (pair.1, setup.commitRecoverySourceState pair.2.state))) filtered,
    fun remaining => congrArg (fun law => law.bind
      (fun pair => setup.commitRecoveryModel.runBehavioralFrom profile remaining pair.2)) filtered⟩

end Vegas.SourceProgram.Setup
