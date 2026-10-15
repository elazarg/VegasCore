/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNonmissingReach

/-! # Static omission factors along actual clear source prefixes -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
/-- Along a genuine clear auxiliary history the source sum constructor
records exactly the elapsed source rank, regardless of private values. -/
theorem commitRecovery_clear_position_length (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (clear : setup.CommitRecoveryClear state) :
    (setup.commitRecoveryPrivate who state).map (ProtocolView.position who setup.program) =
      if trace.length = 0 then none else some (trace.length - 1) := by
  have count := setup.protocol_history_length (CommitmentInterface.forfeiture setup.program)
    (setup.commitRecoveryClearTrace trace clear)
  rw [setup.commitRecoveryClearTrace_length] at count
  cases state with
  | none =>
      change trace.length + (instructionCount setup.program + 1) = _ at count
      have zero : trace.length = 0 := by omega
      simp only [commitRecoveryPrivate, Option.map_none, zero, ↓reduceIte]
  | some current =>
      have position := ProtocolView.position_add_remaining who setup.program current.point
      change trace.length + ProtocolState.remaining setup.program current.point = _ at count
      have positive : trace.length ≠ 0 := by omega
      have rank : ProtocolView.position who setup.program
          (ProtocolState.observe who setup.program current.point) = trace.length - 1 := by omega
      simp only [commitRecoveryPrivate, Option.map_some, positive, ↓reduceIte, rank]

omit [Fintype Player] in
/-- At an inactive source coordinate the probability of no omission is one,
independently of the profile and the preceding hidden actions. -/
theorem commitRecovery_nonmissingMass_inactive
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History) (who : Player)
    (inactive : ¬ setup.commitRecoveryProtocol.active history.state who) :
    setup.commitRecoveryNonmissingMass profile who
      (setup.commitRecoveryModel.infoOf who history.trace) = 1 := by
  classical
  let : Subsingleton (setup.commitRecoveryModel.Choice who
    (setup.commitRecoveryModel.infoOf who history.trace)) :=
      setup.commitRecoveryModel.subsingleton_choice_of_not_active history.trace inactive
  let idle : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryModel.infoOf who history.trace) :=
    ⟨none, (setup.commitRecoveryModel.menu_adequate who history.trace none).mpr inactive⟩
  unfold commitRecoveryNonmissingMass
  rw [eq_pure_of_subsingleton
    (profile who (setup.commitRecoveryModel.infoOf who history.trace)) idle, PMF.pure_map]
  simp only [idle, CommitRecoveryMove.missed, Option.elim_none, PMF.pure_apply, ↓reduceIte]

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)

/-- The nonmissing probability is fixed by elapsed source rank, even when
the histories contain different accepted failed bindings and repeated owners. -/
theorem commitRecovery_nonmissingMass_eq_of_clear_length
    (n : Nat) (who : Player) {first second : setup.commitRecoveryProtocol.State}
    (firstTrace : setup.commitRecoveryProtocol.Trace first)
    (secondTrace : setup.commitRecoveryProtocol.Trace second)
    (firstClear : setup.CommitRecoveryClear first)
    (secondClear : setup.CommitRecoveryClear second)
    (sameLength : firstTrace.length = secondTrace.length) :
    setup.commitRecoveryNonmissingMass (approximation.sequence n).strategy who
      (setup.commitRecoveryModel.infoOf who firstTrace) =
      setup.commitRecoveryNonmissingMass (approximation.sequence n).strategy who
        (setup.commitRecoveryModel.infoOf who secondTrace) := by
  have positions : (setup.commitRecoveryPrivate who first).map
      (ProtocolView.position who setup.program) =
      (setup.commitRecoveryPrivate who second).map (ProtocolView.position who setup.program) := by
    rw [setup.commitRecovery_clear_position_length who firstTrace firstClear,
      setup.commitRecovery_clear_position_length who secondTrace secondClear, sameLength]
  cases first with
  | none =>
      cases second with
      | some current => cases positions
      | none =>
          rw [setup.commitRecovery_nonmissingMass_inactive _ ⟨_, firstTrace⟩ who (fun h => h),
            setup.commitRecovery_nonmissingMass_inactive _ ⟨_, secondTrace⟩ who (fun h => h)]
  | some first =>
      cases second with
      | none => cases positions
      | some second =>
          have samePosition := Option.some.inj positions
          have actors := (ProtocolView.recovery_controls_of_position who setup.program _ _
            samePosition).1
          rw [ProtocolState.actor_observe_eq, ProtocolState.actor_observe_eq] at actors
          by_cases firstActor : ProtocolState.actor setup.program first.point = some who
          · have secondActor : ProtocolState.actor setup.program second.point = some who :=
              actors.symm.trans firstActor
            exact congrArg (fun law : PMF Bool => law false)
              (setup.commitRecovery_approximation_missing_eq_at_traces finite wellFormed target
                approximation n who first second firstTrace secondTrace firstClear secondClear
                firstActor secondActor samePosition)
          · have firstInactive : ¬ setup.commitRecoveryProtocol.active (some first) who :=
              fun active => firstActor active.1
            have secondInactive : ¬ setup.commitRecoveryProtocol.active (some second) who :=
              fun active => firstActor (actors.trans active.1)
            rw [setup.commitRecovery_nonmissingMass_inactive _ ⟨_, firstTrace⟩ who firstInactive,
              setup.commitRecovery_nonmissingMass_inactive _ ⟨_, secondTrace⟩ who secondInactive]

/-- The whole no-omission factor is constant over all clear initialized
source histories at the same depth. No independent-per-owner sampling is used. -/
theorem commitRecovery_nonmissingFactor_eq_of_clear_length (n : Nat) :
    ∀ {first second : setup.commitRecoveryProtocol.State}
      (firstTrace : setup.commitRecoveryProtocol.Trace first)
      (secondTrace : setup.commitRecoveryProtocol.Trace second),
      setup.CommitRecoveryClear first → setup.CommitRecoveryClear second →
      firstTrace.length = secondTrace.length →
      setup.commitRecoveryNonmissingFactor (approximation.sequence n).strategy firstTrace =
        setup.commitRecoveryNonmissingFactor (approximation.sequence n).strategy secondTrace
  | _, _, .start, .start, _, _, _ => rfl
  | _, _, .start, .extend _ _ _ _, _, _, same => by cases same
  | _, _, .extend _ _ _ _, .start, _, _, same => by cases same
  | _, _, .extend firstPrior firstJoint firstLegal firstReached,
      .extend secondPrior secondJoint secondLegal secondReached,
      firstClear, secondClear, same => by
      have firstBefore := setup.commitRecoveryClear_before ⟨firstJoint, firstLegal⟩
        firstReached firstClear
      have secondBefore := setup.commitRecoveryClear_before ⟨secondJoint, secondLegal⟩
        secondReached secondClear
      have earlierLength : firstPrior.length = secondPrior.length := Nat.add_right_cancel same
      change _ * _ = _ * _
      rw [commitRecovery_nonmissingFactor_eq_of_clear_length n firstPrior secondPrior
        firstBefore secondBefore earlierLength]
      congr 1
      apply Finset.prod_congr rfl
      intro who _
      exact congrArg ENNReal.toReal (setup.commitRecovery_nonmissingMass_eq_of_clear_length
        finite wellFormed target approximation n who firstPrior secondPrior firstBefore
        secondBefore earlierLength)

/-- At a fixed clear source prefix depth, the original auxiliary history
law factors into one positive static scalar and the chronological nonmissing
history law. Effective actions and the physical omission convention are kept. -/
theorem commitRecovery_no_omission_factorization (n : Nat)
    {referenceState : setup.commitRecoveryProtocol.State}
    (referenceTrace : setup.commitRecoveryProtocol.Trace referenceState)
    (referenceClear : setup.CommitRecoveryClear referenceState)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (clear : setup.CommitRecoveryClear state)
    (sameLength : referenceTrace.length = trace.length) :
    let factor := setup.commitRecoveryNonmissingFactor
      (approximation.sequence n).strategy referenceTrace
    0 < factor ∧
      (setup.commitRecoveryModel.runBehavioral (approximation.sequence n).strategy
        trace.length ⟨state, trace⟩).toReal = factor *
      (setup.commitRecoveryModel.runBehavioral
        (setup.commitRecoveryNonmissingProfile (approximation.sequence n).strategy)
        trace.length ⟨state, trace⟩).toReal := by
  refine ⟨setup.commitRecovery_nonmissingFactor_pos (approximation.sequence n)
    (approximation.mixed n) referenceTrace, ?_⟩
  have density := setup.commitRecovery_nonmissing_history_density (approximation.sequence n)
    (approximation.mixed n) trace clear
  rw [← setup.commitRecovery_nonmissingFactor_eq_of_clear_length finite wellFormed target
    approximation n referenceTrace trace referenceClear clear sameLength] at density
  exact density

end Vegas.SourceProgram.Setup
