/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNormalizedFlagPlan
import Vegas.Game.CommitRecoveryOmissionWindow

/-! # Actual omission marginals of the normalized original source prescription

The original raw choice law retains omission separately from accepted failure
and domain values. This identifies its public kernel before comparing any
failed-attempt continuation.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

private theorem inactive_choice_none (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (choice : setup.commitRecoveryModel.Choice who info)
    (inactive : ¬ setup.commitRecoveryActive who info.1.1) : choice.val = none := by
  cases selected : choice.val with
  | none => rfl
  | some move =>
      have legal := choice.property
      change setup.commitRecoveryMenu who info choice.val at legal
      rw [selected] at legal
      exact (inactive legal.1).elim

private theorem failure_missed (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (active : setup.commitRecoveryActive who info.1.1)
    (committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true)
    (omitted : Bool) :
    CommitRecoveryMove.missed (setup.commitRecoveryFailureChoice who info omitted).val =
      omitted := by
  cases chosen : (setup.commitRecoveryFailureChoice who info omitted).val with
  | none =>
      have legal := (setup.commitRecoveryFailureChoice who info omitted).property
      change setup.commitRecoveryMenu who info _ at legal
      rw [chosen] at legal
      exact (legal active).elim
  | some move =>
      have property := (setup.commitRecoveryFailureChoice_spec who info omitted move chosen).2
      simpa only [CommitRecoveryMove.missed, Option.elim_some, committing,
        Bool.true_and] using property

private theorem value_missed (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (value : setup.CommitRecoveryValueChoice who info) :
    CommitRecoveryMove.missed value.val.val = false := by
  cases selected : value.val.val with
  | none => rfl
  | some move => exact (value.property move selected).1

/-- At any active original commitment input, the public omission law is
exactly the prescribed omission coin. Accepted failures remain nonmissing;
no conditional posterior or value-independence premise is used. -/
theorem commitRecoveryValueTremble_missed_law (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (active : setup.commitRecoveryActive who info.1.1)
    (committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who info)) :
    (setup.commitRecoveryValueTremble who info omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values).map
          (fun choice => CommitRecoveryMove.missed choice.val) =
      mix omission omissionNonnegative omissionBounded (PMF.pure true) (PMF.pure false) := by
  have ordinary : values.map (fun value => CommitRecoveryMove.missed value.val.val) =
      PMF.pure false := by
    calc
      _ = values.map (fun _ => false) := by
        apply congrArg (fun f => values.map f)
        funext value
        exact setup.value_missed who info value
      _ = _ := PMF.map_const _ _
  simp only [commitRecoveryValueTremble, committing, ↓reduceIte, mix_map, PMF.pure_map,
    PMF.map_comp, Function.comp_def,
    setup.failure_missed who info active committing true,
    setup.failure_missed who info active committing false]
  exact congrArg (mix omission omissionNonnegative omissionBounded (PMF.pure true))
    ((congrArg (mix bad badNonnegative badBounded (PMF.pure false)) ordinary).trans
      (mix_self bad badNonnegative badBounded (PMF.pure false)))

private theorem normalized_commit (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true) :
    (setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who info)).1.1.1.elim false
        (ProtocolView.atCommit who setup.program) = true := by
  have view : (setup.commitRecoveryNoMissInformation who info).1.1.1 = info.1.1.1 := by
    unfold commitRecoveryNoMissInformation
    split
    · exact (setup.commitRecoveryWithAttemptExclusions_controls who _ _ info).1
    · rfl
  change ((setup.commitRecoveryNoMissInformation who info).1.1.1.map
    (ProtocolView.eraseHistory who setup.program)).elim false
      (ProtocolView.atCommit who setup.program) = true
  rw [view]
  cases current : info.1.1.1 with
  | none => simp only [current, Option.elim_none, Bool.false_eq_true] at committing
  | some observed =>
      simpa only [Option.map_some, Option.elim_some, ProtocolView.atCommit_eraseHistory,
        current] using committing

open Classical in
/-- The actual normalized full-information prescription has one fixed
omission coin at active commitment inputs and no omission at inactive inputs.
Its full private query, domain values and accepted-failure rate do not enter
this public marginal. -/
theorem commitRecoveryNormalizedTrembledProfile_missed_law
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (who : Player) (info : setup.commitRecoveryModel.InfoState who)
    (committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true) :
    (setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded values who info).map
        (fun choice => CommitRecoveryMove.missed choice.val) =
      if setup.commitRecoveryActive who info.1.1 then
        mix omission omissionNonnegative omissionBounded (PMF.pure true) (PMF.pure false)
      else PMF.pure false := by
  classical
  by_cases active : setup.commitRecoveryActive who info.1.1
  · rw [ite_eq_left active]
    let query := setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who info)
    have queryActive : setup.commitRecoveryActive who query.1.1 := by
      by_contra inactive
      let choice : setup.commitRecoveryModel.Choice who query := ⟨none, inactive⟩
      have original := ((setup.commitRecoveryNoMissErasedChoice who info).symm choice).property
      change ¬ setup.commitRecoveryActive who info.1.1 at original
      exact original active
    change (setup.commitRecoveryNoMissErasedProfile
      (fun owner query => setup.commitRecoveryValueTremble owner query omission
        omissionNonnegative omissionBounded bad badNonnegative badBounded (values owner query))
        who info).map (CommitRecoveryMove.missed ∘ Subtype.val) = _
    rw [← PMF.map_comp, setup.commitRecoveryNoMissErasedProfile_raw, PMF.map_comp]
    exact setup.commitRecoveryValueTremble_missed_law who query queryActive
      (setup.normalized_commit who info committing) omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded (values who query)
  · rw [ite_eq_right active]
    calc
      _ = (setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative
        omissionBounded bad badNonnegative badBounded values who info).map (fun _ => false) := by
          apply congrArg (fun f => PMF.map f _)
          funext choice
          rw [setup.inactive_choice_none who info choice active]
          rfl
      _ = _ := PMF.map_const _ _

private theorem current_signal (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.commitRecoveryModel.infoOf who trace).1.1 =
      (setup.commitRecoveryPrivate who state, setup.commitRecoveryPublic state) := by
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace).1.1 = _
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  exact setup.commitRecoverySignals_current who trace

variable [Fintype Player]

/-- The actual behavioral joint pushes forward to the independent product of
its original information-local omission marginals. -/
theorem commitRecovery_joint_missed_law
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    (setup.commitRecoveryModel.behavioralJoint profile history.trace running).map
        (fun draw who => CommitRecoveryMove.missed (draw.val who)) =
      independentProduct (fun who =>
        (profile who (setup.commitRecoveryModel.infoOf who history.trace)).map
          (fun choice => CommitRecoveryMove.missed choice.val)) := by
  calc
    _ = ((setup.commitRecoveryModel.behavioralJoint profile history.trace running).map
      Subtype.val).map (fun joint who => CommitRecoveryMove.missed (joint who)) := by
        rw [PMF.map_comp]
        rfl
    _ = _ := by
      rw [setup.commitRecoveryModel.behavioralJoint_map_val, independentProduct_map]
      simp only [PMF.map_comp, Function.comp_def]

/-- The normalized original joint omission kernel is determined by the
actual public cursor and exclusions. All players' private value rules can
change, without changing this kernel. -/
theorem commitRecoveryNormalizedTrembledProfile_joint_missed_eq
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (leftValues rightValues : (who : Player) →
      (info : setup.commitRecoveryErasedModel.InfoState who) →
        PMF (setup.CommitRecoveryValueChoice who info))
    (left right : CommitRecoveryState setup.program)
    (leftTrace : setup.commitRecoveryProtocol.Trace (some left))
    (rightTrace : setup.commitRecoveryProtocol.Trace (some right))
    (leftRunning : ¬ setup.commitRecoveryProtocol.terminal (some left))
    (rightRunning : ¬ setup.commitRecoveryProtocol.terminal (some right))
    (leftCommit : ProtocolState.atCommit setup.program left.point = true)
    (rightCommit : ProtocolState.atCommit setup.program right.point = true)
    (excluded : left.excluded = right.excluded)
    (observed : ∀ who, ProtocolView.publicOnly who setup.program
      (ProtocolState.observe who setup.program left.point) =
        ProtocolView.publicOnly who setup.program
          (ProtocolState.observe who setup.program right.point)) :
    (setup.commitRecoveryModel.behavioralJoint
      (setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded leftValues) leftTrace leftRunning).map
        (fun draw who => CommitRecoveryMove.missed (draw.val who)) =
      (setup.commitRecoveryModel.behavioralJoint
        (setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
          bad badNonnegative badBounded rightValues) rightTrace rightRunning).map
            (fun draw who => CommitRecoveryMove.missed (draw.val who)) := by
  rw [setup.commitRecovery_joint_missed_law _ ⟨some left, leftTrace⟩ leftRunning,
    setup.commitRecovery_joint_missed_law _ ⟨some right, rightTrace⟩ rightRunning]
  apply congrArg independentProduct
  funext who
  have actor : ProtocolState.actor setup.program left.point =
      ProtocolState.actor setup.program right.point := by
    have same := congrArg (ProtocolView.actor who setup.program) (observed who)
    simpa only [ProtocolView.actor_publicOnly, ProtocolState.actor_observe_eq] using same
  have active : setup.commitRecoveryActive who
      (setup.commitRecoveryModel.infoOf who leftTrace).1.1 ↔
        setup.commitRecoveryActive who (setup.commitRecoveryModel.infoOf who rightTrace).1.1 := by
    rw [setup.current_signal who leftTrace, setup.current_signal who rightTrace]
    simp only [commitRecoveryActive, commitRecoveryPrivate, Option.map_some, Option.elim_some,
      ProtocolState.actor_observe_eq, commitRecoveryPublic, actor, excluded]
  have leftIsCommit : (setup.commitRecoveryModel.infoOf who leftTrace).1.1.1.elim false
      (ProtocolView.atCommit who setup.program) = true := by
    rw [setup.current_signal who leftTrace]
    simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
      ProtocolState.atCommit_observe] using leftCommit
  have rightIsCommit : (setup.commitRecoveryModel.infoOf who rightTrace).1.1.1.elim false
      (ProtocolView.atCommit who setup.program) = true := by
    rw [setup.current_signal who rightTrace]
    simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
      ProtocolState.atCommit_observe] using rightCommit
  rw [setup.commitRecoveryNormalizedTrembledProfile_missed_law omission omissionNonnegative
    omissionBounded bad badNonnegative badBounded leftValues who _ leftIsCommit,
    setup.commitRecoveryNormalizedTrembledProfile_missed_law omission omissionNonnegative
    omissionBounded bad badNonnegative badBounded rightValues who _ rightIsCommit, propext active]

/-- Arbitrary domain prescriptions, including private-query changes caused
by earlier values, have the same actual original omission-word law throughout
a commitment window. This is derived from the real initialized raw kernels. -/
theorem commitRecoveryNormalizedTrembledProfile_window_omission_law_eq
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (leftValues rightValues : (who : Player) →
      (info : setup.commitRecoveryErasedModel.InfoState who) →
        PMF (setup.CommitRecoveryValueChoice who info))
    (observer : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (fuel : Nat)
    (within : fuel + ProtocolState.commitEnd setup.program first.point ≤
      ProtocolState.remaining setup.program first.point) :
    (setup.commitRecoveryModel.runBehavioralFrom
      (setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded leftValues) fuel ⟨some first, prior⟩).map
          (fun history => setup.omissionRecall history.trace) =
      (setup.commitRecoveryModel.runBehavioralFrom
        (setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
          bad badNonnegative badBounded rightValues) fuel ⟨some first, prior⟩).map
            (fun history => setup.omissionRecall history.trace) := by
  apply setup.commitRecovery_window_omission_law_eq _ _ first prior committing ?_
    fuel ⟨some first, prior⟩ ⟨some first, prior⟩ .refl .refl rfl (by dsimp only; omega)
  intro left right leftKept rightKept word inside leftRunning rightRunning
  obtain ⟨currentLeft, currentRight, leftState, rightState, _leftSaved, _rightSaved,
    _leftEntry, _rightEntry, _leftGeneration, _rightGeneration, excluded, observed, _past⟩ :=
      setup.inside_attempt_public_eq observer first prior committing left.trace right.trace
        leftKept rightKept word inside
  obtain ⟨point, pointState, leftCommit, _end, _rank⟩ :=
    setup.commitRecovery_prefix_inside_commit first prior committing left.trace leftKept inside
  have equal := Option.some.inj (leftState.symm.trans pointState)
  subst point
  have clock : left.trace.length = right.trace.length := by
    have lengths := congrArg List.length word
    simpa only [omissionRecall, List.length_map, setup.recoveryJointRecall_length] using lengths
  obtain ⟨other, otherState, rightCommit, _end, _rank⟩ :=
    setup.commitRecovery_prefix_inside_commit first prior committing right.trace rightKept
      (by omega)
  have equal := Option.some.inj (rightState.symm.trans otherState)
  subst other
  rcases left with ⟨leftState', leftTrace⟩
  rcases right with ⟨rightState', rightTrace⟩
  dsimp only at leftState rightState
  subst leftState'
  subst rightState'
  exact setup.commitRecoveryNormalizedTrembledProfile_joint_missed_eq omission omissionNonnegative
    omissionBounded bad badNonnegative badBounded leftValues rightValues currentLeft currentRight
    leftTrace rightTrace leftRunning rightRunning leftCommit rightCommit excluded observed

/-- Changing arbitrary private domain rules during an already failed original
attempt does not change the joint terminal law after its real close, when the
selected continuation is resumed. The original omission-word law is derived
from the normalized raw prescription, not supplied as a hypothesis. -/
theorem commitRecoveryNormalizedTrembledProfile_failed_window_terminal_joint_eq
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (leftValues rightValues : (who : Player) →
      (info : setup.commitRecoveryErasedModel.InfoState who) →
        PMF (setup.CommitRecoveryValueChoice who info))
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (observer : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (failed : first.NewFailure) (fuel : Nat)
    (distance : fuel + ProtocolState.commitEnd setup.program first.saved =
      ProtocolState.remaining setup.program first.point) :
    let certificate := setup.commitRecoveryProtocol_bounded.wellFoundedHistories
    let continuation := fun boundary : setup.commitRecoveryProtocol.History =>
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryNoMissErasedProfile profile) boundary).map (fun final =>
          (setup.protocolReadout (setup.commitRecoverySourceState final.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who final))
    (setup.commitRecoveryModel.runBehavioralFrom
      (setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded leftValues) fuel ⟨some first, prior⟩).bind continuation =
      (setup.commitRecoveryModel.runBehavioralFrom
        (setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
          bad badNonnegative badBounded rightValues) fuel ⟨some first, prior⟩).bind
            continuation := by
  have frontier := setup.commitRecovery_blockFrontier prior
  have ending : ProtocolState.commitEnd setup.program first.point =
      ProtocolState.commitEnd setup.program first.saved := by
    rcases frontier with ⟨_saved, _live, ending⟩ | same
    · exact ending
    · rw [same]
  apply setup.commitRecovery_failed_window_terminal_joint_eq _ _ profile utility excludedPayoff
    observer first prior committing failed fuel distance
  exact setup.commitRecoveryNormalizedTrembledProfile_window_omission_law_eq omission
    omissionNonnegative omissionBounded bad badNonnegative badBounded leftValues rightValues
    observer first prior committing fuel (by omega)

end Vegas.SourceProgram.Setup
