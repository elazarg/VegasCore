/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryWordObservation
import Vegas.Source.CommitRecoveryPublicDeterminacy
import Vegas.Source.CommitRecoveryWordMass
import Vegas.Game.CommitRecoveryFlagDensity

/-! # Global original source records under private-word substitution

The public record and each untouched owner's chronological raw coordinate
determine that owner's full information, across every real source branch.
Retried blocks keep their remembered words; no entry law is refreshed.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem jointRecall_length {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.recoveryJointRecall trace).length = trace.length := by
  induction trace with
  | start => rfl
  | extend earlier joint legal reached ih => exact congrArg Nat.succ ih

private theorem publicRecall_extend (who : Player)
    {state target : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal state joint)
    (reached : target ∈ (setup.commitRecoveryProtocol.step state ⟨joint, legal⟩).support) :
    setup.attemptPublicRecall who (trace.extend joint legal reached) =
      setup.attemptPublicSignal who target :: setup.attemptPublicRecall who trace := by
  rw [attemptPublicRecall, InfoSignals.infoOf_extend]
  rfl

private theorem publicRecall_length (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.attemptPublicRecall who trace).length = trace.length + 1 := by
  induction trace with
  | start => rfl
  | extend earlier joint legal reached ih =>
      rw [setup.publicRecall_extend, List.length_cons, ih]
      rfl

private theorem state_some_of_prefix
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    {state : setup.commitRecoveryProtocol.State} (trace : setup.commitRecoveryProtocol.Trace state)
    (retained : TracePrefix prior trace) : ∃ current, state = some current := by
  induction retained with
  | refl => exact ⟨first, rfl⟩
  | @extend source target earlier kept joint legal reached ih =>
      obtain ⟨current, rfl⟩ := ih
      obtain ⟨next, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      exact ⟨next, rfl⟩

private theorem information_extend_congr (who : Player)
    {leftSource leftTarget rightSource rightTarget : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace leftSource)
    (right : setup.commitRecoveryProtocol.Trace rightSource)
    (leftJoint rightJoint : Player → Option (CommitRecoveryMove Player L))
    (leftLegal : setup.commitRecoveryProtocol.Legal leftSource leftJoint)
    (rightLegal : setup.commitRecoveryProtocol.Legal rightSource rightJoint)
    (leftSupport : leftTarget ∈
      (setup.commitRecoveryProtocol.step leftSource ⟨leftJoint, leftLegal⟩).support)
    (rightSupport : rightTarget ∈
      (setup.commitRecoveryProtocol.step rightSource ⟨rightJoint, rightLegal⟩).support)
    (before : setup.commitRecoveryModel.infoOf who left =
      setup.commitRecoveryModel.infoOf who right)
    (ownChoice : leftJoint who = rightJoint who)
    (signal : (setup.commitRecoveryPrivate who leftTarget,
        setup.commitRecoveryPublic leftTarget) =
      (setup.commitRecoveryPrivate who rightTarget, setup.commitRecoveryPublic rightTarget)) :
    setup.commitRecoveryModel.infoOf who (left.extend leftJoint leftLegal leftSupport) =
      setup.commitRecoveryModel.infoOf who (right.extend rightJoint rightLegal rightSupport) := by
  change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _ =
    setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _
  change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who left =
    setup.commitRecoverySignals.withOwnPlayRecall.infoOf who right at before
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at before ⊢
  have base := congrArg Prod.fst before
  have record := congrArg Prod.snd before
  dsimp only at base record
  apply Prod.ext
  · rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend]
    change ((setup.commitRecoveryPrivate who leftTarget,
      setup.commitRecoveryPublic leftTarget), _) =
      ((setup.commitRecoveryPrivate who rightTarget, setup.commitRecoveryPublic rightTarget), _)
    rw [signal, base]
  · rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend, ownChoice]
    cases rightJoint who with
    | none => exact record
    | some action => exact congrArg₂ List.cons (congrArg (fun info => (info, action)) base) record

private theorem source_records_determine_observer (who : Player)
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (publicWord : setup.attemptPublicRecall who leftTrace =
      setup.attemptPublicRecall who rightTrace)
    (coordinate : (setup.recoveryJointRecall leftTrace).map (fun joint => joint who) =
      (setup.recoveryJointRecall rightTrace).map (fun joint => joint who)) :
    ∃ left right : CommitRecoveryState setup.program,
      leftState = some left ∧ rightState = some right ∧
      (ProtocolState.observe who setup.program left.point,
        ProtocolState.observe who setup.program left.saved,
        left.excluded, left.entryExcluded, left.generation) =
      (ProtocolState.observe who setup.program right.point,
        ProtocolState.observe who setup.program right.saved,
        right.excluded, right.entryExcluded, right.generation) ∧
      setup.commitRecoveryModel.infoOf who leftTrace =
        setup.commitRecoveryModel.infoOf who rightTrace := by
  have clock : leftTrace.length = rightTrace.length := by
    have lengths := congrArg List.length coordinate
    simpa only [List.length_map, setup.jointRecall_length] using lengths
  induction leftRetained generalizing rightState with
  | refl =>
      have equal := rightRetained.eq_of_length clock
      cases equal
      exact ⟨first, first, rfl, rfl, rfl, rfl⟩
  | @extend source target earlier kept joint legal reached ih =>
      cases rightRetained with
      | refl =>
          have lower := kept.length_le
          simp only [Trace.length] at clock
          omega
      | @extend rightSource rightTarget rightEarlier rightKept rightJoint rightLegal rightReached =>
          have publicPair := List.cons.inj (by
            simpa only [setup.publicRecall_extend] using publicWord)
          have coordinates := List.cons.inj (by
            simpa only [recoveryJointRecall, List.map_cons] using coordinate)
          have previousClock : earlier.length = rightEarlier.length := by
            simpa only [Trace.length, Nat.add_left_inj] using clock
          obtain ⟨left, right, rfl, rfl, before, beforeInfo⟩ :=
            ih rightEarlier rightKept publicPair.2 coordinates.2 previousClock
          obtain ⟨leftNext, leftNextSupport, rfl⟩ :=
            (PMF.mem_support_map_iff _ _ _).mp reached
          obtain ⟨rightNext, rightNextSupport, rfl⟩ :=
            (PMF.mem_support_map_iff _ _ _).mp rightReached
          have after := setup.commitRecovery_step_observed_eq who left right earlier rightEarlier
            (congrArg Prod.fst before) (congrArg (fun x => x.2.1) before)
            (congrArg (fun x => x.2.2.1) before)
            (congrArg (fun x => x.2.2.2.1) before)
            (congrArg (fun x => x.2.2.2.2) before)
            joint rightJoint coordinates.1 leftNext rightNext leftNextSupport rightNextSupport
            publicPair.1
          refine ⟨leftNext, rightNext, rfl, rfl, after, ?_⟩
          apply setup.information_extend_congr who earlier rightEarlier joint rightJoint
            legal rightLegal reached rightReached beforeInfo coordinates.1
          have privateEqual : setup.commitRecoveryPrivate who (some leftNext) =
              setup.commitRecoveryPrivate who (some rightNext) :=
            congrArg some (congrArg Prod.fst after)
          have publicEqual : setup.commitRecoveryPublic (some leftNext) =
              setup.commitRecoveryPublic (some rightNext) :=
            congrArg (fun signal => signal.2) publicPair.1
          exact Prod.ext privateEqual publicEqual

/-- From the literal original setup prefix, the public source chronology
and the observer's actual raw coordinate word determine its ENTIRE original
perfect-recall information. All phases, retries and exhausted advances are
included; no prior or final private-information equality is assumed. -/
theorem commitRecovery_info_eq_of_public_and_coordinate (who : Player)
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (publicWord : setup.attemptPublicRecall who leftTrace =
      setup.attemptPublicRecall who rightTrace)
    (coordinate : (setup.recoveryJointRecall leftTrace).map (fun joint => joint who) =
      (setup.recoveryJointRecall rightTrace).map (fun joint => joint who)) :
    setup.commitRecoveryModel.infoOf who leftTrace =
      setup.commitRecoveryModel.infoOf who rightTrace := by
  obtain ⟨_, _, _, _, _, information⟩ := setup.source_records_determine_observer who first prior
    leftTrace rightTrace leftRetained rightRetained publicWord coordinate
  exact information

/-- The global record substitution has a genuine inverse: the SAME original
setup prefix, complete raw joint word and public sample word identify the
entire canonical source History, including every remembered retired choice.
This is equality of original histories, not only of retained semantic states. -/
theorem commitRecovery_history_eq_of_public_and_joints (who : Player)
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (publicWord : setup.attemptPublicRecall who leftTrace =
      setup.attemptPublicRecall who rightTrace)
    (joints : setup.recoveryJointRecall leftTrace = setup.recoveryJointRecall rightTrace) :
    (⟨leftState, leftTrace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨rightState, rightTrace⟩ := by
  have clock : leftTrace.length = rightTrace.length := by
    have lengths := congrArg List.length joints
    simpa only [setup.jointRecall_length] using lengths
  induction leftRetained generalizing rightState with
  | refl =>
      have equal := rightRetained.eq_of_length clock
      cases equal
      rfl
  | @extend source target earlier kept joint legal reached ih =>
      cases rightRetained with
      | refl =>
          have lower := kept.length_le
          simp only [Trace.length] at clock
          omega
      | @extend rightSource rightTarget rightEarlier rightKept rightJoint rightLegal rightReached =>
          have publicPair := List.cons.inj (by
            simpa only [setup.publicRecall_extend] using publicWord)
          have jointPair := List.cons.inj joints
          have previousClock : earlier.length = rightEarlier.length := by
            simpa only [Trace.length, Nat.add_left_inj] using clock
          have before := ih rightEarlier rightKept publicPair.2 jointPair.2 previousClock
          cases before
          cases jointPair.1
          obtain ⟨current, rfl⟩ := setup.state_some_of_prefix first prior earlier kept
          obtain ⟨leftNext, leftNextSupport, rfl⟩ :=
            (PMF.mem_support_map_iff _ _ _).mp reached
          obtain ⟨rightNext, rightNextSupport, rfl⟩ :=
            (PMF.mem_support_map_iff _ _ _).mp rightReached
          have next := setup.commitRecovery_step_eq_of_public who current earlier joint
            leftNext rightNext leftNextSupport rightNextSupport publicPair.1
          cases next
          rfl

variable [Fintype Player]

/-- Global original source counterfactual density: preserving the genuine
setup draw, complete public source word and each nonfocal raw coordinate
preserves EVERY opponent and Nature factor. There is no commitment-window
bound, erased endpoint premise, intendedness assumption or desired density
factor. All accepted failures, retired words and later source phases remain. -/
theorem commitRecovery_counterfactual_reach_eq_of_public_and_coordinates
    (strategy : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (publicWord : ∀ who, setup.attemptPublicRecall who leftTrace =
      setup.attemptPublicRecall who rightTrace)
    (coordinates : ∀ who, who ≠ focal →
      (setup.recoveryJointRecall leftTrace).map (fun joint => joint who) =
        (setup.recoveryJointRecall rightTrace).map (fun joint => joint who)) :
    setup.commitRecoveryModel.counterfactualReachProbability strategy focal leftTrace =
      setup.commitRecoveryModel.counterfactualReachProbability strategy focal rightTrace := by
  classical
  have clock : leftTrace.length = rightTrace.length := by
    have lengths := congrArg List.length (publicWord focal)
    simpa only [setup.publicRecall_length, Nat.add_left_inj] using lengths
  induction leftRetained generalizing rightState with
  | refl =>
      have equal := rightRetained.eq_of_length clock
      cases equal
      rfl
  | @extend source target earlier kept joint legal reached ih =>
      cases rightRetained with
      | refl =>
          have lower := kept.length_le
          simp only [Trace.length] at clock
          omega
      | @extend rightSource rightTarget rightEarlier rightKept rightJoint rightLegal rightReached =>
          have publicPair who := List.cons.inj (by
            simpa only [setup.publicRecall_extend] using publicWord who)
          have coordinatePair who (nonfocal : who ≠ focal) := List.cons.inj (by
            simpa only [recoveryJointRecall, List.map_cons] using coordinates who nonfocal)
          have previousPublic who := (publicPair who).2
          have previousCoordinates who nonfocal := (coordinatePair who nonfocal).2
          have previousClock : earlier.length = rightEarlier.length := by
            simpa only [Trace.length, Nat.add_left_inj] using clock
          have previous := ih rightEarlier rightKept previousPublic previousCoordinates
            previousClock
          obtain ⟨left, rfl⟩ := setup.state_some_of_prefix first prior earlier kept
          obtain ⟨right, rfl⟩ := setup.state_some_of_prefix first prior rightEarlier rightKept
          obtain ⟨leftNext, leftNextSupport, rfl⟩ :=
            (PMF.mem_support_map_iff _ _ _).mp reached
          obtain ⟨rightNext, rightNextSupport, rfl⟩ :=
            (PMF.mem_support_map_iff _ _ _).mp rightReached
          have nature := setup.commitRecovery_step_mass_eq_of_public focal left right earlier
            rightEarlier (previousPublic focal) joint rightJoint leftNext rightNext
            leftNextSupport rightNextSupport (publicPair focal).1
          have leftMass : setup.commitRecoveryProtocol.step (some left) ⟨joint, legal⟩
              (some leftNext) = left.step joint leftNext :=
            pmf_map_apply_of_injective (left.step joint) (Option.some_injective _) leftNext
          have rightMass : setup.commitRecoveryProtocol.step (some right) ⟨rightJoint, rightLegal⟩
              (some rightNext) = right.step rightJoint rightNext :=
            pmf_map_apply_of_injective (right.step rightJoint) (Option.some_injective _) rightNext
          have stepEqual : setup.commitRecoveryModel.counterfactualStepProb strategy focal earlier
                ⟨joint, legal⟩ (some leftNext) =
              setup.commitRecoveryModel.counterfactualStepProb strategy focal rightEarlier
                ⟨rightJoint, rightLegal⟩ (some rightNext) := by
            unfold InformationModel.counterfactualStepProb
            rw [leftMass, rightMass, nature]
            apply congrArg (fun probability =>
              probability * (right.step rightJoint rightNext).toReal)
            unfold InformationModel.opponentsStepProb
            apply Finset.prod_congr rfl
            intro who member
            have nonfocal := (Finset.mem_erase.mp member).1
            have sameInfo := setup.commitRecovery_info_eq_of_public_and_coordinate who first prior
              earlier rightEarlier kept rightKept (previousPublic who)
              (previousCoordinates who nonfocal)
            have sameChoice := (coordinatePair who nonfocal).1
            have leftRaw := pmf_map_apply_of_injective
              (f := fun choice : setup.commitRecoveryModel.Choice who
                (setup.commitRecoveryModel.infoOf who earlier) => choice.val)
              (strategy who (setup.commitRecoveryModel.infoOf who earlier)) Subtype.val_injective
              (setup.commitRecoveryModel.choicesOfLegal earlier ⟨joint, legal⟩ who)
            have rightRaw := pmf_map_apply_of_injective
              (f := fun choice : setup.commitRecoveryModel.Choice who
                (setup.commitRecoveryModel.infoOf who rightEarlier) => choice.val)
              (strategy who (setup.commitRecoveryModel.infoOf who rightEarlier))
              Subtype.val_injective
              (setup.commitRecoveryModel.choicesOfLegal rightEarlier ⟨rightJoint, rightLegal⟩ who)
            have rawLaw := congrArg (fun info => (strategy who info).map Subtype.val) sameInfo
            apply congrArg ENNReal.toReal
            rw [← leftRaw, ← rightRaw]
            change ((strategy who (setup.commitRecoveryModel.infoOf who earlier)).map Subtype.val)
                (joint who) =
              ((strategy who (setup.commitRecoveryModel.infoOf who rightEarlier)).map Subtype.val)
                (rightJoint who)
            rw [rawLaw, sameChoice]
          change setup.commitRecoveryModel.counterfactualReachProbability strategy focal earlier *
              setup.commitRecoveryModel.counterfactualStepProb strategy focal earlier
                ⟨joint, legal⟩ (some leftNext) =
            setup.commitRecoveryModel.counterfactualReachProbability strategy focal rightEarlier *
              setup.commitRecoveryModel.counterfactualStepProb strategy focal rightEarlier
                ⟨rightJoint, rightLegal⟩ (some rightNext)
          rw [previous, stepEqual]

/-- The global history densities have exactly the original focal own-record
ratio. This form remains valid at zero reach and needs no Bayes denominator. -/
theorem commitRecovery_reach_cross_mul_eq_of_public_and_coordinates
    (strategy : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (focal : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (publicWord : ∀ who, setup.attemptPublicRecall who leftTrace =
      setup.attemptPublicRecall who rightTrace)
    (coordinates : ∀ who, who ≠ focal →
      (setup.recoveryJointRecall leftTrace).map (fun joint => joint who) =
        (setup.recoveryJointRecall rightTrace).map (fun joint => joint who)) :
    (setup.commitRecoveryModel.historyReachWeight strategy ⟨leftState, leftTrace⟩).toReal *
        setup.commitRecoveryModel.playerReachProbability strategy focal rightTrace =
      (setup.commitRecoveryModel.historyReachWeight strategy ⟨rightState, rightTrace⟩).toReal *
        setup.commitRecoveryModel.playerReachProbability strategy focal leftTrace := by
  have counterfactual := setup.commitRecovery_counterfactual_reach_eq_of_public_and_coordinates
    strategy focal first prior leftTrace rightTrace leftRetained rightRetained
      publicWord coordinates
  rw [setup.commitRecoveryModel.historyReachProbability_eq_player_mul_counterfactual,
    setup.commitRecoveryModel.historyReachProbability_eq_player_mul_counterfactual, counterfactual]
  ring

end Vegas.SourceProgram.Setup
