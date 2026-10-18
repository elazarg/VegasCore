/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryClosedSupport
import Vegas.Game.CommitRecoveryGlobalWordDensity

/-! # Genuine source prefixes with one owner's original word substituted

The existing source traces are pasted instruction by instruction. Each new
joint is legal and its successor is supported by the original kernel.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem publicRecall_head (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.attemptPublicRecall who trace).head? = some (setup.attemptPublicSignal who state) := by
  simp only [attemptPublicRecall, List.map_cons, List.head?_cons,
    setup.commitRecoverySignals_current, attemptPublicSignal]

theorem commitRecovery_splice_public_control (focal : Player)
    (mine others : CommitRecoveryState setup.program) (metadata : mine.MetadataEq others) :
    setup.commitRecoveryPublic (some (CommitRecoveryState.splice focal mine others)) =
      setup.commitRecoveryPublic (some others) := by
  have saved := ProtocolState.MetadataEq.controls setup.program _ _
    (ProtocolState.splice_metadata_eq_others focal setup.program _ _ metadata.2.1)
  simp only [commitRecoveryPublic, CommitRecoveryState.splice, saved.1]

theorem commitRecovery_splice_public_signal (focal observer : Player)
    (mine others : CommitRecoveryState setup.program) (metadata : mine.MetadataEq others)
    (same : setup.attemptPublicSignal observer (some mine) =
      setup.attemptPublicSignal observer (some others)) :
    setup.attemptPublicSignal observer (some (CommitRecoveryState.splice focal mine others)) =
      setup.attemptPublicSignal observer (some others) := by
  apply Prod.ext
  · by_cases own : observer = focal
    · subst observer
      have before := Option.some.inj (congrArg Prod.fst same)
      have view := ProtocolState.splice_observe_self focal setup.program _ _ before
      change some (ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program
          (ProtocolState.splice focal setup.program mine.point others.point))) = _
      rw [view]
      exact congrArg Prod.fst same
    · have view := ProtocolState.splice_observe_other focal observer own setup.program _ _
        metadata.1
      change some (ProtocolView.publicOnly observer setup.program
        (ProtocolState.observe observer setup.program
          (ProtocolState.splice focal setup.program mine.point others.point))) = _
      rw [view]
      rfl
  · exact setup.commitRecovery_splice_public_control focal mine others metadata

theorem commitRecovery_splice_signal_self (focal : Player)
    (mine others : CommitRecoveryState setup.program) (metadata : mine.MetadataEq others)
    (same : setup.attemptPublicSignal focal (some mine) =
      setup.attemptPublicSignal focal (some others)) :
    (setup.commitRecoveryPrivate focal (some (CommitRecoveryState.splice focal mine others)),
        setup.commitRecoveryPublic (some (CommitRecoveryState.splice focal mine others))) =
      (setup.commitRecoveryPrivate focal (some mine), setup.commitRecoveryPublic (some mine)) := by
  have view := ProtocolState.splice_observe_self focal setup.program mine.point others.point
    (Option.some.inj (congrArg Prod.fst same))
  apply Prod.ext
  · exact congrArg some view
  · exact (setup.commitRecovery_splice_public_control focal mine others metadata).trans
      (congrArg Prod.snd same).symm

theorem commitRecovery_splice_signal_other (focal observer : Player) (foreign : observer ≠ focal)
    (mine others : CommitRecoveryState setup.program) (metadata : mine.MetadataEq others) :
    (setup.commitRecoveryPrivate observer (some (CommitRecoveryState.splice focal mine others)),
        setup.commitRecoveryPublic (some (CommitRecoveryState.splice focal mine others))) =
      (setup.commitRecoveryPrivate observer (some others),
        setup.commitRecoveryPublic (some others)) := by
  exact Prod.ext (congrArg some (ProtocolState.splice_observe_other focal observer foreign
    setup.program _ _ metadata.1))
      (setup.commitRecovery_splice_public_control focal mine others metadata)

theorem commitRecovery_splice_joint_legal (focal : Player)
    (mine others : CommitRecoveryState setup.program) (metadata : mine.MetadataEq others)
    (before : ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program mine.point) =
      ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program others.point))
    (left right : Player → Option (CommitRecoveryMove Player L))
    (leftLegal : setup.commitRecoveryProtocol.Legal (some mine) left)
    (rightLegal : setup.commitRecoveryProtocol.Legal (some others) right) :
    setup.commitRecoveryProtocol.Legal (some (CommitRecoveryState.splice focal mine others))
      (Function.update right focal (left focal)) := by
  have control := ProtocolState.MetadataEq.controls setup.program _ _
    (ProtocolState.splice_metadata_eq_others focal setup.program _ _ metadata.1)
  have running : ¬ setup.commitRecoveryProtocol.terminal
      (some (CommitRecoveryState.splice focal mine others)) := by
    intro terminal
    apply rightLegal.1
    change ProtocolState.terminal setup.program _ at terminal ⊢
    apply (ProtocolState.remaining_zero_iff_terminal setup.program _).mp
    rw [← control.1]
    exact (ProtocolState.remaining_zero_iff_terminal setup.program _).mpr terminal
  apply setup.commitRecoveryProtocol.legal_of_legalOption running
  intro who
  by_cases own : who = focal
  · subst who
    have view := ProtocolState.splice_observe_self focal setup.program _ _ before
    have actor : ProtocolState.actor setup.program
        (ProtocolState.splice focal setup.program mine.point others.point) =
        ProtocolState.actor setup.program mine.point := by
      rw [← ProtocolState.actor_observe_eq setup.program _ focal, view,
        ProtocolState.actor_observe_eq]
    have given := setup.commitRecoveryProtocol.legalOption_of_legal leftLegal focal
    simpa only [Function.update_self, LegalOption, commitRecoveryProtocol,
      CommitRecoveryState.Active, CommitRecoveryState.available, CommitRecoveryState.splice,
      Option.elim_some, actor, view, metadata.2.2.1] using given
  · have view := ProtocolState.splice_observe_other focal who own setup.program _ _ metadata.1
    have actor : ProtocolState.actor setup.program
        (ProtocolState.splice focal setup.program mine.point others.point) =
        ProtocolState.actor setup.program others.point := by
      rw [← ProtocolState.actor_observe_eq setup.program _ who, view,
        ProtocolState.actor_observe_eq]
    have given := setup.commitRecoveryProtocol.legalOption_of_legal rightLegal who
    simpa only [Function.update_of_ne own, LegalOption, commitRecoveryProtocol,
      CommitRecoveryState.Active, CommitRecoveryState.available, CommitRecoveryState.splice,
      Option.elim_some, actor, view] using given

private theorem splice_prefixes (focal : Player)
    (first second : CommitRecoveryState setup.program)
    (leftPrior : setup.commitRecoveryProtocol.Trace (some first))
    (rightPrior : setup.commitRecoveryProtocol.Trace (some second))
    (initialPaste : CommitRecoveryState.splice focal first second = second)
    (initialWord : setup.recoveryJointRecall leftPrior = setup.recoveryJointRecall rightPrior)
    (initialInformation : ∀ who,
      setup.attemptPublicRecall who leftPrior = setup.attemptPublicRecall who rightPrior →
      setup.commitRecoveryModel.infoOf who rightPrior =
        if who = focal then setup.commitRecoveryModel.infoOf who leftPrior
        else setup.commitRecoveryModel.infoOf who rightPrior)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix leftPrior leftTrace)
    (rightRetained : TracePrefix rightPrior rightTrace)
    (samePublic : ∀ who, setup.attemptPublicRecall who leftTrace =
      setup.attemptPublicRecall who rightTrace) :
    ∃ leftCurrent rightCurrent : CommitRecoveryState setup.program,
      leftState = some leftCurrent ∧ rightState = some rightCurrent ∧
      ∃ hybrid : setup.commitRecoveryProtocol.History,
      hybrid.state = some (CommitRecoveryState.splice focal leftCurrent rightCurrent) ∧
      TracePrefix rightPrior hybrid.trace ∧
      (∀ who, setup.attemptPublicRecall who hybrid.trace =
        setup.attemptPublicRecall who rightTrace) ∧
      (∀ who, (setup.recoveryJointRecall hybrid.trace).map (fun joint => joint who) =
        if who = focal then (setup.recoveryJointRecall leftTrace).map (fun joint => joint who)
        else (setup.recoveryJointRecall rightTrace).map (fun joint => joint who)) ∧
      (∀ who, setup.commitRecoveryModel.infoOf who hybrid.trace =
        if who = focal then setup.commitRecoveryModel.infoOf who leftTrace
        else setup.commitRecoveryModel.infoOf who rightTrace) := by
  have baseClock : leftPrior.length = rightPrior.length := by
    simpa only [setup.jointRecall_length] using congrArg List.length initialWord
  have clock : leftTrace.length = rightTrace.length := by
    simpa only [setup.publicRecall_length, Nat.add_left_inj] using
      congrArg List.length (samePublic focal)
  induction leftRetained generalizing rightState with
  | refl =>
      have equal := rightRetained.eq_of_length (baseClock.symm.trans clock)
      cases equal
      refine ⟨first, second, rfl, rfl, ⟨some second, rightPrior⟩,
        congrArg some initialPaste.symm, .refl, ?_, ?_, ?_⟩
      · intro who; rfl
      · intro who
        split
        · exact congrArg (List.map (fun joint => joint who)) initialWord.symm
        · rfl
      · exact fun who => initialInformation who (samePublic who)
  | @extend source target earlier kept joint legal reached ih =>
      cases rightRetained with
      | refl =>
          have lower := kept.length_le
          simp only [Trace.length] at clock
          omega
      | @extend rightSource rightTarget rightEarlier rightKept rightJoint rightLegal rightReached =>
          have publicPair who := List.cons.inj (by
            simpa only [setup.publicRecall_extend] using samePublic who)
          have previousClock : earlier.length = rightEarlier.length := by
            simpa only [Trace.length, Nat.add_left_inj] using clock
          obtain ⟨mine, others, rfl, rfl, hybridRecord, hybridShape, hybridKept, hybridPublic,
            hybridCoordinates, hybridInformation⟩ :=
            ih rightEarlier rightKept (fun who => (publicPair who).2) previousClock
          rcases hybridRecord with ⟨hybridState, hybrid⟩
          change hybridState = some (CommitRecoveryState.splice focal mine others) at hybridShape
          subst hybridState
          obtain ⟨leftNext, leftSupport, leftEq⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          obtain ⟨rightNext, rightSupport, rightEq⟩ :=
            (PMF.mem_support_map_iff _ _ _).mp rightReached
          cases leftEq
          cases rightEq
          have metadata := setup.commitRecovery_metadata_of_publicRecall focal earlier rightEarlier
            (publicPair focal).2
          have publicBefore := Option.some.inj (by
            simpa only [setup.publicRecall_head] using
              congrArg List.head? (publicPair focal).2)
          have before := Option.some.inj (congrArg Prod.fst publicBefore)
          have mixedLegal := setup.commitRecovery_splice_joint_legal
            focal mine others metadata before
            joint rightJoint legal rightLegal
          have mixedSupport := setup.commitRecovery_step_splice_support focal mine others earlier
            metadata before joint rightJoint leftNext rightNext leftSupport rightSupport
              (publicPair focal).1
          have supported : some (CommitRecoveryState.splice focal leftNext rightNext) ∈
              (setup.commitRecoveryProtocol.step
                (some (CommitRecoveryState.splice focal mine others))
                ⟨Function.update rightJoint focal (joint focal), mixedLegal⟩).support :=
            (PMF.mem_support_map_iff _ _ _).mpr ⟨_, mixedSupport, rfl⟩
          let newTrace := hybrid.extend _ mixedLegal supported
          refine ⟨leftNext, rightNext, rfl, rfl, ⟨_, newTrace⟩, rfl,
            hybridKept.extend _ mixedLegal supported, ?_, ?_, ?_⟩
          · intro who
            change setup.attemptPublicRecall who
                (hybrid.extend _ mixedLegal supported) = _
            rw [setup.publicRecall_extend, setup.publicRecall_extend, hybridPublic who]
            apply congrArg (fun head => head :: setup.attemptPublicRecall who rightEarlier)
            apply setup.commitRecovery_splice_public_signal focal who leftNext rightNext
            · exact setup.commitRecovery_metadata_of_publicRecall focal
                (earlier.extend joint legal reached)
                (rightEarlier.extend rightJoint rightLegal rightReached) (samePublic focal)
            · exact (publicPair who).1
          · intro who
            simp only [newTrace, recoveryJointRecall, List.map_cons]
            rw [hybridCoordinates who]
            by_cases own : who = focal
            · subst who
              simp only [Function.update_self, ↓reduceIte]
            · simp only [own, ↓reduceIte, Function.update_of_ne own]
          · intro who
            have nextMetadata := setup.commitRecovery_metadata_of_publicRecall focal
              (earlier.extend joint legal reached)
              (rightEarlier.extend rightJoint rightLegal rightReached) (samePublic focal)
            by_cases own : who = focal
            · subst who
              simp only [↓reduceIte]
              have previous : setup.commitRecoveryModel.infoOf focal hybrid =
                  setup.commitRecoveryModel.infoOf focal earlier := by
                simpa only [↓reduceIte] using hybridInformation focal
              exact setup.information_extend_congr focal hybrid earlier _ _ mixedLegal legal
                supported reached previous (Function.update_self ..)
                (setup.commitRecovery_splice_signal_self focal leftNext rightNext nextMetadata
                  (publicPair focal).1)
            · simp only [own, ↓reduceIte]
              apply setup.information_extend_congr who hybrid rightEarlier _ _ mixedLegal rightLegal
                supported rightReached
              · simpa only [own, ↓reduceIte] using hybridInformation who
              · exact Function.update_of_ne own ..
              · exact setup.commitRecovery_splice_signal_other
                  focal who own leftNext rightNext nextMetadata

private theorem initial_joint_word {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (length : trace.length = 1) :
    setup.recoveryJointRecall trace = [fun _ => none] := by
  cases trace with
  | start => simp only [Trace.length] at length; omega
  | @extend source target prior joint legal reached =>
      cases prior with
      | start =>
          have empty : joint = fun _ => none := by
            funext who
            exact LegalOption.eq_none_of_inactive (joint who)
              (setup.commitRecoveryProtocol.legalOption_of_legal legal who)
                (fun impossible => impossible)
          simp only [recoveryJointRecall, empty]
      | extend earlier joint legal reached =>
          simp only [Trace.length] at length
          omega

private theorem initial_information_congr (who : Player)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftLength : leftTrace.length = 1) (rightLength : rightTrace.length = 1)
    (signal : (setup.commitRecoveryPrivate who leftState, setup.commitRecoveryPublic leftState) =
      (setup.commitRecoveryPrivate who rightState, setup.commitRecoveryPublic rightState)) :
    setup.commitRecoveryModel.infoOf who leftTrace =
      setup.commitRecoveryModel.infoOf who rightTrace := by
  cases leftTrace with
  | start => simp only [Trace.length] at leftLength; omega
  | extend leftPrior leftJoint leftLegal leftReached =>
      cases leftPrior with
      | extend earlier joint legal reached => simp only [Trace.length] at leftLength; omega
      | start =>
          cases rightTrace with
          | start => simp only [Trace.length] at rightLength; omega
          | extend rightPrior rightJoint rightLegal rightReached =>
              cases rightPrior with
              | extend earlier joint legal reached =>
                  simp only [Trace.length] at rightLength; omega
              | start =>
                  apply setup.information_extend_congr who .start .start leftJoint rightJoint
                    leftLegal rightLegal leftReached rightReached rfl ?_ signal
                  have left := LegalOption.eq_none_of_inactive (leftJoint who)
                    (setup.commitRecoveryProtocol.legalOption_of_legal leftLegal who)
                      (fun impossible => impossible)
                  have right := LegalOption.eq_none_of_inactive (rightJoint who)
                    (setup.commitRecoveryProtocol.legalOption_of_legal rightLegal who)
                      (fun impossible => impossible)
                  exact left.trans right.symm

/-- Any two genuine source prefixes with the same public chronology can be
pasted from their ORIGINAL setup draws: one owner's complete raw word comes
from the first, every other coordinate and the actual setup draw from the
second. Only equality of that owner's original input tuple is required;
no independence of input coordinates or refreshed entry law is assumed. -/
theorem commitRecovery_hybrid_of_initial_inputs [Fintype Player]
    (strategy : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (focal : Player)
    (mineInput othersInput : State L setup.context)
    (inputAgree : HiddenAgree focal mineInput othersInput)
    (minePrior : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
      (ProtocolState.entry setup.program (setup.initialConfig mineInput)) ∅ 0)))
    (othersPrior : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
      (ProtocolState.entry setup.program (setup.initialConfig othersInput)) ∅ 0)))
    (mineInitial : minePrior.length = 1) (othersInitial : othersPrior.length = 1)
    (mine others : CommitRecoveryState setup.program)
    (mineTrace : setup.commitRecoveryProtocol.Trace (some mine))
    (othersTrace : setup.commitRecoveryProtocol.Trace (some others))
    (mineRetained : TracePrefix minePrior mineTrace)
    (othersRetained : TracePrefix othersPrior othersTrace)
    (samePublic : ∀ who, setup.attemptPublicRecall who mineTrace =
      setup.attemptPublicRecall who othersTrace) :
    ∃! hybrid : setup.commitRecoveryProtocol.History,
      hybrid.state = some (CommitRecoveryState.splice focal mine others) ∧
      TracePrefix othersPrior hybrid.trace ∧
      (∀ who, setup.attemptPublicRecall who hybrid.trace =
        setup.attemptPublicRecall who othersTrace) ∧
      (∀ who, (setup.recoveryJointRecall hybrid.trace).map (fun joint => joint who) =
        if who = focal then (setup.recoveryJointRecall mineTrace).map (fun joint => joint who)
        else (setup.recoveryJointRecall othersTrace).map (fun joint => joint who)) ∧
      setup.commitRecoveryModel.infoOf focal hybrid.trace =
        setup.commitRecoveryModel.infoOf focal mineTrace ∧
      (∀ who, who ≠ focal → setup.commitRecoveryModel.infoOf who hybrid.trace =
        setup.commitRecoveryModel.infoOf who othersTrace) ∧
      setup.commitRecoveryModel.counterfactualReachProbability strategy focal hybrid.trace =
        setup.commitRecoveryModel.counterfactualReachProbability strategy focal othersTrace ∧
      (setup.commitRecoveryModel.historyReachWeight strategy hybrid).toReal *
          setup.commitRecoveryModel.playerReachProbability strategy focal othersTrace =
        (setup.commitRecoveryModel.historyReachWeight strategy ⟨some others, othersTrace⟩).toReal *
          setup.commitRecoveryModel.playerReachProbability strategy focal hybrid.trace := by
  have configuration : Config.splice focal (setup.initialConfig mineInput)
        (setup.initialConfig othersInput) = setup.initialConfig othersInput := by
    unfold Config.splice initialConfig
    rw [splice_of_hiddenAgree inputAgree]
    congr 1
    exact Function.update_eq_self _ _
  have initialPaste : CommitRecoveryState.splice focal
      (CommitRecoveryState.atPoint (ProtocolState.entry setup.program
        (setup.initialConfig mineInput)) ∅ 0)
      (CommitRecoveryState.atPoint (ProtocolState.entry setup.program
        (setup.initialConfig othersInput)) ∅ 0) =
      CommitRecoveryState.atPoint (ProtocolState.entry setup.program
        (setup.initialConfig othersInput)) ∅ 0 := by
    rw [CommitRecoveryState.splice_atPoint, ProtocolState.splice_entry, configuration]
  have initialInformation who (publicWord : setup.attemptPublicRecall who minePrior =
      setup.attemptPublicRecall who othersPrior) :
      setup.commitRecoveryModel.infoOf who othersPrior =
        if who = focal then setup.commitRecoveryModel.infoOf who minePrior
        else setup.commitRecoveryModel.infoOf who othersPrior := by
    by_cases own : who = focal
    · subst who
      simp only [↓reduceIte]
      have metadata := setup.commitRecovery_metadata_of_publicRecall focal minePrior othersPrior
        publicWord
      have current := Option.some.inj (by
        simpa only [setup.publicRecall_head] using congrArg List.head? publicWord)
      have signal := setup.commitRecovery_splice_signal_self focal _ _ metadata current
      rw [initialPaste] at signal
      exact setup.initial_information_congr focal othersPrior minePrior
        othersInitial mineInitial signal
    · simp only [own, ↓reduceIte]
  obtain ⟨leftCurrent, rightCurrent, leftEq, rightEq, hybrid, shape, kept, publicWord,
    coordinates, information⟩ :=
    setup.splice_prefixes focal _ _ minePrior othersPrior initialPaste
      ((setup.initial_joint_word minePrior mineInitial).trans
        (setup.initial_joint_word othersPrior othersInitial).symm)
      initialInformation
      mineTrace othersTrace mineRetained othersRetained samePublic
  cases Option.some.inj leftEq
  cases Option.some.inj rightEq
  refine ⟨hybrid, ⟨shape, kept, publicWord, coordinates, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [↓reduceIte] using information focal
  · intro who foreign
    apply setup.commitRecovery_info_eq_of_public_and_coordinate who _ othersPrior
      hybrid.trace othersTrace kept othersRetained (publicWord who)
    simpa only [foreign, ↓reduceIte] using coordinates who
  · apply setup.commitRecovery_counterfactual_reach_eq_of_public_and_coordinates strategy focal
      _ othersPrior hybrid.trace othersTrace kept othersRetained publicWord
    intro who foreign
    simpa only [foreign, ↓reduceIte] using coordinates who
  · apply setup.commitRecovery_reach_cross_mul_eq_of_public_and_coordinates strategy focal
      _ othersPrior hybrid.trace othersTrace kept othersRetained publicWord
    intro who foreign
    simpa only [foreign, ↓reduceIte] using coordinates who
  · intro alternative satisfies
    have alternativeKept := satisfies.2.1
    have alternativePublic := satisfies.2.2.1
    have alternativeCoordinates := satisfies.2.2.2.1
    have wordEqual : setup.recoveryJointRecall alternative.trace =
        setup.recoveryJointRecall hybrid.trace := by
      have coordinateEqual who := (alternativeCoordinates who).trans (coordinates who).symm
      have lengths := congrArg List.length (coordinateEqual focal)
      simp only [List.length_map] at lengths
      apply List.ext_getElem lengths
      intro index alternativeInside hybridInside
      funext who
      have selected := congrArg (fun word => word[index]?) (coordinateEqual who)
      simpa only [List.getElem?_map, List.getElem?_eq_getElem alternativeInside,
        List.getElem?_eq_getElem hybridInside, Option.map_some, Option.some.injEq] using selected
    exact setup.commitRecovery_history_eq_of_public_and_joints focal _ othersPrior
      alternative.trace hybrid.trace alternativeKept kept
      ((alternativePublic focal).trans (publicWord focal).symm) wordEqual

end Vegas.SourceProgram.Setup
