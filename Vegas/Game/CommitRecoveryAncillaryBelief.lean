/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryHybridHistory
import Vegas.Source.CommitRecoveryInitialInputs
import Vegas.Source.CommitRecoveryPublicObservation

/-! # Original source information fibers under retired-word substitution

An original full-information record retains every own raw coordinate,
including its inactive positions. This supplies the inverse on actual
source information fibers rather than only on selected complete traces.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem active_signal (who : Player) (state : setup.commitRecoveryProtocol.State) :
    setup.commitRecoveryActive who
        (setup.commitRecoveryPrivate who state, setup.commitRecoveryPublic state) =
      setup.commitRecoveryProtocol.active state who := by
  cases state with
  | none => rfl
  | some current =>
      simp only [commitRecoveryActive, commitRecoveryPrivate, commitRecoveryPublic,
        Option.map_some, Option.elim_some, ProtocolState.actor_observe_eq,
        commitRecoveryProtocol, CommitRecoveryState.Active]

/-- Full original source information determines the complete chronological
raw own coordinate, including omissions, accepted failures and inactive
positions. No sampled policy, intendedness or reset-memory erasure is used. -/
theorem commitRecovery_coordinate_eq_of_info_eq (who : Player)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (same : setup.commitRecoveryModel.infoOf who leftTrace =
      setup.commitRecoveryModel.infoOf who rightTrace) :
    (setup.recoveryJointRecall leftTrace).map (fun joint => joint who) =
      (setup.recoveryJointRecall rightTrace).map (fun joint => joint who) := by
  have clock : leftTrace.length = rightTrace.length := by
    have reduced := congrArg (setup.commitRecoveryErasedInformation who) same
    rw [← setup.commitRecoveryErasedModel_infoOf who leftTrace,
      ← setup.commitRecoveryErasedModel_infoOf who rightTrace] at reduced
    simpa only [setup.commitRecoveryErasedModel_word_length] using
      congrArg (fun info => info.1.2.length) reduced
  induction leftTrace generalizing rightState with
  | start =>
      cases rightTrace with
      | start => rfl
      | extend prior joint legal reached => simp only [Trace.length] at clock; omega
  | @extend leftSource leftTarget leftPrior leftJoint leftLegal leftReached ih =>
      cases rightTrace with
      | start => simp only [Trace.length] at clock; omega
      | @extend rightSource rightTarget rightPrior rightJoint rightLegal rightReached =>
          change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _ =
            setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _ at same
          rw [InfoSignals.withOwnPlayRecall_infoOf,
            InfoSignals.withOwnPlayRecall_infoOf] at same
          have base := congrArg Prod.fst same
          have own := congrArg Prod.snd same
          rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend] at base
          have past := List.cons.inj (congrArg Prod.snd base)
          have beforeBase : setup.commitRecoverySignals.infoOf who leftPrior =
              setup.commitRecoverySignals.infoOf who rightPrior := Prod.ext past.1 past.2
          have beforeSignal := congrArg Prod.fst beforeBase
          rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current]
            at beforeSignal
          have active : setup.commitRecoveryProtocol.active leftSource who =
              setup.commitRecoveryProtocol.active rightSource who := by
            rw [← setup.active_signal who leftSource, ← setup.active_signal who rightSource]
            exact congrArg (setup.commitRecoveryActive who) beforeSignal
          have leftOffered := setup.commitRecoveryProtocol.legalOption_of_legal leftLegal who
          have rightOffered := setup.commitRecoveryProtocol.legalOption_of_legal rightLegal who
          have previousClock : leftPrior.length = rightPrior.length := by
            simpa only [Trace.length, Nat.add_left_inj] using clock
          cases leftChoice : leftJoint who with
          | none =>
              have rightChoice : rightJoint who = none := by
                apply LegalOption.eq_none_of_inactive _ rightOffered
                rw [← active]
                simpa only [leftChoice, LegalOption] using leftOffered
              have beforeOwn : setup.commitRecoverySignals.ownPlay who leftPrior =
                  setup.commitRecoverySignals.ownPlay who rightPrior := by
                simpa only [InfoSignals.ownPlay_extend, leftChoice, rightChoice] using own
              have before : setup.commitRecoveryModel.infoOf who leftPrior =
                  setup.commitRecoveryModel.infoOf who rightPrior := by
                change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _ =
                  setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _
                rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf]
                exact Prod.ext beforeBase beforeOwn
              have earlier := ih rightPrior before previousClock
              simpa only [recoveryJointRecall, List.map_cons, leftChoice, rightChoice] using
                congrArg (List.cons none) earlier
          | some leftAction =>
              obtain ⟨rightAction, rightChoice⟩ : ∃ action, rightJoint who = some action := by
                cases chosen : rightJoint who with
                | some action => exact ⟨action, rfl⟩
                | none =>
                    have leftActive : setup.commitRecoveryProtocol.active leftSource who := by
                      have offered := leftOffered
                      rw [leftChoice] at offered
                      exact offered.1
                    have rightInactive : ¬ setup.commitRecoveryProtocol.active rightSource who := by
                      simpa only [chosen, LegalOption] using rightOffered
                    exact False.elim (rightInactive (Eq.mp active leftActive))
              rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend,
                leftChoice, rightChoice] at own
              have records := List.cons.inj own
              have actions : leftAction = rightAction := congrArg Prod.snd records.1
              have before : setup.commitRecoveryModel.infoOf who leftPrior =
                  setup.commitRecoveryModel.infoOf who rightPrior := by
                change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _ =
                  setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _
                rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf]
                exact Prod.ext beforeBase records.2
              have earlier := ih rightPrior before previousClock
              simpa only [recoveryJointRecall, List.map_cons, leftChoice, rightChoice,
                actions] using
                congrArg (List.cons (some rightAction)) earlier

/-- Equality of the actual erased source keys retains the whole true public
source record, including its original exclusions and retired attempts. -/
theorem commitRecovery_publicRecall_eq_of_erasedInformation_eq (who : Player)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (same : setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who leftTrace) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who rightTrace)) :
    setup.attemptPublicRecall who leftTrace = setup.attemptPublicRecall who rightTrace := by
  let project := fun information : setup.commitRecoveryModel.InfoState who =>
    (information.1.1 :: information.1.2).map fun signal =>
      (signal.1.map (ProtocolView.publicOnly who setup.program), signal.2)
  have projected {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state) :
      project (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who trace)) = setup.attemptPublicRecall who trace := by
    simp only [project, commitRecoveryErasedInformation, List.map_cons, List.map_map,
      Option.map_map, Function.comp_def, ProtocolView.publicOnly_eraseHistory,
      ProtocolView.publicOnly_idempotent, commitRecoveryModel,
      InfoSignals.withOwnPlayRecall_infoOf, attemptPublicRecall]
  exact (projected leftTrace).symm.trans ((congrArg project same).trans (projected rightTrace))

private theorem initialized_prefix {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    match state with
    | none => trace.length = 0
    | some _ => ∃ inputs : State L setup.context,
        ∃ prior : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
          (ProtocolState.entry setup.program (setup.initialConfig inputs)) ∅ 0)),
          prior.length = 1 ∧ TracePrefix prior trace := by
  induction trace with
  | start => rfl
  | @extend source target earlier joint legal reached ih =>
      cases source with
      | none =>
          obtain ⟨inputs, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          refine ⟨inputs, earlier.extend joint legal reached, ?_, .refl⟩
          change earlier.length + 1 = 1
          rw [ih]
      | some before =>
          obtain ⟨next, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          obtain ⟨inputs, prior, length, retained⟩ := ih
          exact ⟨inputs, prior, length, retained.extend joint legal reached⟩

/-- Actual equal erased source keys supply their own original setup witnesses
and the unique full-information exchange. No input equality, independent
entry posterior, selected prior or desired source-information equation is
assumed. The actual other-world setup draw and every Nature factor remain. -/
theorem commitRecovery_hybrid_of_erasedInformation_eq [Fintype Player]
    (strategy : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (focal : Player)
    (mine others : CommitRecoveryState setup.program)
    (mineTrace : setup.commitRecoveryProtocol.Trace (some mine))
    (othersTrace : setup.commitRecoveryProtocol.Trace (some others))
    (same : setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryModel.infoOf focal mineTrace) =
      setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryModel.infoOf focal othersTrace)) :
    ∃ input : State L setup.context,
      ∃ prior : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
        (ProtocolState.entry setup.program (setup.initialConfig input)) ∅ 0)),
      prior.length = 1 ∧ TracePrefix prior othersTrace ∧
      ∃! hybrid : setup.commitRecoveryProtocol.History,
        hybrid.state = some (CommitRecoveryState.splice focal mine others) ∧
        TracePrefix prior hybrid.trace ∧
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
          (setup.commitRecoveryModel.historyReachWeight strategy
            ⟨some others, othersTrace⟩).toReal *
            setup.commitRecoveryModel.playerReachProbability strategy focal hybrid.trace := by
  obtain ⟨mineInput, minePrior, mineLength, mineRetained⟩ := setup.initialized_prefix mineTrace
  obtain ⟨othersInput, othersPrior, othersLength, othersRetained⟩ :=
    setup.initialized_prefix othersTrace
  have query : setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal
          (setup.commitRecoveryModel.infoOf focal mineTrace)) =
      setup.commitRecoveryErasedInformation focal
        (setup.commitRecoveryNoMissInformation focal
          (setup.commitRecoveryModel.infoOf focal othersTrace)) := by
    rw [setup.commitRecoveryNoMissInformation_erased,
      setup.commitRecoveryNoMissInformation_erased, same]
  have inputs := setup.commitRecovery_initial_hiddenAgree_of_query_eq focal mineInput othersInput
    minePrior othersPrior mine others mineTrace othersTrace mineRetained othersRetained query
  have publicWord := setup.commitRecovery_publicRecall_eq_of_erasedInformation_eq focal
    mineTrace othersTrace same
  refine ⟨othersInput, othersPrior, othersLength, othersRetained, ?_⟩
  exact setup.commitRecovery_hybrid_of_initial_inputs strategy focal mineInput othersInput inputs
    minePrior othersPrior mineLength othersLength mine others mineTrace othersTrace
    mineRetained othersRetained (fun who => setup.attemptPublicRecall_eq_for_observer focal who
      mineTrace othersTrace publicWord)

end Vegas.SourceProgram.Setup
