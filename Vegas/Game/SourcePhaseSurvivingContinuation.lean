/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePhaseObservation
import Vegas.Game.CommitRecoveryHiddenInformation
import Vegas.Source.CommitRecoveryOwnHistory
import Vegas.Source.CommitRecoveryObservedClosure
import Vegas.Source.CommitRecoveryErasedContinuation

/-! # Source continuation laws from surviving players' full information

The original source policies have the same continuation observation law when
saved and live semantic states agree and every surviving player's full source
information agrees. Excluded players cannot act. No initial-prior independence
or restriction of policies to erased information is needed.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem private_of_info_eq (who : Player)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace leftState)
    (right : setup.commitRecoveryProtocol.Trace rightState)
    (same : setup.commitRecoveryModel.infoOf who left =
      setup.commitRecoveryModel.infoOf who right) :
    setup.commitRecoveryPrivate who leftState = setup.commitRecoveryPrivate who rightState := by
  have current (state : setup.commitRecoveryProtocol.State)
      (trace : setup.commitRecoveryProtocol.Trace state) :
      (setup.commitRecoveryModel.infoOf who trace).1.1.1 =
        setup.commitRecoveryPrivate who state := by
    change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace).1.1.1 = _
    rw [InfoSignals.withOwnPlayRecall_infoOf]
    exact congrArg Prod.fst (setup.commitRecoverySignals_current who trace)
  exact (current _ left).symm.trans
    ((congrArg (fun info => info.1.1.1) same).trans (current _ right))

/-- An actual source step with the same joint choice and semantic successor
preserves every surviving player's complete signals and own-play recall. -/
theorem commitRecovery_surviving_information_step
    (first second leftNext rightNext : CommitRecoveryState setup.program)
    (left : setup.commitRecoveryProtocol.Trace (some first))
    (right : setup.commitRecoveryProtocol.Trace (some second))
    (leftJoint rightJoint : Player → Option (CommitRecoveryMove Player L))
    (leftLegal : setup.commitRecoveryProtocol.Legal (some first) leftJoint)
    (rightLegal : setup.commitRecoveryProtocol.Legal (some second) rightJoint)
    (leftReached : some leftNext ∈
      (setup.commitRecoveryProtocol.step (some first) ⟨leftJoint, leftLegal⟩).support)
    (rightReached : some rightNext ∈
      (setup.commitRecoveryProtocol.step (some second) ⟨rightJoint, rightLegal⟩).support)
    (before : ∀ who, who ∉ first.excluded →
      setup.commitRecoveryModel.infoOf who left = setup.commitRecoveryModel.infoOf who right)
    (choices : leftJoint = rightJoint)
    (semantic : leftNext.eraseHistory = rightNext.eraseHistory) :
    ∀ who, who ∉ leftNext.excluded →
      setup.commitRecoveryModel.infoOf who (left.extend leftJoint leftLegal leftReached) =
        setup.commitRecoveryModel.infoOf who (right.extend rightJoint rightLegal rightReached) := by
  have leftSupport : leftNext ∈ (first.step leftJoint).support := by
    obtain ⟨next, supported, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp leftReached
    cases Option.some.inj equal
    exact supported
  have rightSupport : rightNext ∈ (second.step rightJoint).support := by
    obtain ⟨next, supported, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp rightReached
    cases Option.some.inj equal
    exact supported
  have exclusions : leftNext.excluded = rightNext.excluded := congrArg (·.excluded) semantic
  have publicControl : setup.commitRecoveryPublic (some leftNext) =
      setup.commitRecoveryPublic (some rightNext) := by
    have same := congrArg (fun state => setup.commitRecoveryPublic (some state)) semantic
    simpa only [commitRecoveryPublic, CommitRecoveryState.eraseHistory,
      ProtocolState.remaining_withHistory] using same
  intro who survives
  have oldSurvives : who ∉ first.excluded := fun excluded =>
    survives (first.step_excluded_monotone leftJoint leftNext leftSupport excluded)
  have otherSurvives : who ∉ rightNext.excluded := exclusions ▸ survives
  have oldInfo := before who oldSurvives
  have oldView : ProtocolState.observe who setup.program first.point =
      ProtocolState.observe who setup.program second.point :=
    Option.some.inj (setup.private_of_info_eq who left right oldInfo)
  have words : ProtocolState.history setup.program leftNext.point who =
      ProtocolState.history setup.program rightNext.point who := by
    rw [first.step_own_history who leftJoint leftLegal.2 leftNext leftSupport survives,
      second.step_own_history who rightJoint rightLegal.2 rightNext rightSupport otherSurvives,
      choices, ProtocolState.history_eq_of_observe who setup.program _ _ oldView]
  have nextView : ProtocolState.observe who setup.program leftNext.point =
      ProtocolState.observe who setup.program rightNext.point := by
    have points := congrArg (·.point) semantic
    change ProtocolState.withHistory setup.program leftNext.point (fun _ => []) =
      ProtocolState.withHistory setup.program rightNext.point (fun _ => []) at points
    have sameView := ProtocolState.observe_withHistory_congr who setup.program _ _
      (ProtocolState.history setup.program leftNext.point)
      (ProtocolState.history setup.program rightNext.point) (congrArg
        (ProtocolState.observe who setup.program) points) words
    simpa only [ProtocolState.withHistory_withHistory,
      ProtocolState.withHistory_history] using sameView
  exact setup.commitRecovery_info_extend_eq who ⟨some first, left⟩ ⟨some second, right⟩
    leftJoint rightJoint leftLegal rightLegal (some leftNext) (some rightNext) leftReached
      rightReached oldInfo (congrFun choices who) (congrArg some nextView) publicControl

end Vegas.SourceProgram.Setup

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem bindOnSupport_same_summary {A B C D : Type*}
    (left : PMF A) (right : PMF B) (first : A → C) (second : B → C)
    (same : left.map first = right.map second)
    (leftNext : ∀ point ∈ left.support, PMF D)
    (rightNext : ∀ point ∈ right.support, PMF D)
    (agree : ∀ a ha b hb, first a = second b → leftNext a ha = rightNext b hb) :
    left.bindOnSupport leftNext = right.bindOnSupport rightNext := by
  classical
  let totalLeft a := if ha : a ∈ left.support then leftNext a ha
    else leftNext left.support_nonempty.choose left.support_nonempty.choose_spec
  let totalRight b := if hb : b ∈ right.support then rightNext b hb
    else rightNext right.support_nonempty.choose right.support_nonempty.choose_spec
  have leftAgrees : ∀ a ha, leftNext a ha = totalLeft a := by
    intro a ha
    simp only [totalLeft, dite_eq_left ha]
  have rightAgrees : ∀ b hb, rightNext b hb = totalRight b := by
    intro b hb
    simp only [totalRight, dite_eq_left hb]
  rw [bindOnSupport_eq_bind_of_eq_on_support left leftAgrees,
    bindOnSupport_eq_bind_of_eq_on_support right rightAgrees]
  apply bind_eq_of_map_eq left right first second same
  intro a ha b hb equal
  rw [← leftAgrees a ha, ← rightAgrees b hb]
  exact agree a ha b hb equal

private theorem inactive_choice_law (who : Player)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History)
    (inactive : ¬ setup.commitRecoveryProtocol.active history.state who) :
    (profile who (setup.commitRecoveryModel.infoOf who history.trace)).map Subtype.val =
      PMF.pure none := by
  have forced : ∀ choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryModel.infoOf who history.trace), choice.1 = none := by
    intro choice
    exact LegalOption.eq_none_of_inactive choice.1
      ((setup.commitRecoveryModel.menu_adequate who history.trace choice.1).mp choice.2) inactive
  calc
    _ = (profile who (setup.commitRecoveryModel.infoOf who history.trace)).map
        (fun _ => none) := congrArg (fun f => PMF.map f
          (profile who (setup.commitRecoveryModel.infoOf who history.trace))) (funext forced)
    _ = _ := PMF.map_const _ _

/-- Surviving players use identical original policy coordinates; every
excluded player's legal choice is forced silence. -/
theorem commitRecovery_surviving_joint_law [Fintype Player]
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (first second : CommitRecoveryState setup.program)
    (left : setup.commitRecoveryProtocol.Trace (some first))
    (right : setup.commitRecoveryProtocol.Trace (some second))
    (leftRunning : ¬ setup.commitRecoveryProtocol.terminal (some first))
    (rightRunning : ¬ setup.commitRecoveryProtocol.terminal (some second))
    (semantic : first.eraseHistory = second.eraseHistory)
    (information : ∀ who, who ∉ first.excluded →
      setup.commitRecoveryModel.infoOf who left = setup.commitRecoveryModel.infoOf who right) :
    (setup.commitRecoveryModel.behavioralJoint profile left leftRunning).map Subtype.val =
      (setup.commitRecoveryModel.behavioralJoint profile right rightRunning).map Subtype.val := by
  classical
  rw [setup.commitRecoveryModel.behavioralJoint_map_val,
    setup.commitRecoveryModel.behavioralJoint_map_val]
  apply congrArg independentProduct
  funext who
  by_cases excluded : who ∈ first.excluded
  · have other : who ∈ second.excluded := (congrArg (·.excluded) semantic) ▸ excluded
    rw [setup.inactive_choice_law who profile ⟨some first, left⟩ (fun active => active.2 excluded),
      setup.inactive_choice_law who profile ⟨some second, right⟩ (fun active => active.2 other)]
  · exact congrArg (fun info => (profile who info).map Subtype.val) (information who excluded)

/-- Erasing remembered words only in the readout gives equal continuation laws
under arbitrary original policies, with survivor information retained in the proof. -/
theorem commitRecovery_surviving_continuation [Fintype Player]
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ (fuel : Nat) (first second : CommitRecoveryState setup.program)
      (left : setup.commitRecoveryProtocol.Trace (some first))
      (right : setup.commitRecoveryProtocol.Trace (some second)),
      first.eraseHistory = second.eraseHistory →
      (∀ who, who ∉ first.excluded →
        setup.commitRecoveryModel.infoOf who left = setup.commitRecoveryModel.infoOf who right) →
      (setup.commitRecoveryModel.runBehavioralFrom profile fuel ⟨some first, left⟩).map
          (fun history => history.state.map CommitRecoveryState.eraseHistory) =
        (setup.commitRecoveryModel.runBehavioralFrom profile fuel ⟨some second, right⟩).map
          (fun history => history.state.map CommitRecoveryState.eraseHistory) := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro first second left right semantic _
      simpa only [InformationModel.runBehavioralFrom, ExecutionProtocol.runRandomizedFor,
        PMF.pure_map, Option.map_some] using congrArg (fun state => PMF.pure (some state)) semantic
  | succ fuel ih =>
      intro first second left right semantic information
      have terminal := setup.commitRecovery_terminal_eq_of_erased
        (first := some first) (second := some second) (congrArg some semantic)
      by_cases stopped : setup.commitRecoveryProtocol.terminal (some first)
      · rw [setup.commitRecoveryModel.runBehavioralFrom_of_terminal profile _ stopped,
          setup.commitRecoveryModel.runBehavioralFrom_of_terminal profile _ (terminal.mp stopped),
          PMF.pure_map, PMF.pure_map]
        exact congrArg (fun state => PMF.pure (some state)) semantic
      have otherRunning : ¬ setup.commitRecoveryProtocol.terminal (some second) :=
        fun ended => stopped (terminal.mpr ended)
      rw [setup.commitRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile fuel stopped,
        setup.commitRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile fuel otherRunning,
        PMF.map_bind, PMF.map_bind]
      apply bind_eq_of_map_eq _ _ Subtype.val Subtype.val
        (setup.commitRecovery_surviving_joint_law profile first second left right stopped
          otherRunning semantic information)
      rintro ⟨choice, legal⟩ _ ⟨other, otherLegal⟩ _ sameChoice
      change choice = other at sameChoice
      subst other
      rw [map_bindOnSupport, map_bindOnSupport]
      change ((first.step choice).map some).bindOnSupport _ =
        ((second.step choice).map some).bindOnSupport _
      rw [bindOnSupport_map, bindOnSupport_map]
      apply bindOnSupport_same_summary _ _ CommitRecoveryState.eraseHistory
        CommitRecoveryState.eraseHistory
      · rw [← first.step_eraseHistory choice, ← second.step_eraseHistory choice, semantic]
      · intro nextLeft supportedLeft nextRight supportedRight sameNext
        apply ih nextLeft nextRight _ _ sameNext
        exact setup.commitRecovery_surviving_information_step first second nextLeft nextRight
          left right choice choice legal otherLegal
          ((PMF.mem_support_map_iff _ _ _).mpr ⟨nextLeft, supportedLeft, rfl⟩)
          ((PMF.mem_support_map_iff _ _ _).mpr ⟨nextRight, supportedRight, rfl⟩)
          information rfl sameNext

/-- The complete typed terminal readout and declared cash vector have the same
continuation law. History-dependent valuation still needs its separate factorization. -/
theorem sourcePhaseObservation_surviving_continuation [Fintype Player]
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (fuel : Nat) (first second : CommitRecoveryState setup.program)
    (left : setup.commitRecoveryProtocol.Trace (some first))
    (right : setup.commitRecoveryProtocol.Trace (some second))
    (semantic : first.eraseHistory = second.eraseHistory)
    (information : ∀ who, who ∉ first.excluded →
      setup.commitRecoveryModel.infoOf who left = setup.commitRecoveryModel.infoOf who right) :
    (setup.commitRecoveryModel.runBehavioralFrom profile fuel ⟨some first, left⟩).map
        setup.sourcePhaseObservation =
      (setup.commitRecoveryModel.runBehavioralFrom profile fuel ⟨some second, right⟩).map
        setup.sourcePhaseObservation := by
  let read (state : setup.commitRecoveryProtocol.State) :=
    TerminalObservation.read setup
      (state.bind fun current => ProtocolState.readout setup.program current.point)
      (fun who => (setup.cash (state.elim ∅ (·.excluded))
        (state.bind fun current => ProtocolState.readout setup.program current.point) who : ℝ))
  have factor (history : setup.commitRecoveryProtocol.History) :
      setup.sourcePhaseObservation history =
        read (history.state.map CommitRecoveryState.eraseHistory) := by
    unfold sourcePhaseObservation sourcePhaseCash read
    cases state : history.state with
    | none => rfl
    | some current =>
        simp only [Option.map_some, Option.bind_some, Option.elim_some,
          CommitRecoveryState.eraseHistory, ProtocolState.readout_withHistory]
  have law := setup.commitRecovery_surviving_continuation profile fuel first second left right
    semantic information
  simpa only [PMF.map_comp, Function.comp_def, ← factor] using congrArg (PMF.map read) law

end Vegas.SourceProgram.Setup
