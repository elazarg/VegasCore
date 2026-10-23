/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ExclusionGame

/-! # Mandatory moves before exclusion

The source move game offers every commitment value and requires opening at
reveals until an own event fails. Excluded players instead take only the
existing automatic failure actions. Guards retain their deferred checks.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every source view offers an inactive choice or a voluntary nonfailure move. -/
theorem ProtocolView.exists_move_menu (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (view : ProtocolView who program) →
      ∃ choice, ProtocolView.menu who program admission view choice ∧
        ∀ action, choice = some action → ¬ action.IsFailure
  | _, _, .ret _, _, _ =>
      ⟨none, by simp [ProtocolView.menu, ProtocolView.actor], fun _ chosen => by cases chosen⟩
  | _, _, .sample _ _ _ next, admission, view => by
      cases view with
      | inl _ => exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor],
          fun _ chosen => by cases chosen⟩
      | inr later => exact exists_move_menu who next admission later
  | _, _, .commit (payload := payload) name owner _ _ next, admission, view => by
      cases view with
      | inl _ =>
          by_cases own : owner = who
          · refine ⟨some (.commit owner name payload (.success (L.someValue payload))), ?_, ?_⟩
            · exact ⟨by simp [ProtocolView.actor, own], .success _, trivial, rfl⟩
            · rintro _ ⟨⟩
              simp [OwnAction.IsFailure]
          · exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor, own],
              fun _ chosen => by cases chosen⟩
      | inr later => exact exists_move_menu who next (fun site => admission (some site)) later
  | _, _, .reveal _ owner name _ _ _ next, admission, view => by
      cases view with
      | inl _ =>
          by_cases own : owner = who
          · refine ⟨some (.reveal owner name true), ?_, ?_⟩
            · exact ⟨by simp [ProtocolView.actor, own], true, rfl⟩
            · rintro _ ⟨⟩
              simp [OwnAction.IsFailure]
          · exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor, own],
              fun _ chosen => by cases chosen⟩
      | inr later => exact exists_move_menu who next admission later

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- Only excluded owners take failure actions; every other owner moves. -/
def exclusionMoveAvailable (state : setup.ProtocolState) (who : Player) :
    Set (OwnAction Player L) :=
  {action | action ∈ (setup.executionProtocol
      (CommitmentInterface.forfeiture setup.program)).available state who ∧
    (action.IsFailure ↔ setup.ExcludedState who state)}

/-- The observed menu of mandatory moves and automatic excluded failures. -/
def exclusionMoveSourceMenu (who : Player) (view : setup.ProtocolView who) :
    Set (Option (OwnAction Player L)) :=
  {choice | setup.protocolMenu (CommitmentInterface.forfeiture setup.program) who view choice ∧
    ∀ action, choice = some action → (action.IsFailure ↔ setup.ExcludedView who view)}

theorem exclusionMoveSourceMenu_nonempty (who : Player) (view : setup.ProtocolView who) :
    ∃ choice, choice ∈ setup.exclusionMoveSourceMenu who view := by
  classical
  cases view with
  | none => exact ⟨none, rfl, fun _ chosen => by cases chosen⟩
  | some view =>
      by_cases excluded : setup.ExcludedView who (some view)
      · obtain ⟨choice, legal, failure⟩ := ProtocolView.exists_failure_menu who setup.program
          (CommitmentInterface.forfeiture setup.program) (fun _ => rfl) view
        exact ⟨choice, legal, fun action selected =>
          ⟨fun _ => excluded, fun _ => failure action selected⟩⟩
      · obtain ⟨choice, legal, move⟩ := ProtocolView.exists_move_menu who setup.program
          (CommitmentInterface.forfeiture setup.program) view
        exact ⟨choice, legal, fun action selected =>
          ⟨fun fails => (move action selected fails).elim, fun excludedNow =>
            (excluded excludedNow).elim⟩⟩

theorem exclusionMoveSourceMenu_legal (who : Player) (state : setup.ProtocolState)
    (choice : Option (OwnAction Player L)) :
    choice ∈ setup.exclusionMoveSourceMenu who (setup.protocolObserve who state) ↔
      match choice with
      | none => ¬ (setup.executionProtocol
          (CommitmentInterface.forfeiture setup.program)).active state who
      | some action => (setup.executionProtocol
          (CommitmentInterface.forfeiture setup.program)).active state who ∧
          action ∈ setup.exclusionMoveAvailable state who := by
  cases choice with
  | none =>
      cases state <;> simp [exclusionMoveSourceMenu, protocolMenu, protocolObserve,
        ProtocolView.menu, executionProtocol]
  | some action =>
      simp only [exclusionMoveSourceMenu, Set.mem_ofPred_eq, Option.some.injEq, forall_eq',
        excludedView_observe_iff, exclusionMoveAvailable]
      cases state <;> simp [protocolMenu, protocolObserve, ProtocolView.menu, executionProtocol,
        and_assoc]

theorem exclusionMoveAvailable_subset (state : setup.ProtocolState) (who : Player) :
    setup.exclusionMoveAvailable state who ⊆
      (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).available
        state who := fun _ offered => offered.1

theorem exclusionMoveProgress (state : setup.ProtocolState)
    (_ : ¬ (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).terminal
      state) :
    ∃ joint, IsLegalJoint
      ((setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).active state)
      (setup.exclusionMoveAvailable state) joint := by
  let chosen := fun who =>
    setup.exclusionMoveSourceMenu_nonempty who (setup.protocolObserve who state)
  refine ⟨fun who => (chosen who).choose, fun who => ?_⟩
  have permitted := (setup.exclusionMoveSourceMenu_legal who state (chosen who).choose).mp
    (chosen who).choose_spec
  cases selected : (chosen who).choose <;>
    simpa only [selected] using permitted

/-- The source game requiring moves until exclusion and automatic failures thereafter. -/
abbrev exclusionMoveProtocol : ExecutionProtocol Player :=
  setup.exclusionProtocol.restrictAvailable setup.exclusionMoveAvailable
    (fun _ _ _ offered => ⟨offered.1, offered.2.mpr⟩) setup.exclusionMoveProgress

/-- A nonexcluded information flag requires a move; an excluded flag retains
its existing automatic-failure menu. -/
def exclusionMoveMenu (who : Player) (info : setup.exclusionModel.InfoState who) :
    Set (Option (OwnAction Player L)) :=
  {choice | choice ∈ setup.exclusionModel.menu who info ∧
    (info.2 = false → ∀ action, choice = some action → ¬ action.IsFailure)}

open Classical in
/-- The flagged move menu agrees with the semantic menu on genuine observations. -/
theorem exclusionMoveMenu_observed (who : Player) (view : setup.ProtocolView who) :
    setup.exclusionMoveMenu who (view, setup.excludedFlag who view) =
      setup.exclusionMoveSourceMenu who view := by
  ext choice
  by_cases excluded : setup.ExcludedView who view
  · simp only [exclusionMoveMenu, exclusionModel, InformationModel.flagMenu,
      excludedFlag, decide_eq_true excluded, Bool.cond_true, Set.mem_ofPred_eq,
      Bool.true_eq_false, false_implies, and_true, exclusionMenu,
      exclusionMoveSourceMenu]
    constructor
    · rintro ⟨offered, failures⟩
      exact ⟨offered, fun action selected => ⟨fun _ => excluded, fun _ => failures action selected⟩⟩
    · rintro ⟨offered, failures⟩
      exact ⟨offered, fun action selected => (failures action selected).mpr excluded⟩
  · simp only [exclusionMoveMenu, exclusionModel, InformationModel.flagMenu,
      excludedFlag, decide_eq_false excluded, Bool.cond_false, Set.mem_ofPred_eq,
      true_implies, exclusionMoveSourceMenu]
    constructor
    · rintro ⟨offered, moves⟩
      exact ⟨offered, fun action selected =>
        ⟨fun fails => (moves action selected fails).elim, fun excludedNow =>
          (excluded excludedNow).elim⟩⟩
    · rintro ⟨offered, moves⟩
      exact ⟨offered, fun action selected fails => excluded ((moves action selected).mp fails)⟩

/-- The move game retains the source views and the explicit exclusion flag. -/
def exclusionMoveModel : InformationModel setup.exclusionMoveProtocol :=
  setup.exclusionModel.restrictMenu setup.exclusionMoveMenu (by
    intro who state trace choice
    have observed : setup.exclusionModel.infoOf who (restrictAvailable.trace trace) =
        (setup.protocolObserve who state,
          setup.excludedFlag who (setup.protocolObserve who state)) := by
      exact (InformationModel.flagMenu_infoOf _ _ _ _ who _).trans
        (congrArg (fun view => (view, setup.excludedFlag who view))
          (setup.protocol_info _ who _))
    rw [observed, exclusionMoveMenu_observed]
    cases choice <;> exact setup.exclusionMoveSourceMenu_legal who state _)

theorem exclusionMove_perfectRecall : setup.exclusionMoveModel.PerfectRecall :=
  InformationModel.restrictMenu_perfectRecall _ _ _ setup.exclusion_perfectRecall

theorem exclusionMove_decisionRecall : setup.exclusionMoveModel.DecisionRecall :=
  setup.exclusionMoveModel.decisionRecall_of_perfectRecall setup.exclusionMove_perfectRecall

theorem exclusionMove_bounded :
    setup.exclusionMoveProtocol.BoundedHorizon (instructionCount setup.program + 1) :=
  restrictAvailable.boundedHorizon setup.exclusion_bounded

/-- Every move-game history has the flagged source observation. -/
theorem exclusionMove_info (who : Player) {state : setup.ProtocolState}
    (trace : setup.exclusionMoveProtocol.Trace state) :
    setup.exclusionMoveModel.infoOf who trace =
      (setup.protocolObserve who state,
        setup.excludedFlag who (setup.protocolObserve who state)) :=
  (InformationModel.restrictMenu_infoOf _ _ _ who trace).trans
    ((InformationModel.flagMenu_infoOf _ _ _ _ who _).trans
      (congrArg (fun view => (view, setup.excludedFlag who view))
        (setup.protocol_info _ who _)))

/-- Every information value has a legal choice in the move game. -/
theorem exclusionMove_choice_nonempty (who : Player)
    (info : setup.exclusionMoveModel.InfoState who) :
    Nonempty (setup.exclusionMoveModel.Choice who info) := by
  cases info with
  | mk view excluded =>
      cases excluded with
      | true =>
          obtain ⟨choice⟩ := setup.exclusion_choice_nonempty who (view, true)
          exact ⟨⟨choice.1, choice.2, fun impossible => by cases impossible⟩⟩
      | false =>
          cases view with
          | none => exact ⟨⟨none, rfl, fun _ _ chosen => by cases chosen⟩⟩
          | some view =>
              obtain ⟨choice, offered, moves⟩ := ProtocolView.exists_move_menu who setup.program
                (CommitmentInterface.forfeiture setup.program) view
              exact ⟨⟨choice, offered, fun _ => moves⟩⟩

/-- Finite binding types give finite move menus. -/
theorem exclusionMove_finite_choice (finite : setup.program.FiniteBindingTypes) (who : Player)
    (info : setup.exclusionMoveModel.InfoState who) :
    Finite (setup.exclusionMoveModel.Choice who info) := by
  have := setup.exclusion_finite_choice finite who info
  exact Finite.of_injective
    (fun choice : setup.exclusionMoveModel.Choice who info =>
      (⟨choice.1, choice.2.1⟩ : setup.exclusionModel.Choice who info))
    (fun first second same => Subtype.ext (congrArg Subtype.val same :))

/-- Choices at a nonexcluded information flag never voluntarily fail. -/
theorem exclusionMove_choice_not_failure (who : Player)
    (info : setup.exclusionMoveModel.InfoState who) (notExcluded : info.2 = false)
    (choice : setup.exclusionMoveModel.Choice who info) (action : OwnAction Player L)
    (selected : choice.1 = some action) : ¬ action.IsFailure :=
  choice.2.2 notExcluded action selected

/-- The mandatory-move game is a structural action restriction of exclusion. -/
def exclusionMoveRestriction : setup.exclusionMoveModel.ActionRestriction setup.exclusionModel :=
  setup.exclusionModel.menuRestriction setup.exclusionMoveMenu _ (fun _ _ _ offered => offered.1)

end Setup
end Vegas.SourceProgram
