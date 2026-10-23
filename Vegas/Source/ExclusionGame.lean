/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Exclusion
import Vegas.Source.ProtocolChoiceFiniteness
import Vegas.Source.SetupProtocolRecall
import GameTheoryExtensions.Protocol.FlaggedMenuRestriction

/-! # The source game with exclusion

The exclusion game of a setup runs the source protocol under full forfeiture
admission, events one at a time in program order. At its own events a player
moves or fails: at a commit it binds any value of the domain, with guards
deferred to the reveal that completes them, or misses the binding; at a reveal
it opens or withholds. A player whose event has failed is excluded
(`Vegas.SourceProgram.Setup.ExcludedState`), and from then on its only legal
action at an own event is the failure action
(`Vegas.SourceProgram.Setup.exclusionProtocol`). The existing source successors
record every failure in the state, so later guards, samples and views see it.

Exclusion is a function of the excluded player's view
(`Vegas.SourceProgram.Setup.excludedView_observe_iff`). The information model
(`Vegas.SourceProgram.Setup.exclusionModel`) pairs each source view with that
flag and offers the failure menu at a set flag and the full source menu
otherwise; it has perfect recall
(`Vegas.SourceProgram.Setup.exclusion_perfectRecall`).
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable (setup : Setup (Player := Player) (L := L))

/-- A setup protocol state at which `who` is excluded. -/
def ExcludedState (who : Player) : setup.ProtocolState → Prop
  | none => False
  | some state => ProtocolState.Excluded who setup.program state

/-- A view of `who` at which `who` is excluded. -/
def ExcludedView (who : Player) (view : setup.ProtocolView who) : Prop :=
  ∃ state, setup.protocolObserve who state = view ∧ setup.ExcludedState who state

/-- **Exclusion is observed.** A player's view tells it whether it is
excluded. -/
theorem excludedView_observe_iff (who : Player) (state : setup.ProtocolState) :
    setup.ExcludedView who (setup.protocolObserve who state) ↔ setup.ExcludedState who state := by
  constructor
  · rintro ⟨other, same, excluded⟩
    cases other with
    | none => exact excluded.elim
    | some other =>
        cases state with
        | none => cases same
        | some state =>
            exact (ProtocolState.excluded_iff_of_observe_eq who setup.program other state
              (Option.some.inj same)).mp excluded
  · exact fun excluded => ⟨state, rfl, excluded⟩

/-- The actions of the exclusion game: the source actions under full forfeiture
admission, restricted to failure actions for an excluded player. -/
def exclusionAvailable (state : setup.ProtocolState) (who : Player) : Set (OwnAction Player L) :=
  {action | action ∈ (setup.executionProtocol
      (CommitmentInterface.forfeiture setup.program)).available state who ∧
    (setup.ExcludedState who state → action.IsFailure)}

theorem exclusionAvailable_subset (state : setup.ProtocolState) (who : Player) :
    setup.exclusionAvailable state who ⊆
      (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).available
        state who :=
  fun _ offered => offered.1

theorem exclusionProgress (state : setup.ProtocolState)
    (_ : ¬ (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).terminal
      state) :
    ∃ joint, IsLegalJoint
      ((setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).active state)
      (setup.exclusionAvailable state) joint := by
  cases state with
  | none => exact ⟨fun _ => none, fun _ impossible => impossible⟩
  | some state =>
      have found (who : Player) := ProtocolView.exists_failure_menu who setup.program
        (CommitmentInterface.forfeiture setup.program) (fun _ => rfl)
        (ProtocolState.observe who setup.program state)
      refine ⟨fun who => (found who).choose, fun who => ?_⟩
      have chosen := (found who).choose_spec
      dsimp only
      revert chosen
      cases (found who).choose with
      | none => exact fun chosen => chosen.1
      | some action => exact fun chosen => ⟨chosen.1.1, chosen.1.2, fun _ => chosen.2 action rfl⟩

/-- **The exclusion game protocol.** The source protocol under full forfeiture
admission, in which an excluded player can only fail its own events. -/
abbrev exclusionProtocol : ExecutionProtocol Player :=
  (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).restrictAvailable
    setup.exclusionAvailable setup.exclusionAvailable_subset setup.exclusionProgress

/-- The failure menu at a view: the legal source choices that are no action or
a failure action. -/
def exclusionMenu (who : Player) (view : setup.ProtocolView who) :
    Set (Option (OwnAction Player L)) :=
  {choice | choice ∈ (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).menu who view ∧
    ∀ action, choice = some action → action.IsFailure}

open Classical in
/-- Whether a view excludes its player. -/
def excludedFlag (who : Player) (view : setup.ProtocolView who) : Bool :=
  decide (setup.ExcludedView who view)

theorem excludedFlag_observe_eq_true (who : Player) (state : setup.ProtocolState) :
    setup.excludedFlag who (setup.protocolObserve who state) = true ↔
      setup.ExcludedState who state := by
  simp only [excludedFlag, decide_eq_true_iff, excludedView_observe_iff]

theorem exclusionMenu_adequate (who : Player) {state : setup.ProtocolState}
    (trace : setup.exclusionProtocol.Trace state) (choice : Option (OwnAction Player L)) :
    choice ∈ (setup.informationModel
        (CommitmentInterface.forfeiture setup.program)).flaggedMenu setup.excludedFlag
        setup.exclusionMenu who
        ((setup.informationModel (CommitmentInterface.forfeiture setup.program)).infoOf who
          (restrictAvailable.trace trace)) ↔
      LegalOption setup.exclusionProtocol state who choice := by
  have original := (setup.informationModel
    (CommitmentInterface.forfeiture setup.program)).menu_adequate who
      (restrictAvailable.trace trace) choice
  rw [show (setup.informationModel (CommitmentInterface.forfeiture setup.program)).infoOf who
      (restrictAvailable.trace trace) = setup.protocolObserve who state from
    setup.protocol_info _ who _] at original ⊢
  rw [InformationModel.flaggedMenu]
  by_cases excluded : setup.ExcludedState who state
  · rw [(setup.excludedFlag_observe_eq_true who state).mpr excluded, Bool.cond_true]
    cases choice with
    | none =>
        exact ⟨fun offered => original.mp offered.1,
          fun legal => ⟨original.mpr legal, fun _ chosen => by cases chosen⟩⟩
    | some action =>
        constructor
        · rintro ⟨offered, failure⟩
          obtain ⟨active, available⟩ := original.mp offered
          exact ⟨active, available, fun _ => failure action rfl⟩
        · rintro ⟨active, available, failure⟩
          exact ⟨original.mpr ⟨active, available⟩, fun _ chosen => by
            cases chosen
            exact failure excluded⟩
  · have unset : setup.excludedFlag who (setup.protocolObserve who state) = false := by
      simpa only [Bool.not_eq_true] using
        mt (setup.excludedFlag_observe_eq_true who state).mp excluded
    rw [unset, Bool.cond_false]
    cases choice with
    | none => exact original
    | some action =>
        constructor
        · intro offered
          obtain ⟨active, available⟩ := original.mp offered
          exact ⟨active, available, fun excludedNow => (excluded excludedNow).elim⟩
        · rintro ⟨active, available, _⟩
          exact original.mpr ⟨active, available⟩

/-- **The exclusion game model.** Each source view is paired with whether it
excludes its player; an excluded player is offered the failure menu, every
other player the full source menu under forfeiture admission. -/
def exclusionModel : InformationModel setup.exclusionProtocol :=
  (setup.informationModel (CommitmentInterface.forfeiture setup.program)).flagMenu
    setup.excludedFlag setup.exclusionMenu setup.exclusionMenu_adequate

theorem exclusion_perfectRecall : setup.exclusionModel.PerfectRecall :=
  InformationModel.flagMenu_perfectRecall _ _ _ _ (setup.protocol_perfectRecall _)

theorem exclusion_decisionRecall : setup.exclusionModel.DecisionRecall :=
  setup.exclusionModel.decisionRecall_of_perfectRecall setup.exclusion_perfectRecall

theorem exclusion_bounded :
    setup.exclusionProtocol.BoundedHorizon (instructionCount setup.program + 1) :=
  restrictAvailable.boundedHorizon (setup.protocol_bounded _)

theorem exclusionModel_menu_subset (who : Player) (info : setup.exclusionModel.InfoState who) :
    setup.exclusionModel.menu who info ⊆
      (setup.informationModel (CommitmentInterface.forfeiture setup.program)).menu who info.1 := by
  rcases info with ⟨view, _ | _⟩
  · exact fun _ offered => offered
  · exact fun _ offered => offered.1

/-- Every information value of the exclusion game has finite legal choices
under finite fresh-binding alphabets. -/
theorem exclusion_finite_choice (finite : setup.program.FiniteBindingTypes) (who : Player)
    (info : setup.exclusionModel.InfoState who) :
    Finite (setup.exclusionModel.Choice who info) := by
  have := setup.finite_choice finite (CommitmentInterface.forfeiture setup.program) who info.1
  exact Finite.of_injective
    (fun choice : setup.exclusionModel.Choice who info =>
      (⟨choice.1, setup.exclusionModel_menu_subset who info choice.2⟩ :
        (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Choice who
          info.1))
    (fun first second same => Subtype.ext (congrArg Subtype.val same :))

/-- Every information value of the exclusion game has a legal choice. -/
theorem exclusion_choice_nonempty (who : Player) (info : setup.exclusionModel.InfoState who) :
    Nonempty (setup.exclusionModel.Choice who info) := by
  rcases info with ⟨view, _ | _⟩
  · obtain ⟨choice⟩ := setup.choice_nonempty (CommitmentInterface.forfeiture setup.program) who
      view
    exact ⟨⟨choice.1, choice.2⟩⟩
  · cases view with
    | none => exact ⟨⟨none, rfl, fun _ chosen => by cases chosen⟩⟩
    | some view =>
        obtain ⟨choice, legal, failure⟩ := ProtocolView.exists_failure_menu who setup.program
          (CommitmentInterface.forfeiture setup.program) (fun _ => rfl) view
        exact ⟨⟨choice, legal, failure⟩⟩

end Vegas.SourceProgram.Setup
