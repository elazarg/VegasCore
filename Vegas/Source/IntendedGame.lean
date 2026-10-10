/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.GuardPrediction
import Vegas.Source.SetupProtocol
import GameTheoryExtensions.Protocol.MenuRestriction

/-! # The intended game

The intended game of a source program is its source game in which every owned
commitment holds a value the guard accepts and every owned reveal opens. At an
owner's commit it offers only the values the guard is predicted to accept from
the owner's observation (`Vegas.SourceGuard.predicts`); at an owner's reveal it
offers only opening. Both menus are restrictions of the source menus under the
value interface, so the intended model
(`Vegas.SourceProgram.Setup.intendedModel`) is a menu restriction of the source
information model and embeds into it
(`Vegas.SourceProgram.Setup.intendedRestriction`).

The definitions are total: where no value is predicted to be accepted, the
commit menu is the full value menu. A well-formed setup
(`Vegas.SourceProgram.Setup.WellFormed`) never reaches such a commit: every
guard is satisfiable at every commit the intended game reaches, given its
author's observation, and the initial law binds a value in every commitment
cell.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Values

variable {Γ : SourceCtx Player L} {owner : Player} {name : VarId} {payload : L.Ty}

/-- The values a guard is predicted to accept, judged from `who`'s observation;
every value when `who` does not own the commitment. -/
def predictedValues (who : Player) (guard : SourceGuard L Γ owner name payload)
    (observation : SourceObservation L who Γ) : Set (L.Val payload) :=
  {value | ∀ same : owner = who, guard.predicts (same ▸ observation) value = true}

/-- The values the intended game offers at a commit: the predicted values, or
every value when none is predicted. -/
def intendedValues (who : Player) (guard : SourceGuard L Γ owner name payload)
    (observation : SourceObservation L who Γ) : Set (L.Val payload) :=
  {value | value ∈ predictedValues who guard observation ∨
    predictedValues who guard observation = ∅}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem intendedValues_nonempty (who : Player) (guard : SourceGuard L Γ owner name payload)
    (observation : SourceObservation L who Γ) :
    ∃ value, value ∈ intendedValues who guard observation := by
  by_cases empty : predictedValues who guard observation = ∅
  · exact ⟨L.someValue payload, Or.inr empty⟩
  · obtain ⟨value, predicted⟩ := Set.nonempty_iff_ne_empty.mpr empty
    exact ⟨value, Or.inl predicted⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- At the owner's own observation, the predicted values are those the guard is
predicted to accept. -/
theorem mem_predictedValues_self (guard : SourceGuard L Γ owner name payload)
    (observation : SourceObservation L owner Γ) (value : L.Val payload) :
    value ∈ predictedValues owner guard observation ↔ guard.predicts observation value = true :=
  ⟨fun predicted => predicted rfl, fun accepted same => by cases same; exact accepted⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Once some value is predicted to be accepted, the intended values at the
owner's observation are exactly the predicted ones. -/
theorem mem_intendedValues_self (guard : SourceGuard L Γ owner name payload)
    (observation : SourceObservation L owner Γ)
    (satisfiable : ∃ value, guard.predicts observation value = true) (value : L.Val payload) :
    value ∈ intendedValues owner guard observation ↔ guard.predicts observation value = true := by
  obtain ⟨witness, accepted⟩ := satisfiable
  have nonempty : predictedValues owner guard observation ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp
      ⟨witness, (mem_predictedValues_self guard observation _).mpr accepted⟩
  exact (or_iff_left nonempty).trans (mem_predictedValues_self guard observation value)

end Values

/-- Every guard is satisfiable at every commit the intended game reaches from a
configuration: some value is predicted to be accepted from the author's
observation. Reachability follows chance support, predicted values at commits
and opening at reveals. -/
def GuardsSatisfiableFrom : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Config Player L Γ → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample name _ law next, config =>
      ∀ value ∈ (L.evalDist law (sourcePublicEnv config.state)).support,
        GuardsSatisfiableFrom next (sampleSuccessor name config value)
  | _, _, .commit name owner _ guard next, config =>
      (∃ value, guard.predicts (sourceObserve owner config.state) value = true) ∧
      ∀ value, guard.predicts (sourceObserve owner config.state) value = true →
        GuardsSatisfiableFrom next (commitSuccessor name guard config (.success value))
  | _, _, .reveal published _ _ _ source _ next, config =>
      GuardsSatisfiableFrom next (revealSuccessor published source config true)

namespace ProtocolView

/-- The actions the intended game offers at a program point: predicted values
at a commit, opening at a reveal. -/
def intendedAvailable (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program →
      Set (OwnAction Player L)
  | _, _, .ret _ => fun _ => ∅
  | _, _, .sample _ _ _ next => Sum.elim (fun _ => ∅) (intendedAvailable who next)
  | _, _, .commit (payload := payload) name owner _ guard next =>
      Sum.elim
        (fun view => {action | ∃ value ∈ intendedValues who guard view.1,
          action = .commit owner name payload (.success value)})
        (intendedAvailable who next)
  | _, _, .reveal _ owner name _ _ _ next =>
      Sum.elim (fun _ => {.reveal owner name true}) (intendedAvailable who next)

/-- The local menu of the intended game. -/
def intendedMenu (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (view : ProtocolView who program)
    (choice : Option (OwnAction Player L)) : Prop :=
  match choice with
  | some action => actor who program view = some who ∧ action ∈ intendedAvailable who program view
  | none => actor who program view ≠ some who

/-- The intended actions are source actions under every admission. -/
theorem intendedAvailable_subset (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (view : ProtocolView who program) →
      intendedAvailable who program view ⊆ available who program admission view
  | _, _, .ret _, _, _ => fun _ impossible => impossible.elim
  | _, _, .sample _ _ _ next, admission, view => by
      cases view with
      | inl _ => exact fun _ impossible => impossible.elim
      | inr later => exact intendedAvailable_subset who next admission later
  | _, _, .commit _ _ _ _ next, admission, view => by
      cases view with
      | inl _ =>
          rintro action ⟨value, _, rfl⟩
          exact ⟨.success value, CommitmentAdmission.admits_success _ _, rfl⟩
      | inr later =>
          exact intendedAvailable_subset who next (fun site => admission (some site)) later
  | _, _, .reveal _ _ _ _ _ _ next, admission, view => by
      cases view with
      | inl _ =>
          rintro action rfl
          exact ⟨true, rfl⟩
      | inr later => exact intendedAvailable_subset who next admission later

theorem intendedMenu_subset (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (view : ProtocolView who program) (choice : Option (OwnAction Player L))
    (intended : intendedMenu who program view choice) :
    menu who program admission view choice := by
  cases choice with
  | none => exact intended
  | some action =>
      exact ⟨intended.1, intendedAvailable_subset who program admission view intended.2⟩

end ProtocolView

namespace ProtocolState

/-- Every program point offers a joint action legal in the intended game. -/
theorem intendedProgress : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    ∃ joint : Player → Option (OwnAction Player L), ∀ who,
      ProtocolView.intendedMenu who program (observe who program state) (joint who)
  | _, _, .ret _, _ => ⟨fun _ => none, fun _ => by
      simp [ProtocolView.intendedMenu, ProtocolView.actor]⟩
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl config =>
          exact ⟨fun _ => none, fun _ => by
            simp [ProtocolView.intendedMenu, ProtocolView.actor, observe]⟩
      | inr rest => exact intendedProgress next rest
  | _, _, .commit (payload := payload) name owner _ guard next, state => by
      cases state with
      | inl config =>
          obtain ⟨value, intended⟩ :=
            intendedValues_nonempty owner guard (sourceObserve owner config.state)
          refine ⟨fun who => if owner = who then
            some (.commit owner name payload (.success value)) else none, ?_⟩
          intro who
          by_cases same : owner = who
          · subst same
            simp only [↓reduceIte, ProtocolView.intendedMenu, observe, Sum.elim_inl,
              ProtocolView.actor, ProtocolView.intendedAvailable, Config.view]
            exact ⟨trivial, value, intended, rfl⟩
          · simp [same, ProtocolView.intendedMenu, observe, ProtocolView.actor]
      | inr rest => exact intendedProgress next rest
  | _, _, .reveal _ owner name _ _ _ next, state => by
      cases state with
      | inl config =>
          refine ⟨fun who => if owner = who then some (.reveal owner name true) else none, ?_⟩
          intro who
          by_cases same : owner = who
          · simp only [same, ↓reduceIte, ProtocolView.intendedMenu, observe, Sum.elim_inl,
              ProtocolView.actor, ProtocolView.intendedAvailable]
            exact ⟨trivial, rfl⟩
          · simp [same, ProtocolView.intendedMenu, observe, ProtocolView.actor]
      | inr rest => exact intendedProgress next rest

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- A well-formed setup: the initial law binds a value in every commitment cell,
and every guard is satisfiable at every commit the intended game reaches. -/
structure WellFormed : Prop where
  initialValues : ∀ initial ∈ setup.initialLaw.support,
    ∀ {x : VarId} {owner : Player} {payload : L.Ty}
      (cell : HasVar setup.context x (.commitment owner payload)),
      ∃ value, initial.get cell = .success value
  guardsSatisfiable : ∀ initial ∈ setup.initialLaw.support,
    GuardsSatisfiableFrom setup.program (setup.initialConfig initial)

/-- The intended actions at a setup protocol state. -/
def intendedAvailable (state : setup.ProtocolState) (who : Player) : Set (OwnAction Player L) :=
  (setup.protocolObserve who state).elim ∅ (ProtocolView.intendedAvailable who setup.program)

theorem intendedAvailable_subset (admission : CommitmentInterface setup.program)
    (state : setup.ProtocolState) (who : Player) :
    setup.intendedAvailable state who ⊆
      (setup.executionProtocol admission).available state who := by
  cases state with
  | none => exact fun _ impossible => impossible.elim
  | some state =>
      exact ProtocolView.intendedAvailable_subset who setup.program admission
        (ProtocolState.observe who setup.program state)

theorem intendedProgress (admission : CommitmentInterface setup.program)
    (state : setup.ProtocolState) (_ : ¬ (setup.executionProtocol admission).terminal state) :
    ∃ joint, IsLegalJoint ((setup.executionProtocol admission).active state)
      (setup.intendedAvailable state) joint := by
  cases state with
  | none => exact ⟨fun _ => none, fun _ impossible => impossible⟩
  | some state =>
      obtain ⟨joint, legal⟩ := ProtocolState.intendedProgress setup.program state
      refine ⟨joint, fun who => ?_⟩
      have member := legal who
      revert member
      cases joint who <;> exact id

/-- The intended protocol: the source protocol under the value interface with
the intended actions. -/
abbrev intendedProtocol : ExecutionProtocol Player :=
  (setup.executionProtocol (CommitmentInterface.values setup.program)).restrictAvailable
    setup.intendedAvailable (setup.intendedAvailable_subset _) (setup.intendedProgress _)

/-- The intended local menu. -/
def intendedMenu (who : Player) : setup.ProtocolView who → Set (Option (OwnAction Player L))
  | none => {choice | choice = none}
  | some view => {choice | ProtocolView.intendedMenu who setup.program view choice}

theorem intendedMenu_adequate (who : Player) {state : setup.ProtocolState}
    (trace : setup.intendedProtocol.Trace state) (choice : Option (OwnAction Player L)) :
    choice ∈ setup.intendedMenu who
        ((setup.informationModel (CommitmentInterface.values setup.program)).infoOf who
          (restrictAvailable.trace trace)) ↔
      LegalOption setup.intendedProtocol state who choice := by
  rw [show (setup.informationModel (CommitmentInterface.values setup.program)).infoOf who
      (restrictAvailable.trace trace) = setup.protocolObserve who state from
    setup.protocol_info _ who _]
  cases state with
  | none =>
      cases choice with
      | none => exact ⟨fun _ impossible => impossible, fun _ => rfl⟩
      | some action =>
          exact ⟨fun chosen => (nomatch (show some action = none from chosen)),
            fun legal => legal.1.elim⟩
  | some state => cases choice <;> exact Iff.rfl

/-- **The intended model.** The source information model under the value
interface, offering only predicted values at commits and opening at reveals. -/
def intendedModel : InformationModel setup.intendedProtocol :=
  (setup.informationModel (CommitmentInterface.values setup.program)).restrictMenu
    setup.intendedMenu setup.intendedMenu_adequate

theorem intendedMenu_subset (admission : CommitmentInterface setup.program) (who : Player)
  (view : setup.ProtocolView who) :
    setup.intendedMenu who view ⊆
      (setup.informationModel admission).menu who view := by
  cases view with
  | none => exact fun _ chosen => chosen
  | some view =>
      exact fun choice intended => ProtocolView.intendedMenu_subset who setup.program admission view
        choice intended

/-- The intended source game embeds into arbitrary sitewise admission,
including the full forfeiture game, with the same states and transition laws. -/
def intendedRestriction (admission : CommitmentInterface setup.program) :
  setup.intendedModel.ActionRestriction
    (setup.informationModel admission) :=
  (setup.informationModel admission).menuRestriction
    (available := setup.intendedAvailable)
    (included := setup.intendedAvailable_subset admission)
    (progress := setup.intendedProgress admission)
    setup.intendedMenu
    (by
      intro who state trace choice
      rw [show (setup.informationModel admission).infoOf who
        (restrictAvailable.trace trace) = setup.protocolObserve who state from
          setup.protocol_info admission who _]
      have adequate := setup.intendedMenu_adequate who trace choice
      rw [show (setup.informationModel (CommitmentInterface.values setup.program)).infoOf
        who (restrictAvailable.trace
          (E := setup.executionProtocol (CommitmentInterface.values setup.program))
          (included := setup.intendedAvailable_subset
            (CommitmentInterface.values setup.program))
          (progress := setup.intendedProgress (CommitmentInterface.values setup.program)) trace) =
            setup.protocolObserve who state from
          setup.protocol_info _ who _] at adequate
      exact adequate)
    (by
      intro who view choice intended
      cases view with
      | none => exact intended
      | some view =>
          exact ProtocolView.intendedMenu_subset who setup.program admission view choice intended)


end Setup

end Vegas.SourceProgram
