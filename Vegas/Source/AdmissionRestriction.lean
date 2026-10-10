/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.IntendedGame
import GameTheoryExtensions.Protocol.MenuRestriction

/-! # Value commitments inside arbitrary source admission menus

Restricting any sitewise commitment admission to successful value bindings
recovers the actual value-interface source model. Every extra legal choice is
an irrevocably failed commitment; reveals and chance steps add no choices.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

theorem valuesAvailable_subset (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (view : ProtocolView who program) →
      available who program (CommitmentInterface.values program) view ⊆
        available who program admission view
  | _, _, .ret _, _, _ => fun _ impossible => impossible.elim
  | _, _, .sample _ _ _ next, admission, view => by
      cases view with
      | inl _ => exact fun _ impossible => impossible.elim
      | inr later => exact valuesAvailable_subset who next admission later
  | _, _, .commit _ _ _ _ next, admission, view => by
      cases view with
      | inl _ =>
          rintro action ⟨result, admitted, rfl⟩
          cases result with
          | failure => cases admitted
          | success value => exact ⟨.success value, trivial, rfl⟩
      | inr later =>
          exact valuesAvailable_subset who next (fun site => admission (some site)) later
  | _, _, .reveal _ _ _ _ _ _ next, admission, view => by
      cases view with
      | inl _ => exact fun _ legal => legal
      | inr later => exact valuesAvailable_subset who next admission later

theorem valuesMenu_subset (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (view : ProtocolView who program) (choice : Option (OwnAction Player L))
    (legal : menu who program (CommitmentInterface.values program) view choice) :
    menu who program admission view choice := by
  cases choice with
  | none => exact legal
  | some action => exact ⟨legal.1, valuesAvailable_subset who program admission view legal.2⟩

theorem extra_valuesAvailable_failed (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (view : ProtocolView who program) → (action : OwnAction Player L) →
    action ∈ available who program admission view →
    action ∉ available who program (CommitmentInterface.values program) view →
    ∃ owner name payload, action = .commit owner name payload .failure
  | _, _, .ret _, _, _, _, impossible, _ => impossible.elim
  | _, _, .sample _ _ _ next, admission, view, action, legal, extra => by
      cases view with
      | inl _ => exact legal.elim
      | inr later => exact extra_valuesAvailable_failed who next admission later action legal extra
  | _, _, .commit (payload := payload) name owner _ _ next,
      admission, view, action, legal, extra => by
      cases view with
      | inl _ =>
          obtain ⟨result, _admitted, rfl⟩ := legal
          cases result with
          | failure => exact ⟨owner, name, payload, rfl⟩
          | success value => exact (extra ⟨.success value, trivial, rfl⟩).elim
      | inr later =>
          exact extra_valuesAvailable_failed who next
            (fun site => admission (some site)) later action legal extra
  | _, _, .reveal _ _ _ _ _ _ next, admission, view, action, legal, extra => by
      cases view with
      | inl _ => exact (extra legal).elim
      | inr later => exact extra_valuesAvailable_failed who next admission later action legal extra

end ProtocolView

namespace Setup

variable (setup : Setup (Player := Player) (L := L))
  (admission : CommitmentInterface setup.program)

theorem valuesMenu_subset (who : Player) (view : setup.ProtocolView who) :
    (setup.informationModel (CommitmentInterface.values setup.program)).menu who view ⊆
      (setup.informationModel admission).menu who view := by
  cases view with
  | none => exact fun _ legal => legal
  | some view => exact fun choice legal =>
      ProtocolView.valuesMenu_subset who setup.program admission view choice legal

theorem valuesAvailable_subset (state : setup.ProtocolState) (who : Player) :
    (setup.executionProtocol (CommitmentInterface.values setup.program)).available state who ⊆
      (setup.executionProtocol admission).available state who := by
  change (setup.protocolObserve who state).elim (∅ : Set (OwnAction Player L))
    (ProtocolView.available who setup.program (CommitmentInterface.values setup.program)) ⊆
      (setup.protocolObserve who state).elim ∅
        (ProtocolView.available who setup.program admission)
  cases observed : setup.protocolObserve who state with
  | none => exact fun _ impossible => impossible.elim
  | some view => exact ProtocolView.valuesAvailable_subset who setup.program admission view

/-- Successful source binding choices embed in every full or partial
forfeiture interface through the existing structural menu restriction. -/
def valuesRestriction :
    (setup.informationModel (CommitmentInterface.values setup.program)).ActionRestriction
      (setup.informationModel admission) :=
  (setup.informationModel admission).menuRestriction
    (available := (setup.executionProtocol (CommitmentInterface.values setup.program)).available)
    (included := setup.valuesAvailable_subset admission)
    (progress := (setup.executionProtocol (CommitmentInterface.values setup.program)).progress)
    (setup.informationModel (CommitmentInterface.values setup.program)).menu
    (by
      intro who state trace choice
      change _ ↔ LegalOption (setup.executionProtocol
        (CommitmentInterface.values setup.program)) state who choice
      rw [show (setup.informationModel admission).infoOf who
        (restrictAvailable.trace trace) = setup.protocolObserve who state from
          setup.protocol_info admission who _]
      have adequate :=
        (setup.informationModel (CommitmentInterface.values setup.program)).menu_adequate
          who trace choice
      rw [show (setup.informationModel (CommitmentInterface.values setup.program)).infoOf
        who trace = setup.protocolObserve who state from
          setup.protocol_info _ who trace] at adequate
      exact adequate)
    (setup.valuesMenu_subset admission)

theorem valuesRestriction_extra_failed (who : Player) (view : setup.ProtocolView who)
    (choice : (setup.informationModel admission).Choice who view)
    (extra : choice ∉ Set.range ((setup.valuesRestriction admission).choice who view)) :
    ∃ owner name payload, choice.1 = some (.commit owner name payload .failure) := by
  have outside : choice.1 ∉
      (setup.informationModel (CommitmentInterface.values setup.program)).menu who view := by
    intro legal
    apply extra
    exact ⟨⟨choice.1, legal⟩, Subtype.ext rfl⟩
  cases view with
  | none => exact (outside choice.2).elim
  | some view =>
      cases selected : choice.1 with
      | none =>
          have legal := choice.2
          simp only [informationModel, protocolMenu, ProtocolView.menu, selected] at legal outside
          exact (outside legal).elim
      | some action =>
          have legal := choice.2
          simp only [informationModel, protocolMenu, ProtocolView.menu, selected] at legal outside
          obtain ⟨owner, name, payload, same⟩ :=
            ProtocolView.extra_valuesAvailable_failed who setup.program admission view action
              legal.2 (fun permitted => outside ⟨legal.1, permitted⟩)
          exact ⟨owner, name, payload, congrArg some same⟩


end Setup

end Vegas.SourceProgram
