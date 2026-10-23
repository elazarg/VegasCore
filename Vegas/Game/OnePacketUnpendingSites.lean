/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketValueTransport

/-! # Sites without a pending event

At a decision site of who with no pending event of who, every history ends at a
control with who's recall and view at which either who has no turn, or its
turn's event was already submitted for by its recall (`Vegas.unpending_cases`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

variable {setup leaks bounds horizon scheduler} in
omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The state of an unpending site.** A history of a decision site of who
with no pending event of who ends at a control with who's recall and view,
where who has no turn, or has a turn whose event its recall has submitted for. -/
theorem unpending_cases {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup leaks who site.1 = none)
    (history : (onePacketN).InformationHistory who site.1) :
    ∃ control : (application setup leaks).Control, history.1.state = some control ∧
      control.execution.recall who = past ∧
      control.execution.observe (application setup leaks) who = view ∧
      (view.application.publicView.ownTurn? who = none ∨
        ∃ event, view.application.publicView.ownTurn? who = some event ∧
          (runtime setup).eventRecorded leaks past event = true) := by
  obtain ⟨⟨state, trace⟩, info⟩ := history
  have seen := info.trans atSite
  rw [onePacket_infoOf] at seen
  cases state with
  | none => cases seen
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
        obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj seen)
        refine ⟨control, rfl, pastEq, viewEq, ?_⟩
        rw [atSite] at unpending
        cases turn : view.application.publicView.ownTurn? who with
        | none => exact Or.inl rfl
        | some event =>
            refine Or.inr ⟨event, rfl, ?_⟩
            simp only [pendingEvent, turn, Option.filter_some] at unpending
            cases recorded : (runtime setup).eventRecorded leaks past event with
            | true => rfl
            | false => simp [recorded] at unpending
      · simp [ReactiveApplication.observe, active] at seen

end Vegas
