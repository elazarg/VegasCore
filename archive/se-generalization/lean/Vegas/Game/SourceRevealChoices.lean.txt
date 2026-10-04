/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceInformation

/-! # Legal Boolean revelation choices
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem RevealOnly.disclosure_choice (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O), program.RevealOnly →
      ∀ (admission : CommitmentInterface program) (view : ProtocolView who program),
      ProtocolView.actor who program view = some who →
      ∀ disclose : Bool, ∃ choice, ProtocolView.menu who program admission view choice ∧
        OwnAction.disclosure choice = disclose := by
  intro Γ O program
  induction program with
  | ret payoffs =>
      intro _reveals admission view active
      cases active
  | sample name fresh law next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | reveal published owner name fresh selected unresolved next ih =>
      intro reveals admission view active disclose
      cases view with
      | inl current =>
          refine ⟨some (.reveal owner name disclose), ?_, rfl⟩
          exact ⟨active, disclose, rfl⟩
      | inr view => exact ih reveals admission view active disclose

theorem Setup.reveal_choice_fullSupport
    (setup : Setup (Player := Player) (L := L)) (reveals : setup.program.RevealOnly)
    (admission : CommitmentInterface setup.program)
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (who : Player)
    (site : (setup.informationModel admission).InformationSite who) :
    FullSupport ((assessment.strategy who site.1).map fun choice =>
      OwnAction.disclosure choice.1) := by
  intro disclose
  obtain ⟨history, _running, _action⟩ := site.2
  have active := InformationModel.InformationSite.active _ site history
  have observed := (setup.protocol_info admission who history.1.trace).symm.trans history.2
  cases state : history.1.state with
  | none =>
      rw [state] at active
      cases active
  | some current =>
      have actor : ProtocolView.actor who setup.program
          (ProtocolState.observe who setup.program current) = some who := by
        simpa only [Setup.executionProtocol, state, Setup.protocolObserve, Option.map_some,
          Option.elim_some] using active
      obtain ⟨choice, legal, decoded⟩ := RevealOnly.disclosure_choice who setup.program reveals
        admission (ProtocolState.observe who setup.program current) actor disclose
      have permitted : choice ∈ (setup.informationModel admission).menu who site.1 := by
        rw [← observed, state]
        exact legal
      rw [PMF.support_map]
      exact ⟨⟨choice, permitted⟩, mixed who site ⟨choice, permitted⟩, decoded⟩

end Vegas.SourceProgram
