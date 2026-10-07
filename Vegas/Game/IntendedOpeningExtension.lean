/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceContinuation
import Vegas.Source.IntendedGame
import Vegas.Source.Disclosure
import GameTheory.Protocol.RestrictionProfile

/-! # An opening extension of every intended profile

The intended game offers only opening at a reveal. Every profile of the
intended game extends to a profile of the source game that never refuses a
disclosure: at the information values the intended game keeps it plays the
intended law, and elsewhere a legal choice that opens at every own reveal
(`Vegas.SourceProgram.Setup.openingExtension`). Its decoded source policies
disclose at every reveal (`Vegas.SourceProgram.Setup.openingExtension_disclosing`).
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A choice that is not a refusal to disclose. -/
def NotRefusal (choice : Option (OwnAction Player L)) : Prop :=
  ∀ owner name, choice ≠ some (.reveal owner name false)

/-- Every abstract view has a legal choice that is not a refusal: none for a
player not on the move, a value binding at its own commitment and an opening at
its own reveal. -/
theorem ProtocolView.exists_notRefusal_menu (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (view : ProtocolView who program) →
      ∃ choice, ProtocolView.menu who program admission view choice ∧ NotRefusal choice
  | _, _, .ret _, _, _ =>
      ⟨none, by simp [ProtocolView.menu, ProtocolView.actor], fun _ _ => nofun⟩
  | _, _, .sample _ _ _ next, admission, view => by
      cases view with
      | inl _ => exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor], fun _ _ => nofun⟩
      | inr later => exact exists_notRefusal_menu who next admission later
  | _, _, .commit (payload := payload) name owner _ _ next, admission, view => by
      cases view with
      | inl _ =>
          by_cases own : owner = who
          · exact ⟨some (.commit owner name payload (.success (L.someValue payload))),
              by simp [ProtocolView.menu, ProtocolView.actor, ProtocolView.available, own],
              fun _ _ => nofun⟩
          · exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor, own], fun _ _ => nofun⟩
      | inr later => exact exists_notRefusal_menu who next (fun site => admission (some site)) later
  | _, _, .reveal _ owner name _ _ _ next, admission, view => by
      cases view with
      | inl _ =>
          by_cases own : owner = who
          · refine ⟨some (.reveal owner name true),
              by simp [ProtocolView.menu, ProtocolView.actor, ProtocolView.available, own], ?_⟩
            intro other otherName same
            simp at same
          · exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor, own], fun _ _ => nofun⟩
      | inr later => exact exists_notRefusal_menu who next admission later

/-- An intended action never refuses a disclosure. -/
theorem ProtocolView.intendedAvailable_notRefusal (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (view : ProtocolView who program) →
      ∀ action ∈ intendedAvailable who program view, NotRefusal (some action)
  | _, _, .ret _, _, _, member => member.elim
  | _, _, .sample _ _ _ next, view, action, member => by
      cases view with
      | inl _ => exact member.elim
      | inr later => exact intendedAvailable_notRefusal who next later action member
  | _, _, .commit _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          obtain ⟨_, _, rfl⟩ := member
          exact fun _ _ => nofun
      | inr later => exact intendedAvailable_notRefusal who next later action member
  | _, _, .reveal _ _ _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          change action = _ at member
          subst member
          intro other otherName same
          simp at same
      | inr later => exact intendedAvailable_notRefusal who next later action member

/-- A protocol policy that never refuses decodes to a disclosing source policy. -/
theorem BehavioralPolicy.disclosing_fromProtocol {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : (view : ProtocolView who program) → PMF
      {action : Option (OwnAction Player L) //
        ProtocolView.menu who program admission view action}) →
    (∀ view, ∀ choice ∈ (policy view).support, NotRefusal choice.1) →
    Disclosing program (BehavioralPolicy.fromProtocol program admission policy)
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, policy, opens =>
      disclosing_fromProtocol next admission (fun view => policy (Sum.inr view))
        (fun view => opens (Sum.inr view))
  | _, _, .commit _ _ _ _ next, admission, policy, opens =>
      disclosing_fromProtocol next (fun site => admission (some site))
        (fun view => policy (Sum.inr view)) (fun view => opens (Sum.inr view))
  | _, _, .reveal _ owner name _ _ _ next, admission, policy, opens => by
      refine ⟨fun own view refused => ?_,
        disclosing_fromProtocol next admission (fun view => policy (Sum.inr view))
          (fun view => opens (Sum.inr view))⟩
      obtain ⟨choice, supported, decision⟩ := (PMF.mem_support_map_iff _ _ _).mp refused
      have legal := choice.2
      have notRefused := opens (Sum.inl view) choice supported
      cases selected : choice.1 with
      | none =>
          rw [selected] at legal
          simp [ProtocolView.menu, ProtocolView.actor, own] at legal
      | some action =>
          rw [selected] at legal decision notRefused
          obtain ⟨_, disclose, rfl⟩ := legal
          change disclose = false at decision
          subst decision
          exact notRefused owner name rfl

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- A legal choice that is not a refusal, at every information value. -/
theorem exists_notRefusal_choice (admission : CommitmentInterface setup.program)
    (who : Player) (info : setup.ProtocolView who) :
    ∃ choice : (setup.informationModel admission).Choice who info, NotRefusal choice.1 := by
  cases info with
  | none => exact ⟨⟨none, rfl⟩, fun _ _ => nofun⟩
  | some view =>
      obtain ⟨choice, legal, opens⟩ :=
        ProtocolView.exists_notRefusal_menu who setup.program admission view
      exact ⟨⟨choice, legal⟩, opens⟩

/-- A source policy that at every information value plays a legal choice that
is not a refusal. -/
def openingPolicy (admission : CommitmentInterface setup.program) (who : Player) :
    (setup.informationModel admission).BehavioralPolicy who := fun info =>
  PMF.pure (setup.exists_notRefusal_choice admission who info).choose

/-- **The opening extension of an intended profile.** At the information values
the intended game keeps, play the intended law; elsewhere a legal choice that
is not a refusal. -/
def openingExtension (intended : Profile setup.intendedModel.behavioralSignature) :
    Profile
      (setup.informationModel (CommitmentInterface.values setup.program)).behavioralSignature :=
  setup.intendedRestriction.extendProfile intended
    (fun who => setup.openingPolicy (CommitmentInterface.values setup.program) who)

/-- The opening extension extends the intended profile. -/
theorem openingExtension_extends (intended : Profile setup.intendedModel.behavioralSignature) :
    setup.intendedRestriction.ExtendsProfile intended (setup.openingExtension intended) :=
  setup.intendedRestriction.extendProfile_extends _ _

/-- The opening extension never refuses a disclosure. -/
theorem openingExtension_notRefusal (intended : Profile setup.intendedModel.behavioralSignature)
    (who : Player) (info : setup.ProtocolView who) :
    ∀ choice ∈ (setup.openingExtension intended who info).support, NotRefusal choice.1 := by
  classical
  by_cases retained : setup.intendedRestriction.Retained who info
  · obtain ⟨site, rfl⟩ := retained
    simp only [openingExtension, InformationModel.ActionRestriction.extendProfile,
      dite_eq_left (setup.intendedRestriction.retained_site who site),
      InformationModel.ActionRestriction.retainedLaw_at]
    intro choice member
    obtain ⟨intendedChoice, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have intendedOpens : ∀ (info : setup.ProtocolView who) (choice : Option (OwnAction Player L)),
        choice ∈ setup.intendedMenu who info → NotRefusal choice := by
      intro info choice legal
      cases info with
      | none =>
          change choice = none at legal
          rw [legal]
          exact fun _ _ => nofun
      | some view =>
          change ProtocolView.intendedMenu who setup.program view choice at legal
          cases choice with
          | none => exact fun _ _ => nofun
          | some action =>
              exact ProtocolView.intendedAvailable_notRefusal who setup.program view action
                legal.2
    exact intendedOpens site.1 intendedChoice.1 intendedChoice.2
  · simp only [openingExtension, InformationModel.ActionRestriction.extendProfile,
      dite_eq_right retained, openingPolicy]
    intro choice member
    rw [(PMF.mem_support_pure_iff _ _).mp member]
    exact (setup.exists_notRefusal_choice _ who info).choose_spec

/-- **The opening extension discloses.** Its decoded source policies disclose
at every reveal. -/
theorem openingExtension_disclosing
    (intended : Profile setup.intendedModel.behavioralSignature) (who : Player) :
    Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.values setup.program) (setup.openingExtension intended) who) :=
  BehavioralPolicy.disclosing_fromProtocol setup.program _ _
    (fun view => setup.openingExtension_notRefusal intended who (some view))

end Setup

end Vegas.SourceProgram
