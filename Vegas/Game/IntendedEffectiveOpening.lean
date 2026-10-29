/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.AuthenticOpening
import Vegas.Game.IntendedOpeningExtension
import Vegas.Game.IntendedPreservation

/-! # The intended law through effective openings

An intended profile, read as a law of source choices at every source view
(`Vegas.SourceProgram.Setup.intendedSourceProfile`), extends itself, decodes to
source policies that always disclose, and its effective opening
(`Vegas.SourceProgram.Setup.intendedOpeningProfile`) opens effectively by
construction. Every point of the intended game carries the program's registry
and publication status (`Vegas.SourceProgram.Setup.staticState_trace`), so at
every intended decision site the effective opening plays the intended law, and
its source run has the intended law of typed readouts
(`Vegas.SourceProgram.Setup.intendedOpeningProfile_run`).
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- An intended profile read as a law of source choices at every source view. -/
def intendedSourceProfile (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    ∀ who, (setup.informationModel (CommitmentInterface.values setup.program)).BehavioralPolicy
      who :=
  fun who info => (intended who info).map
    ((setup.intendedRestriction (CommitmentInterface.values setup.program)).choice who info)

/-- The intended source profile never refuses a disclosure. -/
theorem intendedSourceProfile_notRefusal
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) (who : Player)
    (info : setup.ProtocolView who) :
    ∀ choice ∈ (setup.intendedSourceProfile intended who info).support,
      NotRefusal choice.1 := by
  intro choice member
  obtain ⟨intendedChoice, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  have legal := intendedChoice.2
  change intendedChoice.1 ∈ setup.intendedMenu who info at legal
  change NotRefusal intendedChoice.1
  cases info with
  | none =>
      change intendedChoice.1 = none at legal
      rw [legal]
      exact fun _ _ => nofun
  | some view =>
      change ProtocolView.intendedMenu who setup.program view intendedChoice.1 at legal
      cases chosen : intendedChoice.1 with
      | none => exact fun _ _ => nofun
      | some action =>
          rw [chosen] at legal
          exact ProtocolView.intendedAvailable_notRefusal who setup.program view action legal.2

/-- **The intended effective opening.** The intended profile's source policies,
opening exactly their effective disclosures. -/
def intendedOpeningProfile (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    BehavioralProfile setup.program := fun who =>
  (setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
    (setup.intendedSourceProfile intended) who).effectiveOpening setup.program []
      (Revelations.initial setup.context)

theorem intendedOpeningProfile_admitted
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) (who : Player) :
    (setup.intendedOpeningProfile intended who).Admitted setup.program
      (CommitmentInterface.values setup.program) :=
  BehavioralPolicy.admitted_effectiveOpening _ _ _ _ _
    ((setup.behavioralPolicyEquiv (CommitmentInterface.values setup.program) who).symm
      (setup.intendedSourceProfile intended who)).2

/-- Every state of the intended game carries the program's registry and
publication status. -/
theorem staticState_trace :
    ∀ {state} (_ : setup.intendedProtocol.Trace state),
      state.elim True
        (ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context))
  | _, .start => trivial
  | _, .extend (source := before) prior joint _ realized => by
      have earlier := staticState_trace prior
      cases before with
      | none =>
          change _ ∈ (setup.initialLaw.map fun initial =>
            some (ProtocolState.entry setup.program (Config.initial initial))).support
              at realized
          rw [PMF.support_map] at realized
          obtain ⟨initial, _, rfl⟩ := realized
          exact ProtocolState.staticAt_entry setup.program _ rfl rfl
      | some before =>
          change _ ∈ ((ProtocolState.step setup.program before joint).map some).support
            at realized
          rw [PMF.support_map] at realized
          obtain ⟨after, reached, rfl⟩ := realized
          exact ProtocolState.staticAt_step setup.program _ _ before joint after earlier reached

/-- **The effective opening plays the intended law at intended sites.** -/
theorem intendedOpeningProfile_extends (wellFormed : setup.WellFormed)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    (setup.intendedRestriction (CommitmentInterface.values setup.program)).ExtendsProfile
      intended (fun who => setup.toProtocolBehavioralPolicy
        (CommitmentInterface.values setup.program) who (setup.intendedOpeningProfile intended who)
        (setup.intendedOpeningProfile_admitted intended who)) := by
  intro who site
  rcases site with ⟨info, occurs⟩
  change setup.toProtocolBehavioralPolicy (CommitmentInterface.values setup.program) who
      (setup.intendedOpeningProfile intended who)
      (setup.intendedOpeningProfile_admitted intended who) info =
    setup.intendedSourceProfile intended who info
  obtain ⟨⟨history, infoEq⟩, -, action, offered⟩ := occurs
  have observed : setup.intendedModel.infoOf who history.trace =
      setup.protocolObserve who history.state := by
    unfold intendedModel
    rw [InformationModel.restrictMenu_infoOf]
    exact setup.protocol_info _ who _
  have intendedState := setup.intendedState_trace wellFormed history.trace
  have staticState := setup.staticState_trace history.trace
  rw [observed] at infoEq
  subst infoEq
  revert offered intendedState staticState
  cases history.state with
  | none =>
      intro _ _ offered
      exact (nomatch (show some action = none from offered))
  | some state =>
      intro intendedState staticState _
      change ProtocolState.Intended setup.program state at intendedState
      change ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) state
        at staticState
      change setup.toProtocolBehavioralPolicy (CommitmentInterface.values setup.program) who
          (setup.intendedOpeningProfile intended who)
          (setup.intendedOpeningProfile_admitted intended who)
          (some (ProtocolState.observe who setup.program state)) =
        setup.intendedSourceProfile intended who
          (some (ProtocolState.observe who setup.program state))
      apply pmf_map_injective Subtype.val_injective
      rw [setup.toProtocolBehavioralPolicy_map_val]
      change (setup.intendedOpeningProfile intended who).protocolAction setup.program
          (ProtocolState.observe who setup.program state) = _
      unfold intendedOpeningProfile
      have disclosing : Disclosing setup.program (setup.decodeBehavioralProfile
          (CommitmentInterface.values setup.program) (setup.intendedSourceProfile intended)
          who) :=
        BehavioralPolicy.disclosing_fromProtocol setup.program _ _
          (fun view => setup.intendedSourceProfile_notRefusal intended who (some view))
      rw [BehavioralPolicy.protocolAction_effectiveOpening setup.program _ _ _ disclosing
        state staticState intendedState]
      exact BehavioralPolicy.protocolAction_fromProtocol setup.program _ _ _

/-- **The intended law through effective openings.** For a well-formed setup,
the source run of the intended effective opening reads out exactly the intended
law of typed readouts. -/
theorem intendedOpeningProfile_run [Fintype Player] (wellFormed : setup.WellFormed)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => setup.protocolReadout final.state) =
      (setup.run (setup.intendedOpeningProfile intended)).map some := by
  have law := (setup.intendedRestriction (CommitmentInterface.values
    setup.program)).initialized_law intended _ (setup.intendedOpeningProfile_extends wellFormed
      intended) (instructionCount setup.program + 1)
  have source := setup.protocol_runBehavioral_eq (CommitmentInterface.values setup.program)
    (setup.intendedOpeningProfile intended) (setup.intendedOpeningProfile_admitted intended)
  rw [InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom] at source
  rw [← source]
  change _ = ((setup.informationModel (CommitmentInterface.values setup.program)).runBehavioral
    _ (instructionCount setup.program + 1)).map _
  rw [← law, PMF.map_comp]
  rfl

/-- **Intended play from a history is the effective opening's continuation.**
For a well-formed setup, from every history of the intended game, play of an
intended profile for enough steps reads out the continuation of its intended
effective opening from the history's state. -/
theorem intendedOpeningProfile_runFrom [Fintype Player] (wellFormed : setup.WellFormed)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) (fuel : Nat)
    (history : setup.intendedProtocol.History)
    (enough : setup.protocolRemaining history.state ≤ fuel) :
    (setup.intendedModel.runBehavioralFrom intended fuel history).map
        (fun final => setup.protocolReadout final.state) =
      (setup.continuationLaw (setup.intendedOpeningProfile intended) history.state).map some := by
  let restriction := setup.intendedRestriction (CommitmentInterface.values setup.program)
  have law := restriction.runFrom_law intended _ (setup.intendedOpeningProfile_extends wellFormed
    intended) fuel history
  have source := setup.protocol_runBehavioralFrom_eq (CommitmentInterface.values setup.program)
    (setup.intendedOpeningProfile intended) (setup.intendedOpeningProfile_admitted intended) fuel
    (restriction.history history) enough
  rw [InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom] at source
  rw [← law, PMF.map_comp] at source
  exact source

end Vegas.SourceProgram.Setup
