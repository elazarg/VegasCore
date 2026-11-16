module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Source.AuthenticOpening
public import Vegas.Game.IntendedSourceProfile
public import Vegas.Game.IntendedPreservation

@[expose] public section

/-! # The intended law through authentic openings

An intended profile, read as a law of source choices at every source view
(`Vegas.SourceProgram.Setup.intendedSourceProfile`), extends itself, decodes to
source policies that always disclose, and its authentic opening
(`Vegas.SourceProgram.Setup.intendedOpeningProfile`) opens authentic bindings by
construction. Every point of the intended game carries the program's registry
and publication status (`Vegas.SourceProgram.Setup.staticState_trace`), so at
every intended decision site the authentic opening plays the intended law, and
its source run has the intended law of typed readouts
(`Vegas.SourceProgram.Setup.intendedOpeningProfile_run`).
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- **The intended authentic opening.** The intended profile's source policies,
opening exactly their effective disclosures. -/
def intendedOpeningProfile (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    BehavioralProfile setup.program := fun who =>
  (setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
    (setup.intendedSourceProfile (CommitmentInterface.values setup.program) intended)
      who).authenticOpening setup.program

theorem intendedOpeningProfile_admitted
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) (who : Player) :
    (setup.intendedOpeningProfile intended who).Admitted setup.program
      (CommitmentInterface.values setup.program) :=
  BehavioralPolicy.admitted_authenticOpening _ _ _
    ((setup.behavioralPolicyEquiv (CommitmentInterface.values setup.program) who).symm
      (setup.intendedSourceProfile (CommitmentInterface.values setup.program) intended who)).2

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

/-- **The authentic opening plays the intended law at intended sites.** -/
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
    setup.intendedSourceProfile (CommitmentInterface.values setup.program) intended who info
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
        setup.intendedSourceProfile (CommitmentInterface.values setup.program) intended who
          (some (ProtocolState.observe who setup.program state))
      apply pmf_map_injective Subtype.val_injective
      rw [setup.toProtocolBehavioralPolicy_map_val]
      change (setup.intendedOpeningProfile intended who).protocolAction setup.program
          (ProtocolState.observe who setup.program state) = _
      unfold intendedOpeningProfile
      have disclosing : Disclosing setup.program (setup.decodeBehavioralProfile
          (CommitmentInterface.values setup.program) (setup.intendedSourceProfile
            (CommitmentInterface.values setup.program) intended)
          who) :=
        setup.intendedSourceProfile_disclosing (CommitmentInterface.values setup.program)
          intended who
      rw [BehavioralPolicy.protocolAction_authenticOpening setup.program _ disclosing
        state staticState intendedState]
      exact BehavioralPolicy.protocolAction_fromProtocol setup.program _ _ _

/-- **The intended law through authentic openings.** For a well-formed setup,
the source run of the intended authentic opening reads out exactly the intended
law of typed readouts. -/
theorem intendedOpeningProfile_run [Finite Player] (wellFormed : setup.WellFormed)
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

/-- **Intended play from a history is the authentic opening's continuation.**
For a well-formed setup, from every history of the intended game, play of an
intended profile for enough steps reads out the continuation of its intended
authentic opening from the history's state. -/
theorem intendedOpeningProfile_runFrom [Finite Player] (wellFormed : setup.WellFormed)
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

/-- Every extension has the same full source continuation from any genuine
intended history, including histories with zero probability under the profile. -/
theorem continuationLaw_eq_of_intended_extension [Finite Player]
    (wellFormed : setup.WellFormed)
    (admission : CommitmentInterface setup.program)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel admission).behavioralSignature)
    (agrees : (setup.intendedRestriction admission).ExtendsProfile intended target)
    (history : setup.intendedProtocol.History) :
    setup.continuationLaw (setup.decodeBehavioralProfile admission target) history.state =
      setup.continuationLaw (setup.intendedOpeningProfile intended) history.state := by
  let restriction := setup.intendedRestriction admission
  let fuel := setup.protocolRemaining history.state
  have histories := restriction.runFrom_law intended target agrees fuel history
  have readouts := congrArg (PMF.map fun final => setup.protocolReadout final.state) histories
  have targetLaw := setup.runBehavioralFrom_readout admission target fuel
    (restriction.history history) (by rfl)
  have intendedLaw := setup.intendedOpeningProfile_runFrom wellFormed intended fuel history le_rfl
  have equal : (setup.continuationLaw (setup.decodeBehavioralProfile admission target)
      history.state).map some =
      (setup.continuationLaw (setup.intendedOpeningProfile intended) history.state).map some := by
    rw [PMF.map_comp] at readouts
    exact targetLaw.symm.trans (readouts.symm.trans intendedLaw)
  exact pmf_map_injective (Option.some_injective _) equal

/-- The source continuation of an arbitrary extension is clear at every
intended history; no reach probability or equilibrium hypothesis is needed. -/
theorem continuation_clean_of_intended_extension [Finite Player]
    (wellFormed : setup.WellFormed)
    (admission : CommitmentInterface setup.program)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel admission).behavioralSignature)
    (agrees : (setup.intendedRestriction admission).ExtendsProfile intended target)
    (history : setup.intendedProtocol.History)
    (terminal : Config Player L setup.program.terminalCtx)
    (supported : terminal ∈ (setup.continuationLaw
      (setup.decodeBehavioralProfile admission target) history.state).support) :
    terminal.defaulted = ∅ ∧
      ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0 := by
  rw [setup.continuationLaw_eq_of_intended_extension wellFormed admission intended target
    agrees history] at supported
  let fuel := setup.protocolRemaining history.state
  have intendedLaw := setup.intendedOpeningProfile_runFrom wellFormed intended fuel history le_rfl
  have chosen : some terminal ∈ ((setup.continuationLaw
      (setup.intendedOpeningProfile intended) history.state).map some).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨terminal, supported, rfl⟩
  rw [← intendedLaw] at chosen
  obtain ⟨final, _finalSupport, read⟩ := (PMF.mem_support_map_iff _ _ _).mp chosen
  exact ⟨Finset.eq_empty_iff_forall_notMem.mpr fun who =>
    setup.not_defaulted_of_intendedState (setup.intendedState_trace wellFormed final.trace)
      who read, setup.intended_no_failed_reveals wellFormed final read⟩

end Vegas.SourceProgram.Setup
