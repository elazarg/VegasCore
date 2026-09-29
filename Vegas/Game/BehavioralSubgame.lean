/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SetupSubgame
import Vegas.Source.SetupProtocolBehavioral
import GameTheoryExtensions.Protocol.BehavioralContinuation

/-! # Source-facing behavioral subgame perfection

Every legal protocol deviation corresponds to one admitted source behavioral
policy. The continuation inequalities use the existing source runner and its
full terminal store, permitting utilities of persistent types and public data.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

def admittedBehavioralSignature (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) : GameSignature Player where
  Strategy who := {policy : BehavioralPolicy who program // policy.Admitted program admission}
  Outcome := State L program.terminalCtx

theorem protocol_behavioralContinuationValue_eq (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    (profile : Profile (admittedBehavioralSignature program admission))
    (utility : State L program.terminalCtx → Player → ℝ)
    (history : (executionProtocol program admission initial).History) (who : Player) :
    expect ((informationModel program admission initial).runSingleMoverBehavioralFrom
      (protocol_singleMover program admission initial)
      (Profile.map (target := (informationModel program admission initial).behavioralSignature)
        (fun who => behavioralPolicyEquiv program admission initial who) profile)
      (instructionCount program) history)
        (fun final => protocolUtility program admission initial utility final who) =
      expect (ProtocolState.continuationLaw program (fun who => (profile who).1) history.state)
        (utility · who) := by
  have law := protocol_runBehavioralFrom_eq program admission initial (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount program) history
    (by have count := protocol_history_length program admission initial history.trace; omega)
  have values := congrArg
    (fun law => expect law (fun state => state.elim 0 (utility · who))) law
  simp only [expect_map, Function.comp_def, Option.elim_some] at values
  convert values using 1
  rfl

/-- Finite fresh-binding alphabets make every behavioral continuation law
finitely supported, so every utility is integrable. -/
theorem protocol_behavioralRun_integrable (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    (finite : program.FiniteBindingTypes)
    (profile : Profile (admittedBehavioralSignature program admission))
    (utility : State L program.terminalCtx → Player → ℝ)
    (history : (executionProtocol program admission initial).History) (who : Player) :
    UtilityIntegrable (protocolUtility program admission initial utility) who
      ((informationModel program admission initial).runSingleMoverBehavioralFrom
        (protocol_singleMover program admission initial)
        (Profile.map (target := (informationModel program admission initial).behavioralSignature)
          (fun who => behavioralPolicyEquiv program admission initial who) profile)
        (instructionCount program) history) := by
  have law := protocol_runBehavioralFrom_eq program admission initial (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount program) history
    (by have count := protocol_history_length program admission initial history.trace; omega)
  have mapped : (((informationModel program admission initial).runSingleMoverBehavioralFrom
      (protocol_singleMover program admission initial)
      (fun who => (profile who).1.toProtocol program admission (profile who).2)
      (instructionCount program) history).map
        (fun final => ProtocolState.readout program final.state)).support.Finite := by
    rw [law, PMF.support_map]
    exact (ProtocolState.continuationLaw_support_finite program _
      (FiniteBindingTypes.profileFiniteSupport program finite _) _).image _
  have integrable := (payoffIntegrable_map_iff _ _ (fun state => state.elim 0 (utility · who))).mp
    (payoffIntegrable_of_finite_support _ _ mapped)
  convert integrable using 1
  · rfl
  · funext final
    rfl

theorem protocol_isBehavioralSubgamePerfect_iff (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    (finite : program.FiniteBindingTypes)
    (profile : Profile (admittedBehavioralSignature program admission))
    (utility : State L program.terminalCtx → Player → ℝ) :
    (informationModel program admission initial).IsSingleMoverBehavioralSubgamePerfect
        (protocol_singleMover program admission initial)
        (protocol_bounded program admission initial)
        (Profile.map (fun who => behavioralPolicyEquiv program admission initial who) profile)
        (protocolUtility program admission initial utility) ↔
      ∀ history, (informationModel program admission initial).IsSubgameRoot history →
        ∀ who (alternative : (admittedBehavioralSignature program admission).Strategy who),
          expect (ProtocolState.continuationLaw program
            (fun player => (Profile.update profile who alternative player).1)
            history.state) (utility · who) ≤
          expect (ProtocolState.continuationLaw program (fun player => (profile player).1)
            history.state) (utility · who) := by
  rw [InformationModel.isSingleMoverBehavioralSubgamePerfect_iff]
  constructor
  · intro perfect history proper who alternative
    have bound := (perfect history proper who
      (behavioralPolicyEquiv program admission initial who alternative)).2.2
    simp only [expectedUtility] at bound
    rw [← Profile.map_update, protocol_behavioralContinuationValue_eq,
      protocol_behavioralContinuationValue_eq] at bound
    exact bound
  · intro optimal history proper who alternative
    obtain ⟨sourceAlternative, rfl⟩ :=
      (behavioralPolicyEquiv program admission initial who).surjective alternative
    rw [← Profile.map_update]
    refine ⟨protocol_behavioralRun_integrable program admission initial finite profile utility
      history who, protocol_behavioralRun_integrable program admission initial finite _ utility
      history who, ?_⟩
    simp only [expectedUtility]
    rw [protocol_behavioralContinuationValue_eq, protocol_behavioralContinuationValue_eq]
    exact optimal history proper who sourceAlternative

namespace Setup

theorem protocol_behavioralContinuationValue_eq (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : Profile (admittedBehavioralSignature setup.program admission))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (history : (setup.executionProtocol admission).History) (who : Player) :
    expect ((setup.informationModel admission).runSingleMoverBehavioralFrom
      (setup.protocol_singleMover admission)
      (Profile.map (target := (setup.informationModel admission).behavioralSignature)
        (fun who => setup.behavioralPolicyEquiv admission who) profile)
      (instructionCount setup.program + 1) history)
        (fun final => setup.protocolUtility admission utility final who) =
      expect (setup.continuationLaw (fun who => (profile who).1) history.state)
        (utility · who) := by
  have law := setup.protocol_runBehavioralFrom_eq admission (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount setup.program + 1) history
    (by have count := setup.protocol_history_length admission history.trace; omega)
  have values := congrArg
    (fun law => expect law (fun state => state.elim 0 (utility · who))) law
  simp only [expect_map, Function.comp_def, Option.elim_some] at values
  convert values using 1
  rfl

/-- Finite fresh-binding alphabets and a finitely supported initial law make
every behavioral continuation law finitely supported. -/
theorem protocol_behavioralRun_integrable (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw]
    (profile : Profile (admittedBehavioralSignature setup.program admission))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (history : (setup.executionProtocol admission).History) (who : Player) :
    UtilityIntegrable (setup.protocolUtility admission utility) who
      ((setup.informationModel admission).runSingleMoverBehavioralFrom
        (setup.protocol_singleMover admission)
        (Profile.map (target := (setup.informationModel admission).behavioralSignature)
          (fun who => setup.behavioralPolicyEquiv admission who) profile)
        (instructionCount setup.program + 1) history) := by
  have law := setup.protocol_runBehavioralFrom_eq admission (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount setup.program + 1) history
    (by have count := setup.protocol_history_length admission history.trace; omega)
  have mapped : (((setup.informationModel admission).runSingleMoverBehavioralFrom
      (setup.protocol_singleMover admission)
      (fun who => setup.toProtocolBehavioralPolicy admission who (profile who).1 (profile who).2)
      (instructionCount setup.program + 1) history).map
        (fun final => setup.protocolReadout final.state)).support.Finite := by
    rw [law, PMF.support_map]
    exact (setup.continuationLaw_support_finite _
      (FiniteBindingTypes.profileFiniteSupport _ finite _) _).image _
  have integrable := (payoffIntegrable_map_iff _ _ (fun state => state.elim 0 (utility · who))).mp
    (payoffIntegrable_of_finite_support _ _ mapped)
  convert integrable using 1
  · rfl
  · funext final
    rfl

theorem protocol_isBehavioralSubgamePerfect_iff (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw]
    (profile : Profile (admittedBehavioralSignature setup.program admission))
    (utility : State L setup.program.terminalCtx → Player → ℝ) :
    (setup.informationModel admission).IsSingleMoverBehavioralSubgamePerfect
        (setup.protocol_singleMover admission) (setup.protocol_bounded admission)
        (Profile.map (fun who => setup.behavioralPolicyEquiv admission who) profile)
        (setup.protocolUtility admission utility) ↔
      ∀ history, (setup.informationModel admission).IsSubgameRoot history →
        ∀ who (alternative : (admittedBehavioralSignature setup.program admission).Strategy who),
          expect (setup.continuationLaw
            (fun player => (Profile.update profile who alternative player).1)
            history.state) (utility · who) ≤
          expect (setup.continuationLaw (fun player => (profile player).1)
            history.state) (utility · who) := by
  rw [InformationModel.isSingleMoverBehavioralSubgamePerfect_iff]
  constructor
  · intro perfect history proper who alternative
    have bound :=
      (perfect history proper who (setup.behavioralPolicyEquiv admission who alternative)).2.2
    simp only [expectedUtility] at bound
    rw [← Profile.map_update, protocol_behavioralContinuationValue_eq,
      protocol_behavioralContinuationValue_eq] at bound
    exact bound
  · intro optimal history proper who alternative
    obtain ⟨sourceAlternative, rfl⟩ :=
      (setup.behavioralPolicyEquiv admission who).surjective alternative
    rw [← Profile.map_update]
    refine ⟨setup.protocol_behavioralRun_integrable admission finite profile utility
      history who, setup.protocol_behavioralRun_integrable admission finite _
      utility history who, ?_⟩
    simp only [expectedUtility]
    rw [protocol_behavioralContinuationValue_eq, protocol_behavioralContinuationValue_eq]
    exact optimal history proper who sourceAlternative

end Setup
end Vegas.SourceProgram
