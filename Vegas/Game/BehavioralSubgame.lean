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
    ((informationModel program admission initial).runSingleMoverBehavioralFrom
      (protocol_singleMover program admission initial)
      (Profile.map (target := (informationModel program admission initial).behavioralSignature)
        (fun who => behavioralPolicyEquiv program admission initial who) profile)
      (instructionCount program) history).expect
        (fun final => protocolUtility program admission initial utility final who) =
      (ProtocolState.continuationLaw program (fun who => (profile who).1) history.state).expect
        (utility · who) := by
  have law := protocol_runBehavioralFrom_eq program admission initial (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount program) history
    (by have count := protocol_history_length program admission initial history.trace; omega)
  have values := congrArg
    (fun law => law.expect (fun state => state.elim 0 (utility · who))) law
  simp only [FinDist.expect_map, Option.elim_some] at values
  convert values using 1
  rfl

theorem protocol_isBehavioralSubgamePerfect_iff (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    (profile : Profile (admittedBehavioralSignature program admission))
    (utility : State L program.terminalCtx → Player → ℝ) :
    (informationModel program admission initial).IsBehavioralSubgamePerfect
        (protocol_singleMover program admission initial)
        (protocol_bounded program admission initial)
        (Profile.map (fun who => behavioralPolicyEquiv program admission initial who) profile)
        (protocolUtility program admission initial utility) ↔
      ∀ history, (informationModel program admission initial).IsSubgameRoot history →
        ∀ who (alternative : (admittedBehavioralSignature program admission).Strategy who),
          (ProtocolState.continuationLaw program
            (fun player => (Profile.update profile who alternative player).1)
            history.state).expect (utility · who) ≤
          (ProtocolState.continuationLaw program (fun player => (profile player).1)
            history.state).expect (utility · who) := by
  rw [InformationModel.isBehavioralSubgamePerfect_iff]
  constructor
  · intro perfect history proper who alternative
    have bound := perfect history proper who
      (behavioralPolicyEquiv program admission initial who alternative)
    rw [← Profile.map_update, protocol_behavioralContinuationValue_eq,
      protocol_behavioralContinuationValue_eq] at bound
    exact bound
  · intro optimal history proper who alternative
    obtain ⟨sourceAlternative, rfl⟩ :=
      (behavioralPolicyEquiv program admission initial who).surjective alternative
    rw [← Profile.map_update, protocol_behavioralContinuationValue_eq,
      protocol_behavioralContinuationValue_eq]
    exact optimal history proper who sourceAlternative

namespace Setup

theorem protocol_behavioralContinuationValue_eq (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : Profile (admittedBehavioralSignature setup.program admission))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (history : (setup.executionProtocol admission).History) (who : Player) :
    ((setup.informationModel admission).runSingleMoverBehavioralFrom
      (setup.protocol_singleMover admission)
      (Profile.map (target := (setup.informationModel admission).behavioralSignature)
        (fun who => setup.behavioralPolicyEquiv admission who) profile)
      (instructionCount setup.program + 1) history).expect
        (fun final => setup.protocolUtility admission utility final who) =
      (setup.continuationLaw (fun who => (profile who).1) history.state).expect
        (utility · who) := by
  have law := setup.protocol_runBehavioralFrom_eq admission (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount setup.program + 1) history
    (by have count := setup.protocol_history_length admission history.trace; omega)
  have values := congrArg
    (fun law => law.expect (fun state => state.elim 0 (utility · who))) law
  simp only [FinDist.expect_map, Option.elim_some] at values
  convert values using 1
  rfl

theorem protocol_isBehavioralSubgamePerfect_iff (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : Profile (admittedBehavioralSignature setup.program admission))
    (utility : State L setup.program.terminalCtx → Player → ℝ) :
    (setup.informationModel admission).IsBehavioralSubgamePerfect
        (setup.protocol_singleMover admission) (setup.protocol_bounded admission)
        (Profile.map (fun who => setup.behavioralPolicyEquiv admission who) profile)
        (setup.protocolUtility admission utility) ↔
      ∀ history, (setup.informationModel admission).IsSubgameRoot history →
        ∀ who (alternative : (admittedBehavioralSignature setup.program admission).Strategy who),
          (setup.continuationLaw
            (fun player => (Profile.update profile who alternative player).1)
            history.state).expect (utility · who) ≤
          (setup.continuationLaw (fun player => (profile player).1)
            history.state).expect (utility · who) := by
  rw [InformationModel.isBehavioralSubgamePerfect_iff]
  constructor
  · intro perfect history proper who alternative
    have bound := perfect history proper who (setup.behavioralPolicyEquiv admission who alternative)
    rw [← Profile.map_update, protocol_behavioralContinuationValue_eq,
      protocol_behavioralContinuationValue_eq] at bound
    exact bound
  · intro optimal history proper who alternative
    obtain ⟨sourceAlternative, rfl⟩ :=
      (setup.behavioralPolicyEquiv admission who).surjective alternative
    rw [← Profile.map_update, protocol_behavioralContinuationValue_eq,
      protocol_behavioralContinuationValue_eq]
    exact optimal history proper who sourceAlternative

end Setup
end Vegas.SourceProgram
