/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolEvaluation
import GameTheoryExtensions.Protocol.Continuation

/-! # Source payoffs and canonical subgame perfection

The source protocol uses the shared definition of proper subgames. These
theorems let a source proof evaluate a continuation with `SourceProgram.runFrom` and replace
one admitted source policy, without introducing a second equilibrium predicate.
The bridge is for pure policies, with the source's stochastic public samples.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

/-- The admission interface restricts both prescribed policies and deviations.
Its legal histories are supplied separately by `executionProtocol`. -/
def admittedPureSignature (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) : GameSignature Player where
  Strategy who := { policy : PurePolicy who program // policy.Admitted program admission }
  Outcome := State L program.terminalCtx

/-- The existing source payoff read on terminal protocol histories. The value
at an unfinished history is immaterial to the terminating evaluator. -/
def protocolUtility (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    (utility : State L program.terminalCtx → Player → ℝ) :
    (executionProtocol program admission initial).History → Player → ℝ :=
  fun history who => (ProtocolState.readout program history.state).elim 0 (utility · who)

/-- Canonical backward value is exactly the expectation of the existing source
continuation law, at every legal history and for any terminal-store utility. -/
theorem protocol_continuationValue_eq (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    (profile : Profile (admittedPureSignature program admission))
    (utility : State L program.terminalCtx → Player → ℝ)
    (history : (executionProtocol program admission initial).History) (who : Player) :
    (executionProtocol program admission initial).historyBackwardValue
        (protocol_terminates program admission initial)
        ((informationModel program admission initial).historyChooser
          (Profile.map (target := (informationModel program admission initial).strategicSignature)
            (fun who => purePolicyEquiv program admission initial who) profile))
        (fun final => protocolUtility program admission initial utility final who) history =
      (ProtocolState.continuationLaw program
        (fun who => (profile who).1.toBehavioral program) history.state).expect
        (utility · who) := by
  rw [(informationModel program admission initial).historyBackwardValue_eq_expect_runFrom_of_bound
    (protocol_terminates program admission initial) (protocol_bounded program admission initial)]
  have law := protocol_runFrom_eq program admission initial (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount program) history
    (by have count := protocol_history_length program admission initial history.trace; omega)
  have values := congrArg
    (fun law => law.expect (fun state => state.elim 0 (utility · who))) law
  simp only [FinDist.expect_map, Option.elim_some] at values
  convert values using 1
  rfl

/-- Source-facing characterization of the canonical SPE predicate. In
particular, every legal protocol deviation is represented by one whole,
information-local admitted source policy; opponents are unchanged. -/
theorem protocol_isSubgamePerfect_iff (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    (profile : Profile (admittedPureSignature program admission))
    (utility : State L program.terminalCtx → Player → ℝ) :
    (informationModel program admission initial).IsSubgamePerfect
        (protocol_terminates program admission initial)
        (Profile.map (fun who => purePolicyEquiv program admission initial who) profile)
        (protocolUtility program admission initial utility) ↔
      ∀ history, (informationModel program admission initial).IsSubgameRoot history →
        ∀ who (alternative : (admittedPureSignature program admission).Strategy who),
          (ProtocolState.continuationLaw program
            (fun player => (Profile.update profile who alternative player).1.toBehavioral program)
            history.state).expect (utility · who) ≤
          (ProtocolState.continuationLaw program
            (fun player => (profile player).1.toBehavioral program)
            history.state).expect (utility · who) := by
  constructor
  · intro perfect history proper who alternative
    have bound := perfect history proper who
      (purePolicyEquiv program admission initial who alternative)
    rw [← Profile.map_update, protocol_continuationValue_eq,
      protocol_continuationValue_eq] at bound
    exact bound
  · intro optimal history proper who alternative
    obtain ⟨sourceAlternative, rfl⟩ :=
      (purePolicyEquiv program admission initial who).surjective alternative
    rw [← Profile.map_update, protocol_continuationValue_eq, protocol_continuationValue_eq]
    exact optimal history proper who sourceAlternative

end Vegas.SourceProgram
