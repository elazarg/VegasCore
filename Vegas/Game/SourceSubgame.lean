/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolEvaluation
import GameTheory.Protocol.Continuation

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
        (protocol_terminates program admission initial).wellFoundedHistories
        ((informationModel program admission initial).historyChooser
          (Profile.map (target := (informationModel program admission initial).strategicSignature)
            (fun who => purePolicyEquiv program admission initial who) profile))
        (fun final => protocolUtility program admission initial utility final who) history =
      expect (ProtocolState.continuationLaw program
        (fun who => (profile who).1.toBehavioral program) history.state)
        (utility · who) := by
  rw [(informationModel program admission initial).historyBackwardValue_eq_expect_runFrom_of_bound
    (protocol_terminates program admission initial).wellFoundedHistories
    (protocol_bounded program admission initial)]
  have law := protocol_runFrom_eq program admission initial (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount program) history
    (by have count := protocol_history_length program admission initial history.trace; omega)
  have values := congrArg
    (fun law => expect law (fun state => state.elim 0 (utility · who))) law
  simp only [expect_map, Function.comp_def, Option.elim_some] at values
  convert values using 1
  rfl

/-- Pure source policies branch only at chance, so every canonical continuation
law of a pure profile is finitely supported and every utility is integrable. -/
theorem protocol_backwardLaw_integrable (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    (profile : Profile (admittedPureSignature program admission))
    (utility : State L program.terminalCtx → Player → ℝ)
    (history : (executionProtocol program admission initial).History) (who : Player) :
    PayoffIntegrable
      ((executionProtocol program admission initial).historyBackwardLaw
        (protocol_terminates program admission initial).wellFoundedHistories
        ((informationModel program admission initial).historyChooser
          (Profile.map (target := (informationModel program admission initial).strategicSignature)
            (fun who => purePolicyEquiv program admission initial who) profile)) history)
      (fun final => protocolUtility program admission initial utility final who) := by
  rw [(executionProtocol program admission initial).historyBackwardLaw_eq_runHistoryFor
    ((executionProtocol program admission initial).stopsHistoryWithin_of_bound
      (protocol_bounded program admission initial) _ _)]
  have law := protocol_runFrom_eq program admission initial (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount program) history
    (by have count := protocol_history_length program admission initial history.trace; omega)
  have finite : (((informationModel program admission initial).runFrom
      (fun who => (profile who).1.toProtocol program admission (profile who).2)
        (instructionCount program) history).map
          (fun final => ProtocolState.readout program final.state)).support.Finite := by
    rw [law, PMF.support_map]
    exact (ProtocolState.continuationLaw_support_finite program _
      (PurePolicy.profileFiniteSupport program fun who => (profile who).1) _).image _
  have integrable := (payoffIntegrable_map_iff _ _ (fun state => state.elim 0 (utility · who))).mp
    (payoffIntegrable_of_finite_support _ _ finite)
  convert integrable using 1
  · rfl
  · funext final
    rfl

/-- Source-facing characterization of the canonical SPE predicate. In
particular, every legal protocol deviation is represented by one whole,
information-local admitted source policy; opponents are unchanged. -/
theorem protocol_isSubgamePerfect_iff (program : SourceProgram Player L Γ O)
    (admission : CommitmentInterface program) (initial : Config Player L Γ)
    (profile : Profile (admittedPureSignature program admission))
    (utility : State L program.terminalCtx → Player → ℝ) :
    (informationModel program admission initial).IsSubgamePerfect
        (protocol_terminates program admission initial).wellFoundedHistories
        (Profile.map (fun who => purePolicyEquiv program admission initial who) profile)
        (protocolUtility program admission initial utility) ↔
      ∀ history, (informationModel program admission initial).IsSubgameRoot history →
        ∀ who (alternative : (admittedPureSignature program admission).Strategy who),
          expect (ProtocolState.continuationLaw program
            (fun player => (Profile.update profile who alternative player).1.toBehavioral program)
            history.state) (utility · who) ≤
          expect (ProtocolState.continuationLaw program
            (fun player => (profile player).1.toBehavioral program)
            history.state) (utility · who) := by
  constructor
  · intro perfect history proper who alternative
    have bound := (perfect history proper who
      (purePolicyEquiv program admission initial who alternative)).2.2
    rw [← Profile.map_update, ExecutionProtocol.historyBackwardExtendedValue_le_iff _
      (protocol_backwardLaw_integrable program admission initial _ utility history who)
      (protocol_backwardLaw_integrable program admission initial profile utility history who),
      protocol_continuationValue_eq, protocol_continuationValue_eq] at bound
    exact bound
  · intro optimal history proper who alternative
    obtain ⟨sourceAlternative, rfl⟩ :=
      (purePolicyEquiv program admission initial who).surjective alternative
    rw [← Profile.map_update]
    refine ⟨hasExpectation_of_payoffIntegrable
        (protocol_backwardLaw_integrable program admission initial _ utility history who),
      hasExpectation_of_payoffIntegrable
        (protocol_backwardLaw_integrable program admission initial profile utility history who),
      ?_⟩
    rw [ExecutionProtocol.historyBackwardExtendedValue_le_iff _
      (protocol_backwardLaw_integrable program admission initial _ utility history who)
      (protocol_backwardLaw_integrable program admission initial profile utility history who),
      protocol_continuationValue_eq, protocol_continuationValue_eq]
    exact optimal history proper who sourceAlternative

end Vegas.SourceProgram
