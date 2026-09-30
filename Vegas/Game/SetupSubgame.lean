/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceSubgame
import Vegas.Source.SetupProtocolEvaluation

/-! # Subgame perfection with private initial types

The shared protocol predicate is read against the source's own continuation
law. Utilities may inspect persistent types jointly with public results. The
history tree includes the prior, so a hidden draw is not assumed to identify
a proper subgame. This bridge quantifies over pure policy replacements.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def protocolUtility (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (utility : State L setup.program.terminalCtx → Player → ℝ) :
    (setup.executionProtocol admission).History → Player → ℝ :=
  fun history who => (setup.protocolReadout history.state).elim 0 (utility · who)

theorem protocol_continuationValue_eq (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : Profile (admittedPureSignature setup.program admission))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (history : (setup.executionProtocol admission).History) (who : Player) :
    (setup.executionProtocol admission).historyBackwardValue
        (setup.protocol_terminates admission).wellFoundedHistories
        ((setup.informationModel admission).historyChooser
          (Profile.map (target := (setup.informationModel admission).strategicSignature)
            (fun who => setup.purePolicyEquiv admission who) profile))
        (fun final => setup.protocolUtility admission utility final who) history =
      expect (setup.continuationLaw
        (fun who => (profile who).1.toBehavioral setup.program) history.state)
        (utility · who) := by
  rw [(setup.informationModel admission).historyBackwardValue_eq_expect_runFrom_of_bound
    (setup.protocol_terminates admission).wellFoundedHistories (setup.protocol_bounded admission)]
  have law := setup.protocol_runFrom_eq admission (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount setup.program + 1) history
    (by have count := setup.protocol_history_length admission history.trace; omega)
  have values := congrArg
    (fun law => expect law (fun state => state.elim 0 (utility · who))) law
  simp only [expect_map, Function.comp_def, Option.elim_some] at values
  convert values using 1
  rfl

/-- Pure policies branch only at chance and at the initial draw, so with a
finitely supported initial law every canonical continuation law of a pure
profile is finitely supported and every utility is integrable. -/
theorem protocol_backwardLaw_integrable (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    [setup.FiniteInitialLaw]
    (profile : Profile (admittedPureSignature setup.program admission))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (history : (setup.executionProtocol admission).History) (who : Player) :
    PayoffIntegrable
      ((setup.executionProtocol admission).historyBackwardLaw
        (setup.protocol_terminates admission).wellFoundedHistories
        ((setup.informationModel admission).historyChooser
          (Profile.map (target := (setup.informationModel admission).strategicSignature)
            (fun who => setup.purePolicyEquiv admission who) profile)) history)
      (fun final => setup.protocolUtility admission utility final who) := by
  rw [(setup.executionProtocol admission).historyBackwardLaw_eq_runHistoryFor
    ((setup.executionProtocol admission).stopsHistoryWithin_of_bound
      (setup.protocol_bounded admission) _ _)]
  have law := setup.protocol_runFrom_eq admission (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount setup.program + 1) history
    (by have count := setup.protocol_history_length admission history.trace; omega)
  have finite : (((setup.informationModel admission).runFrom
      (fun who => setup.toProtocolPolicy admission who (profile who).1 (profile who).2)
        (instructionCount setup.program + 1) history).map
          (fun final => setup.protocolReadout final.state)).support.Finite := by
    rw [law, PMF.support_map]
    exact (setup.continuationLaw_support_finite _
      (PurePolicy.profileFiniteSupport setup.program fun who => (profile who).1) _).image _
  have integrable := (payoffIntegrable_map_iff _ _ (fun state => state.elim 0 (utility · who))).mp
    (payoffIntegrable_of_finite_support _ _ finite)
  convert integrable using 1
  · rfl
  · funext final
    rfl

/-- Proper-root closure is tested in the game containing all setup draws;
the payoff and the retained prefix are never resampled for a deviation. -/
theorem protocol_isSubgamePerfect_iff (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    [setup.FiniteInitialLaw]
    (profile : Profile (admittedPureSignature setup.program admission))
    (utility : State L setup.program.terminalCtx → Player → ℝ) :
    (setup.informationModel admission).IsSubgamePerfect
        (setup.protocol_terminates admission).wellFoundedHistories
        (Profile.map (fun who => setup.purePolicyEquiv admission who) profile)
        (setup.protocolUtility admission utility) ↔
      ∀ history, (setup.informationModel admission).IsSubgameRoot history →
        ∀ who (alternative : (admittedPureSignature setup.program admission).Strategy who),
          expect (setup.continuationLaw
            (fun player =>
              (Profile.update profile who alternative player).1.toBehavioral setup.program)
            history.state) (utility · who) ≤
          expect (setup.continuationLaw
            (fun player => (profile player).1.toBehavioral setup.program)
            history.state) (utility · who) := by
  constructor
  · intro perfect history proper who alternative
    have bound :=
      (perfect history proper who (setup.purePolicyEquiv admission who alternative)).2.2
    rw [← Profile.map_update, ExecutionProtocol.historyBackwardExtendedValue_le_iff _
      (setup.protocol_backwardLaw_integrable admission _ utility history who)
      (setup.protocol_backwardLaw_integrable admission profile utility history who),
      protocol_continuationValue_eq, protocol_continuationValue_eq] at bound
    exact bound
  · intro optimal history proper who alternative
    obtain ⟨sourceAlternative, rfl⟩ := (setup.purePolicyEquiv admission who).surjective alternative
    rw [← Profile.map_update]
    refine ⟨hasExpectation_of_payoffIntegrable
        (setup.protocol_backwardLaw_integrable admission _ utility history who),
      hasExpectation_of_payoffIntegrable
        (setup.protocol_backwardLaw_integrable admission profile utility history who), ?_⟩
    rw [ExecutionProtocol.historyBackwardExtendedValue_le_iff _
      (setup.protocol_backwardLaw_integrable admission _ utility history who)
      (setup.protocol_backwardLaw_integrable admission profile utility history who),
      protocol_continuationValue_eq, protocol_continuationValue_eq]
    exact optimal history proper who sourceAlternative

end Vegas.SourceProgram.Setup
