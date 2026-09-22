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
        (setup.protocol_terminates admission)
        ((setup.informationModel admission).historyChooser
          (Profile.map (target := (setup.informationModel admission).strategicSignature)
            (fun who => setup.purePolicyEquiv admission who) profile))
        (fun final => setup.protocolUtility admission utility final who) history =
      (setup.continuationLaw
        (fun who => (profile who).1.toBehavioral setup.program) history.state).expect
        (utility · who) := by
  rw [(setup.informationModel admission).historyBackwardValue_eq_expect_runFrom_of_bound
    (setup.protocol_terminates admission) (setup.protocol_bounded admission)]
  have law := setup.protocol_runFrom_eq admission (fun who => (profile who).1)
    (fun who => (profile who).2) (instructionCount setup.program + 1) history
    (by have count := setup.protocol_history_length admission history.trace; omega)
  have values := congrArg
    (fun law => law.expect (fun state => state.elim 0 (utility · who))) law
  simp only [FinDist.expect_map, Option.elim_some] at values
  convert values using 1
  rfl

/-- Proper-root closure is tested in the game containing all setup draws;
the payoff and the retained prefix are never resampled for a deviation. -/
theorem protocol_isSubgamePerfect_iff (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : Profile (admittedPureSignature setup.program admission))
    (utility : State L setup.program.terminalCtx → Player → ℝ) :
    (setup.informationModel admission).IsSubgamePerfect
        (setup.protocol_terminates admission)
        (Profile.map (fun who => setup.purePolicyEquiv admission who) profile)
        (setup.protocolUtility admission utility) ↔
      ∀ history, (setup.informationModel admission).IsSubgameRoot history →
        ∀ who (alternative : (admittedPureSignature setup.program admission).Strategy who),
          (setup.continuationLaw
            (fun player =>
              (Profile.update profile who alternative player).1.toBehavioral setup.program)
            history.state).expect (utility · who) ≤
          (setup.continuationLaw (fun player => (profile player).1.toBehavioral setup.program)
            history.state).expect (utility · who) := by
  constructor
  · intro perfect history proper who alternative
    have bound := perfect history proper who (setup.purePolicyEquiv admission who alternative)
    rw [← Profile.map_update, protocol_continuationValue_eq,
      protocol_continuationValue_eq] at bound
    exact bound
  · intro optimal history proper who alternative
    obtain ⟨sourceAlternative, rfl⟩ := (setup.purePolicyEquiv admission who).surjective alternative
    rw [← Profile.map_update, protocol_continuationValue_eq, protocol_continuationValue_eq]
    exact optimal history proper who sourceAlternative

end Vegas.SourceProgram.Setup
