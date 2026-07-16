/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Strategic

/-!
# Checkpoint-aligned source/frontier behavioral bridge

Checkpoint-aligned source play uses the canonical frontier information surface
and observes completed frontier histories through the compiler's source payoff
projection.
-/

namespace Vegas

open GameTheory
open Math.Probability

namespace ToEventGraph
namespace FrontierGameSemantics

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
variable {program : WFProgram P L} [FiniteDomains program]

/-- Source-facing checkpoint histories for behavioral play.  These are the
canonical frontier checkpoint histories, not raw primitive-event
linearizations. -/
abbrev SourceCheckpointBehavioralHistory
    (semantics : FrontierGameSemantics program) : Type :=
  semantics.BehavioralHistory

/-- Source-facing checkpoint information states.  This is the strategic
decision surface used by the checkpoint-aligned source game. -/
abbrev SourceCheckpointInfoState
    (semantics : FrontierGameSemantics program) (player : P) : Type :=
  (semantics.behavioral.view).ReachableInfoState semantics.horizon player

/-- Source-facing checkpoint behavioral strategies. -/
abbrev SourceCheckpointBehavioralStrategy
    (semantics : FrontierGameSemantics program) (player : P) : Type :=
  (semantics.behavioral.view).BoundedBehavioralStrategy
    semantics.horizon player

/-- Source-facing checkpoint behavioral profiles. -/
abbrev SourceCheckpointBehavioralProfile
    (semantics : FrontierGameSemantics program) : Type :=
  ∀ player, semantics.SourceCheckpointBehavioralStrategy player

/-- Source-payoff projection of a completed behavioral checkpoint history.

This is the checkpoint-aligned source outcome surface: histories are the
canonical frontier checkpoint histories, while outcomes are read back through
the compiler's source payoff projection. -/
noncomputable def sourceCheckpointBehavioralOutcome
    (semantics : FrontierGameSemantics program)
    (history : semantics.SourceCheckpointBehavioralHistory) :
    Option (Outcome P) :=
  ToEventGraph.sourceOutcomeOptionAtHistory program.core history

/-- Source-checkpoint behavioral kernel: run the canonical behavioral frontier
history kernel, then read each completed checkpoint history through the source
payoff projection.  The strategy carrier is checkpoint-local, matching the
canonical frontier information surface rather than raw source `LStep`
linearizations. -/
noncomputable def sourceCheckpointBehavioralKernel
    (semantics : FrontierGameSemantics program)
    (profile : semantics.SourceCheckpointBehavioralProfile) :
    PMF (Option (Outcome P)) :=
  PMF.map (semantics.sourceCheckpointBehavioralOutcome)
    (semantics.behavioralHistoryKernel profile)

/-- Utility for source-checkpoint optional outcomes.  The `none` branch is the
bounded cutoff branch and has zero support at the completed horizon. -/
noncomputable def sourceCheckpointOptionUtility
    (_semantics : FrontierGameSemantics program) :
    Option (Outcome P) → Payoff P
  | some outcome => fun who => (outcome who : ℝ)
  | none => 0

/-- Checkpoint-aligned source behavioral game.

This is the source-facing strategic game that matches the canonical frontier
checkpoint information surface.  Its outcomes are not primitive-machine
outcomes; they are source payoff outcomes reconstructed from completed
checkpoint histories. -/
noncomputable def sourceCheckpointBehavioralGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P where
  Strategy := semantics.SourceCheckpointBehavioralStrategy
  Outcome := Option (Outcome P)
  utility := semantics.sourceCheckpointOptionUtility
  outcomeKernel := semantics.sourceCheckpointBehavioralKernel

@[simp] theorem sourceCheckpointBehavioralGame_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (profile : semantics.sourceCheckpointBehavioralGame.Profile) :
    semantics.sourceCheckpointBehavioralGame.outcomeKernel profile =
      semantics.sourceCheckpointBehavioralKernel profile := rfl

/-- The checkpoint-aligned source behavioral kernel is exactly the option-valued
completed behavioral frontier kernel. -/
theorem sourceCheckpointBehavioralKernel_eq_optionOutcomeKernel
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    semantics.sourceCheckpointBehavioralKernel profile =
      semantics.behavioral.optionOutcomeKernel profile := by
  exact
    (semantics.behavioralOptionOutcomeKernel_eq_sourceMap profile).symm

/-- The checkpoint-aligned source behavioral kernel is the completed behavioral
frontier outcome kernel observed through `some`. -/
theorem sourceCheckpointBehavioralKernel_eq_map_some_behavioralOutcomeKernel
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    semantics.sourceCheckpointBehavioralKernel profile =
      PMF.map some (semantics.behavioralGame.outcomeKernel profile) := by
  rw [semantics.sourceCheckpointBehavioralKernel_eq_optionOutcomeKernel profile]
  change
    semantics.behavioral.optionOutcomeKernel profile =
      PMF.map some
        (eraseNonePMF (semantics.behavioral.optionOutcomeKernel profile)
          (fun result hresult =>
            semantics.behavioral.optionOutcomeKernel_support_some
              profile hresult))
  rw [eraseNonePMF_map_some]

/-- Checkpoint-aligned source behavioral play and canonical behavioral
frontier play are Nash-deviation bisimilar when both are observed as optional
source payoff outcomes. -/
noncomputable def sourceCheckpointBehavioralNashDeviationBisimulation
    (semantics : FrontierGameSemantics program) :
    KernelGame.NashDeviationBisimulation
      semantics.sourceCheckpointBehavioralGame semantics.behavioralGame
      (Option (Outcome P)) where
  viewG := { observe := fun _ => id }
  viewH := { observe := fun _ => some }
  rel := fun sourceProfile frontierProfile =>
    sourceProfile = frontierProfile
  law_eq := by
    intro sourceProfile frontierProfile hrel _
    subst frontierProfile
    dsimp [GameForm.ViewFamily.plaw]
    exact
      (PMF.map_id
        (semantics.sourceCheckpointBehavioralKernel sourceProfile)).trans
        (semantics.sourceCheckpointBehavioralKernel_eq_map_some_behavioralOutcomeKernel
          sourceProfile)
  simulate_target_deviation := by
    intro sourceProfile frontierProfile hrel who frontierDeviation
    subst frontierProfile
    refine ⟨frontierDeviation, ?_⟩
    dsimp [GameForm.ViewFamily.plaw]
    exact
      (PMF.map_id
        (semantics.sourceCheckpointBehavioralKernel
          (Function.update sourceProfile who frontierDeviation))).trans
        (semantics.sourceCheckpointBehavioralKernel_eq_map_some_behavioralOutcomeKernel
          (Function.update sourceProfile who frontierDeviation))
  simulate_source_deviation := by
    intro sourceProfile frontierProfile hrel who sourceDeviation
    subst frontierProfile
    refine ⟨sourceDeviation, ?_⟩
    dsimp [GameForm.ViewFamily.plaw]
    exact
      (PMF.map_id
        (semantics.sourceCheckpointBehavioralKernel
          (Function.update sourceProfile who sourceDeviation))).trans
        (semantics.sourceCheckpointBehavioralKernel_eq_map_some_behavioralOutcomeKernel
          (Function.update sourceProfile who sourceDeviation))

end FrontierGameSemantics
end ToEventGraph

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Program-facing checkpoint source histories for behavioral play. -/
abbrev SourceCheckpointBehavioralHistory
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  program.frontierSemantics.SourceCheckpointBehavioralHistory

/-- Program-facing checkpoint source information states. -/
abbrev SourceCheckpointInfoState
    (program : WFProgram P L) [FiniteDomains program] (player : P) : Type :=
  program.frontierSemantics.SourceCheckpointInfoState player

/-- Program-facing checkpoint source behavioral strategies. -/
abbrev SourceCheckpointBehavioralStrategy
    (program : WFProgram P L) [FiniteDomains program] (player : P) : Type :=
  program.frontierSemantics.SourceCheckpointBehavioralStrategy player

/-- Program-facing checkpoint source behavioral profiles. -/
abbrev SourceCheckpointBehavioralProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  program.frontierSemantics.SourceCheckpointBehavioralProfile

/-- Program-facing checkpoint-aligned source behavioral game.  It uses the
canonical frontier checkpoint information surface and reads completed histories
through the compiler's source payoff projection. -/
noncomputable def sourceCheckpointBehavioralGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.sourceCheckpointBehavioralGame

@[simp] theorem sourceCheckpointBehavioralGame_outcomeKernel
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.sourceCheckpointBehavioralGame.Profile) :
    program.sourceCheckpointBehavioralGame.outcomeKernel profile =
      program.frontierSemantics.sourceCheckpointBehavioralKernel profile := rfl

/-- Program-facing law equality: the source-checkpoint behavioral kernel is the
canonical behavioral frontier kernel observed through `some`. -/
theorem sourceCheckpointBehavioralGame_outcomeKernel_eq_map_some
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.sourceCheckpointBehavioralGame.Profile) :
    program.sourceCheckpointBehavioralGame.outcomeKernel profile =
      PMF.map some
        (program.behavioralFrontierGame.outcomeKernel profile) :=
  program.frontierSemantics
    |>.sourceCheckpointBehavioralKernel_eq_map_some_behavioralOutcomeKernel
      profile

/-- Program-facing source-checkpoint/behavioral-frontier Nash-deviation
bisimulation. -/
noncomputable def sourceCheckpointBehavioralFrontierNashDeviationBisimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationBisimulation
      program.sourceCheckpointBehavioralGame program.behavioralFrontierGame
      (Option (Outcome P)) :=
  program.frontierSemantics
    |>.sourceCheckpointBehavioralNashDeviationBisimulation

end WFProgram

end Vegas
