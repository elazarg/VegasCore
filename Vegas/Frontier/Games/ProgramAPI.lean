/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.Games.Semantics

/-!
# Program-facing compiled frontier games: `WFProgram` API

The `WFProgram`-facing entry points that expose the canonical completed-frontier
game semantics for a checked program.
-/

namespace Vegas

namespace WFProgram

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}


/-- Program-facing entry point for the canonical completed-frontier strategic
semantics. -/
noncomputable def frontierSemantics
    (program : WFProgram P L) [FiniteDomains program] :
    ToEventGraph.FrontierGameSemantics program :=
  ToEventGraph.canonicalFrontierGameSemantics program

/-- Completed pure-strategy frontier game of a checked program. -/
noncomputable def pureFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.pureGame

/-- Completed behavioral-strategy frontier game of a checked program. -/
noncomputable def behavioralFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.behavioralGame

/-- Mixed extension of the completed pure-strategy frontier game. -/
noncomputable def mixedPureFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.mixedPureGame

/-- Pure-strategy game form over completed frontier histories. -/
noncomputable def pureFrontierHistoryGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.pureHistoryGameForm

/-- Behavioral-strategy game form over completed frontier histories. -/
noncomputable def behavioralFrontierHistoryGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.behavioralHistoryGameForm

/-- Pure-strategy game form over public checkpoint-observation histories. -/
noncomputable def pureFrontierPublicHistoryGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.purePublicHistoryGameForm

/-- Behavioral-strategy game form over public checkpoint-observation histories. -/
noncomputable def behavioralFrontierPublicHistoryGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.behavioralPublicHistoryGameForm

/-- Pure-strategy game form over terminal public graph observations. -/
noncomputable def pureFrontierTerminalPublicGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.pureTerminalPublicGameForm

/-- Behavioral-strategy game form over terminal public graph observations. -/
noncomputable def behavioralFrontierTerminalPublicGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.behavioralTerminalPublicGameForm

/-- Completed pure-strategy frontier-history game. -/
noncomputable def pureFrontierHistoryKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.pureHistoryKernelGame

/-- Completed behavioral-strategy frontier-history game. -/
noncomputable def behavioralFrontierHistoryKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.behavioralHistoryKernelGame

/-- Completed pure-strategy game over terminal public graph observations. -/
noncomputable def pureTerminalPublicFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.pureTerminalPublicKernelGame

/-- Completed behavioral-strategy game over terminal public graph observations. -/
noncomputable def behavioralTerminalPublicFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.behavioralTerminalPublicKernelGame

/-- Mixed extension of the terminal-public pure frontier game. -/
noncomputable def mixedPureTerminalPublicFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.mixedPureTerminalPublicGame

/-- Pure frontier strategies of a checked program. -/
abbrev PureFrontierStrategy
    (program : WFProgram P L) [FiniteDomains program] (player : P) : Type :=
  (program.pureFrontierGame).Strategy player

/-- Behavioral frontier strategies of a checked program. -/
abbrev BehavioralFrontierStrategy
    (program : WFProgram P L) [FiniteDomains program] (player : P) : Type :=
  (program.behavioralFrontierGame).Strategy player

/-- Mixed-pure frontier strategies of a checked program. -/
abbrev MixedPureFrontierStrategy
    (program : WFProgram P L) [FiniteDomains program] (player : P) : Type :=
  (program.mixedPureFrontierGame).Strategy player

/-- Pure frontier strategy profiles of a checked program. -/
abbrev PureFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.pureFrontierGame).Profile

/-- Behavioral frontier strategy profiles of a checked program. -/
abbrev BehavioralFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.behavioralFrontierGame).Profile

/-- Mixed pure frontier strategy profiles of a checked program. -/
abbrev MixedPureFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.mixedPureFrontierGame).Profile

/-- A pure frontier profile embedded as a behavioral profile has the same
completed-game outcome kernel. -/
theorem pureToBehavioralFrontierOutcomeKernel
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.behavioralFrontierGame.outcomeKernel
        ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
          program.frontierSemantics.horizon profile) =
      program.pureFrontierGame.outcomeKernel profile := by
  simpa [PureFrontierProfile, BehavioralFrontierProfile,
    pureFrontierGame, behavioralFrontierGame, frontierSemantics] using
    program.frontierSemantics.pureToBehavioralOutcomeKernel profile

/-- A pure frontier profile embedded as a behavioral profile has the same joint
utility distribution. -/
theorem pureToBehavioralFrontierUdist
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.behavioralFrontierGame.udist
        ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
          program.frontierSemantics.horizon profile) =
      program.pureFrontierGame.udist profile := by
  simpa [PureFrontierProfile, BehavioralFrontierProfile,
    pureFrontierGame, behavioralFrontierGame, frontierSemantics] using
    program.frontierSemantics.pureToBehavioralUdist profile

/-- Completed pure frontier histories of a checked program. -/
abbrev PureFrontierHistory
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  program.frontierSemantics.PureHistory

/-- Completed behavioral frontier histories of a checked program. -/
abbrev BehavioralFrontierHistory
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  program.frontierSemantics.BehavioralHistory

/-- The checked program's native frontier round view has an operational
primitive-event replay certificate for each supported strategic round. -/
theorem frontierView_operationallyCertified
    (program : WFProgram P L) [FiniteDomains program] :
    program.frontierSemantics.games.view.OperationallyCertified :=
  program.frontierSemantics.view_operationallyCertified

/-- Public checkpoint-observation histories of a checked program. -/
abbrev PublicFrontierHistory
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  program.frontierSemantics.PublicHistory

/-- Terminal public graph observations of a checked program. -/
abbrev TerminalPublicFrontierObservation
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  program.frontierSemantics.TerminalPublicObservation

/-- Pure terminal-public frontier strategy profiles of a checked program. -/
abbrev PureTerminalPublicFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.pureTerminalPublicFrontierGame).Profile

/-- Behavioral terminal-public frontier strategy profiles of a checked
program. -/
abbrev BehavioralTerminalPublicFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.behavioralTerminalPublicFrontierGame).Profile

/-- Mixed pure terminal-public frontier strategy profiles of a checked
program. -/
abbrev MixedPureTerminalPublicFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.mixedPureTerminalPublicFrontierGame).Profile

/-- Correlated pure frontier profiles of a checked program. -/
abbrev PureFrontierCorrelatedProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  PMF program.PureFrontierProfile

/-- Distributions over complete behavioral frontier profiles, used by
correlated-equilibrium predicates on the behavioral frontier game. This is not
a local behavioral recommendation device. -/
abbrev BehavioralFrontierCorrelatedProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  PMF program.BehavioralFrontierProfile

/-- Correlated terminal-public pure frontier profiles of a checked program. -/
abbrev PureTerminalPublicFrontierCorrelatedProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  PMF program.PureTerminalPublicFrontierProfile

/-- Distributions over complete terminal-public behavioral frontier profiles,
used by correlated-equilibrium predicates on the behavioral terminal-public
frontier game. This is not a local behavioral recommendation device. -/
abbrev BehavioralTerminalPublicFrontierCorrelatedProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  PMF program.BehavioralTerminalPublicFrontierProfile

/-- Finite carrier for a player's pure frontier strategies. -/
@[reducible]
noncomputable def pureFrontierStrategyFintype
    (program : WFProgram P L) [FiniteDomains program] (player : P) :
    Fintype (program.PureFrontierStrategy player) :=
  program.frontierSemantics.pureStrategyFintype player

/-- Pure frontier strategy spaces are nonempty for all players. -/
theorem pureFrontierStrategyNonempty
    (program : WFProgram P L) [FiniteDomains program] (player : P) :
    Nonempty (program.PureFrontierStrategy player) :=
  program.frontierSemantics.pureStrategyNonempty player

/-- Expected utility in the pure completed-frontier game. -/
noncomputable def pureFrontierEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) (player : P) : ℝ :=
  program.pureFrontierGame.eu profile player

/-- Expected utility in the behavioral completed-frontier game. -/
noncomputable def behavioralFrontierEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) (player : P) : ℝ :=
  program.behavioralFrontierGame.eu profile player

/-- Expected utility in the pure terminal-public frontier game. -/
noncomputable def pureTerminalPublicFrontierEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureTerminalPublicFrontierProfile)
    (player : P) : ℝ :=
  program.pureTerminalPublicFrontierGame.eu profile player

/-- Expected utility in the behavioral terminal-public frontier game. -/
noncomputable def behavioralTerminalPublicFrontierEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralTerminalPublicFrontierProfile)
    (player : P) : ℝ :=
  program.behavioralTerminalPublicFrontierGame.eu profile player

/-- Correlated expected utility in the pure completed-frontier game. -/
noncomputable def pureFrontierCorrelatedEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierCorrelatedProfile) (player : P) : ℝ :=
  program.pureFrontierGame.correlatedEu profile player

/-- Correlated expected utility in the behavioral completed-frontier game. -/
noncomputable def behavioralFrontierCorrelatedEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierCorrelatedProfile)
    (player : P) : ℝ :=
  program.behavioralFrontierGame.correlatedEu profile player

/-- Nash predicate for the pure completed-frontier game. -/
def PureFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) : Prop :=
  program.pureFrontierGame.IsNash profile

/-- Nash predicate for the behavioral completed-frontier game. -/
def BehavioralFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) : Prop :=
  program.behavioralFrontierGame.IsNash profile

/-- Nash predicate for the mixed pure completed-frontier game. -/
def MixedPureFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.MixedPureFrontierProfile) : Prop :=
  program.mixedPureFrontierGame.IsNash profile

/-- Nash predicate for the pure terminal-public frontier game. -/
def PureTerminalPublicFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureTerminalPublicFrontierProfile) : Prop :=
  program.pureTerminalPublicFrontierGame.IsNash profile

/-- Nash predicate for the behavioral terminal-public frontier game. -/
def BehavioralTerminalPublicFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralTerminalPublicFrontierProfile) : Prop :=
  program.behavioralTerminalPublicFrontierGame.IsNash profile

/-- Nash predicate for the mixed pure terminal-public frontier game. -/
def MixedPureTerminalPublicFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.MixedPureTerminalPublicFrontierProfile) : Prop :=
  program.mixedPureTerminalPublicFrontierGame.IsNash profile

/-- Best-response predicate for behavioral frontier strategies. -/
def BehavioralFrontierBestResponse
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (profile : program.BehavioralFrontierProfile)
    (strategy : program.BehavioralFrontierStrategy player) : Prop :=
  program.behavioralFrontierGame.IsBestResponse player profile strategy

/-- Dominant-strategy predicate for behavioral frontier strategies. -/
def BehavioralFrontierDominant
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.BehavioralFrontierStrategy player) :
    Prop :=
  program.behavioralFrontierGame.IsDominant player strategy

/-- Strict Nash predicate for behavioral frontier profiles. -/
def BehavioralFrontierStrictNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) : Prop :=
  program.behavioralFrontierGame.IsStrictNash profile

/-- Strict dominant-strategy predicate for behavioral frontier strategies. -/
def BehavioralFrontierStrictDominant
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.BehavioralFrontierStrategy player) :
    Prop :=
  program.behavioralFrontierGame.IsStrictDominant player strategy

/-- Correlated-equilibrium predicate for behavioral frontier profiles. -/
def BehavioralFrontierCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierCorrelatedProfile) : Prop :=
  program.behavioralFrontierGame.IsCorrelatedEq profile

/-- Coarse-correlated-equilibrium predicate for behavioral frontier profiles. -/
def BehavioralFrontierCoarseCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierCorrelatedProfile) : Prop :=
  program.behavioralFrontierGame.IsCoarseCorrelatedEq profile

/-- Correlated-equilibrium predicate for pure frontier profiles. -/
def PureFrontierCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierCorrelatedProfile) : Prop :=
  program.pureFrontierGame.IsCorrelatedEq profile

/-- Coarse-correlated-equilibrium predicate for pure frontier profiles. -/
def PureFrontierCoarseCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierCorrelatedProfile) : Prop :=
  program.pureFrontierGame.IsCoarseCorrelatedEq profile

/-- Correlated-equilibrium predicate for terminal-public pure frontier
profiles. -/
def PureTerminalPublicFrontierCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureTerminalPublicFrontierCorrelatedProfile) : Prop :=
  program.pureTerminalPublicFrontierGame.IsCorrelatedEq profile

/-- Coarse-correlated-equilibrium predicate for terminal-public pure frontier
profiles. -/
def PureTerminalPublicFrontierCoarseCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureTerminalPublicFrontierCorrelatedProfile) : Prop :=
  program.pureTerminalPublicFrontierGame.IsCoarseCorrelatedEq profile

/-- Correlated-equilibrium predicate for terminal-public behavioral frontier
profiles. -/
def BehavioralTerminalPublicFrontierCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralTerminalPublicFrontierCorrelatedProfile) :
    Prop :=
  program.behavioralTerminalPublicFrontierGame.IsCorrelatedEq profile

/-- Coarse-correlated-equilibrium predicate for terminal-public behavioral
frontier profiles. -/
def BehavioralTerminalPublicFrontierCoarseCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralTerminalPublicFrontierCorrelatedProfile) :
    Prop :=
  program.behavioralTerminalPublicFrontierGame.IsCoarseCorrelatedEq profile

/-- Program-facing mixed-pure-to-behavioral deviation simulation type. -/
abbrev MixedPureToBehavioralFrontierDeviationSimulation
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  ToEventGraph.FrontierGameSemantics.MixedPureToBehavioralDeviationSimulation
    program.frontierSemantics

/-- Program-facing strategy/deviation-level Kuhn equivalence package. -/
abbrev FrontierKuhnStrategicEquivalence
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  ToEventGraph.FrontierGameSemantics.KuhnStrategicEquivalence
    program.frontierSemantics

/-- Canonical strategy/deviation-level Kuhn equivalence for the completed
frontier games of a checked program. -/
noncomputable def frontierKuhnStrategicEquivalence
    (program : WFProgram P L) [FiniteDomains program] :
    program.FrontierKuhnStrategicEquivalence :=
  program.frontierSemantics.kuhnStrategicEquivalence

/-- Product mixed pure-strategy profile induced by a behavioral frontier
profile. -/
noncomputable def behavioralFrontierToMixedPure
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    program.MixedPureFrontierProfile :=
  program.frontierSemantics.behavioralToMixedPure behavioral

/-- Canonical behavioral frontier profile realizing a mixed-pure frontier
profile by Kuhn's mixed-to-behavioral construction. -/
noncomputable def mixedPureToBehavioralFrontierProfile
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile) :
    program.BehavioralFrontierProfile :=
  program.frontierSemantics.mixedToBehavioralProfile mixed

/-- The canonical mixed-pure-to-behavioral frontier profile preserves the
completed-frontier outcome kernel. -/
theorem mixedPureToBehavioralFrontierProfile_outcomeKernel
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile) :
    program.behavioralFrontierGame.outcomeKernel
        (program.mixedPureToBehavioralFrontierProfile mixed) =
      program.mixedPureFrontierGame.outcomeKernel mixed := by
  exact program.frontierSemantics.mixedToBehavioralProfileOutcomeKernel mixed

/-- Program-facing canonical mixed-pure-to-behavioral deviation simulation. -/
noncomputable def canonicalMixedPureToBehavioralFrontierDeviationSimulation
    (program : WFProgram P L) [FiniteDomains program] :
    program.MixedPureToBehavioralFrontierDeviationSimulation :=
  program.frontierSemantics
    |>.canonicalMixedPureToBehavioralDeviationSimulation

/-- Every unilateral behavioral deviation from the canonical behavioral
realization of a mixed-pure frontier profile has a matching unilateral
mixed-pure deviation with the same completed-frontier outcome kernel. -/
theorem mixedPureFrontier_behavioralDeviation_to_mixedPure
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile)
    (who : P)
    (behavioralDeviation : program.BehavioralFrontierStrategy who) :
    ∃ mixedDeviation : program.MixedPureFrontierStrategy who,
      program.behavioralFrontierGame.outcomeKernel
          (Function.update
            (program.mixedPureToBehavioralFrontierProfile mixed)
            who behavioralDeviation) =
        program.mixedPureFrontierGame.outcomeKernel
          (Function.update mixed who mixedDeviation) := by
  refine
    ⟨program.frontierSemantics.behavioralStrategyToMixedPure
      who behavioralDeviation, ?_⟩
  simpa [frontierSemantics, behavioralFrontierGame, mixedPureFrontierGame,
    mixedPureToBehavioralFrontierProfile, MixedPureFrontierProfile,
    BehavioralFrontierStrategy, MixedPureFrontierStrategy] using
    program.frontierSemantics
      |>.mixedToBehavioralUnilateralDeviationOutcomeKernel
        mixed who behavioralDeviation

/-- Every unilateral mixed-pure deviation has a matching unilateral behavioral
deviation from the canonical behavioral realization, with the same
completed-frontier outcome kernel. -/
theorem mixedPureFrontier_mixedDeviation_to_behavioral
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile)
    (who : P)
    (mixedDeviation : program.MixedPureFrontierStrategy who) :
    ∃ behavioralDeviation : program.BehavioralFrontierStrategy who,
      program.mixedPureFrontierGame.outcomeKernel
          (Function.update mixed who mixedDeviation) =
        program.behavioralFrontierGame.outcomeKernel
          (Function.update
            (program.mixedPureToBehavioralFrontierProfile mixed)
            who behavioralDeviation) := by
  simpa [frontierSemantics, behavioralFrontierGame, mixedPureFrontierGame,
    mixedPureToBehavioralFrontierProfile, MixedPureFrontierProfile,
    BehavioralFrontierStrategy, MixedPureFrontierStrategy] using
    program.frontierSemantics
      |>.mixedToBehavioralMixedDeviationOutcomeKernel
        mixed who mixedDeviation

/-- Mixed pure strategies realize as behavioral strategies with the same
completed-frontier outcome kernel. -/
theorem mixedPureFrontier_to_behavioral
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile) :
    ∃ behavioral : program.BehavioralFrontierProfile,
      program.behavioralFrontierGame.outcomeKernel behavioral =
        program.mixedPureFrontierGame.outcomeKernel mixed := by
  exact
    ⟨program.mixedPureToBehavioralFrontierProfile mixed,
      program.mixedPureToBehavioralFrontierProfile_outcomeKernel mixed⟩

/-- Mixed pure strategies realize as behavioral strategies with the same
completed-frontier outcome kernel and expected utility. -/
theorem mixedPureFrontier_to_behavioral_eu
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile) :
    ∃ behavioral : program.BehavioralFrontierProfile,
      program.behavioralFrontierGame.outcomeKernel behavioral =
        program.mixedPureFrontierGame.outcomeKernel mixed ∧
      ∀ player,
        program.behavioralFrontierGame.eu behavioral player =
          program.mixedPureFrontierGame.eu mixed player := by
  simpa [frontierSemantics, behavioralFrontierGame, mixedPureFrontierGame,
    BehavioralFrontierProfile, MixedPureFrontierProfile] using
    program.frontierSemantics.mixedToBehavioralEU mixed

/-- Relation saying that a behavioral frontier profile realizes a mixed-pure
frontier profile with the same completed-game outcome kernel. -/
def MixedPureToBehavioralFrontierProfileRealizes
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile)
    (behavioral : program.BehavioralFrontierProfile) : Prop :=
  program.frontierSemantics.MixedPureToBehavioralProfileRealizes
    mixed behavioral

/-- Program-facing mixed-pure-to-behavioral realization relating profile laws
with the same correlated outcome law. This does not include the
deviation-preservation theorem needed for Nash transport. -/
noncomputable def mixedPureToBehavioralFrontierRealization
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.Realization
      program.mixedPureFrontierGame program.behavioralFrontierGame
      (GameForm.ViewFamily.const
        (F := program.mixedPureFrontierGame.toGameForm) (U := P) id)
      (GameForm.ViewFamily.const
        (F := program.behavioralFrontierGame.toGameForm) (U := P) id) :=
  program.frontierSemantics.mixedPureToBehavioralRealization

/-- Every mixed-pure frontier profile has a behavioral profile with the same
completed-game outcome kernel. -/
theorem mixedPureToBehavioralFrontierProfileRealizes_exists
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile) :
    ∃ behavioral : program.BehavioralFrontierProfile,
      program.MixedPureToBehavioralFrontierProfileRealizes
        mixed behavioral := by
  exact program.frontierSemantics
    |>.mixedPureToBehavioralProfileRealizes_exists mixed

/-- Behavioral frontier strategies induce product mixed pure strategies with
the same completed-frontier outcome kernel. -/
theorem behavioralFrontier_to_mixedPure_outcomeKernel
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    program.behavioralFrontierGame.outcomeKernel behavioral =
      program.mixedPureFrontierGame.outcomeKernel
        (program.behavioralFrontierToMixedPure behavioral) := by
  simpa [behavioralFrontierToMixedPure, frontierSemantics,
    behavioralFrontierGame, mixedPureFrontierGame,
    BehavioralFrontierProfile, MixedPureFrontierProfile] using
    program.frontierSemantics.behavioralToMixedPureOutcomeKernel behavioral

/-- Every unilateral behavioral deviation from an arbitrary behavioral
frontier profile has a matching unilateral mixed-pure deviation from the
profile induced by behavioral-to-product-mixed Kuhn realization. -/
theorem behavioralFrontier_deviation_to_mixedPure
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile)
    (who : P)
    (behavioralDeviation : program.BehavioralFrontierStrategy who) :
    ∃ mixedDeviation : program.MixedPureFrontierStrategy who,
      program.behavioralFrontierGame.outcomeKernel
          (Function.update behavioral who behavioralDeviation) =
        program.mixedPureFrontierGame.outcomeKernel
          (Function.update
            (program.behavioralFrontierToMixedPure behavioral)
            who mixedDeviation) := by
  classical
  let equivalence := program.frontierKuhnStrategicEquivalence
  exact equivalence.arbitrary_behavioral_deviation_to_mixed_deviation
    behavioral who behavioralDeviation

/-- Behavioral frontier strategies induce product mixed pure strategies with
the same joint utility distribution. -/
theorem behavioralFrontier_to_mixedPure_udist
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    program.behavioralFrontierGame.udist behavioral =
      program.mixedPureFrontierGame.udist
        (program.behavioralFrontierToMixedPure behavioral) := by
  change
    (program.behavioralFrontierGame.outcomeKernel behavioral).bind
        (fun outcome =>
          PMF.pure (program.behavioralFrontierGame.utility outcome)) =
      (program.mixedPureFrontierGame.outcomeKernel
          (program.behavioralFrontierToMixedPure behavioral)).bind
        (fun outcome =>
          PMF.pure (program.mixedPureFrontierGame.utility outcome))
  rw [program.behavioralFrontier_to_mixedPure_outcomeKernel behavioral]
  rfl

/-- Behavioral frontier strategies induce product mixed pure strategies with
the same expected utility. -/
theorem behavioralFrontier_to_mixedPure_eu
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    ∀ player,
      program.behavioralFrontierGame.eu behavioral player =
        program.mixedPureFrontierGame.eu
          (program.behavioralFrontierToMixedPure behavioral) player := by
  simpa [behavioralFrontierToMixedPure, frontierSemantics,
    behavioralFrontierGame, mixedPureFrontierGame,
    BehavioralFrontierProfile, MixedPureFrontierProfile] using
    program.frontierSemantics.behavioralToMixedPureEU behavioral

/-- Program-facing Nash deviation simulation for the proved
behavioral-to-product-mixed Kuhn direction. Its relation pairs a behavioral
frontier profile with its induced product mixed-pure frontier profile. -/
noncomputable def behavioralToMixedPureFrontierNashDeviationSimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationSimulation
      program.mixedPureFrontierGame program.behavioralFrontierGame
      program.mixedPureFrontierGame.Outcome :=
  program.frontierSemantics.behavioralToMixedPureNashDeviationSimulation

/-- Program-facing canonical mixed-pure-to-behavioral Nash deviation
simulation, obtained from the canonical mixed-pure behavioral realization. -/
noncomputable def mixedPureToBehavioralFrontierNashDeviationSimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationSimulation
      program.mixedPureFrontierGame program.behavioralFrontierGame
      program.mixedPureFrontierGame.Outcome :=
  program.canonicalMixedPureToBehavioralFrontierDeviationSimulation
    |>.toNashDeviationSimulation

/-- Program-facing canonical Kuhn strategic equivalence as a standard
`NashDeviationBisimulation` between the mixed-pure and behavioral completed
frontier games. -/
noncomputable def mixedPureBehavioralFrontierNashDeviationBisimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationBisimulation
      program.mixedPureFrontierGame program.behavioralFrontierGame
      program.mixedPureFrontierGame.Outcome :=
  program.frontierSemantics.mixedPureToBehavioralNashDeviationBisimulation

/-- Program-facing two-direction Kuhn outcome-equality schema for completed
frontier games. This packages the behavioral-to-product-mixed direction and
the mixed-pure-to-behavioral realizability direction at outcome-kernel level. -/
theorem frontierCompleteOutcomeKuhn
    (program : WFProgram P L) [FiniteDomains program] :
    GameTheory.Theorems.KuhnCompleteViaOutcome
      program.BehavioralFrontierProfile
      (∀ player, PMF (program.PureFrontierStrategy player))
      program.PureFrontierProfile
      program.pureFrontierGame.Outcome
      (fun behavioral =>
        Math.PMFProduct.pmfPi
          (program.behavioralFrontierToMixedPure behavioral))
      Math.PMFProduct.pmfPi
      program.behavioralFrontierGame.outcomeKernel
      program.pureFrontierGame.outcomeKernel := by
  exact program.frontierSemantics.games.completeOutcomeKuhn
    program.frontierSemantics.menus

/-- Behavioral frontier strategies realize as correlated distributions over
pure frontier profiles with the same completed-frontier outcome kernel. -/
theorem behavioralFrontier_to_correlatedPure
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    ∃ correlated : PMF program.PureFrontierProfile,
      program.behavioralFrontierGame.outcomeKernel behavioral =
        correlated.bind fun pureProfile =>
          program.pureFrontierGame.outcomeKernel pureProfile := by
  simpa [frontierSemantics, behavioralFrontierGame, pureFrontierGame,
    BehavioralFrontierProfile, PureFrontierProfile] using
    program.frontierSemantics.behavioralToCorrelatedPure behavioral

/-- Behavioral frontier strategies realize as correlated distributions over
pure frontier profiles with the same expected utility for one player, assuming
that player's payoff coordinate is bounded. -/
theorem behavioralFrontier_to_correlatedPure_eu_of_bounded
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile)
    (player : P) {C : ℝ}
    (hbd :
      ∀ outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C) :
    ∃ correlated : PMF program.PureFrontierProfile,
      program.behavioralFrontierGame.outcomeKernel behavioral =
        (correlated.bind fun pureProfile =>
          program.pureFrontierGame.outcomeKernel pureProfile) ∧
      program.behavioralFrontierGame.eu behavioral player =
        Math.Probability.expect correlated
          (fun pureProfile =>
            program.pureFrontierGame.eu pureProfile player) := by
  simpa [frontierSemantics, behavioralFrontierGame, pureFrontierGame,
    BehavioralFrontierProfile, PureFrontierProfile] using
    program.frontierSemantics
      |>.behavioralToCorrelatedPureEU_of_bounded behavioral player hbd

/-- A legal pure frontier strategy chooses an available optional move at every
reachable completed-frontier history. -/
theorem pureFrontierStrategy_chooses_available
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.PureFrontierStrategy player)
    (history : program.PureFrontierHistory) :
    strategy.1
        ((program.frontierSemantics.pure.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player history) ∈
      (program.frontierSemantics.pure.view).boundedAvailableMoves
          program.frontierSemantics.horizon history player := by
  simpa [PureFrontierStrategy, PureFrontierHistory, frontierSemantics] using
    program.frontierSemantics
      |>.pureStrategy_chooses_available strategy history

/-- A legal behavioral frontier strategy assigns probability only to available
optional moves. -/
theorem behavioralFrontierStrategy_supports_available
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.BehavioralFrontierStrategy player)
    (history : program.BehavioralFrontierHistory)
    {move : Option ((program.frontierSemantics.behavioral.view).Act player)}
    (hmove :
      move ∈
        (strategy.1
          ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
              program.frontierSemantics.horizon player history)).support) :
    move ∈
      (program.frontierSemantics.behavioral.view).boundedAvailableMoves
          program.frontierSemantics.horizon history player := by
  simpa [BehavioralFrontierStrategy, BehavioralFrontierHistory,
    frontierSemantics] using
    program.frontierSemantics
      |>.behavioralStrategy_supports_available strategy history hmove

/-- Pure frontier strategies depend only on the player's information state. -/
theorem pureFrontierStrategy_eq_of_playerView_eq
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.PureFrontierStrategy player)
    {left right : program.PureFrontierHistory}
    (hview : left.playerView player = right.playerView player) :
    strategy.1
        ((program.frontierSemantics.pure.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player left) =
      strategy.1
        ((program.frontierSemantics.pure.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player right) := by
  simpa [PureFrontierStrategy, PureFrontierHistory, frontierSemantics] using
    program.frontierSemantics
      |>.pureStrategy_eq_of_playerView_eq strategy hview

/-- Behavioral frontier strategies depend only on the player's information
state. -/
theorem behavioralFrontierStrategy_eq_of_playerView_eq
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.BehavioralFrontierStrategy player)
    {left right : program.BehavioralFrontierHistory}
    (hview : left.playerView player = right.playerView player) :
    strategy.1
        ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player left) =
      strategy.1
        ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player right) := by
  simpa [BehavioralFrontierStrategy, BehavioralFrontierHistory,
    frontierSemantics] using
    program.frontierSemantics
      |>.behavioralStrategy_eq_of_playerView_eq strategy hview

/-- The option-valued completed pure frontier kernel is the completed run
distribution pushed forward through the source payoff projection. -/
theorem pureFrontierOptionOutcomeKernel_eq_sourceMap
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.frontierSemantics.pure.optionOutcomeKernel profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        ((program.frontierSemantics.pure.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          ((program.frontierSemantics.pure.view).legalPureToBehavioral
            (ToEventGraph.completionBound
              (ToEventGraph.compile program.core)) profile)) := by
  simpa [frontierSemantics, PureFrontierProfile] using
    program.frontierSemantics.pureOptionOutcomeKernel_eq_sourceMap profile

/-- The option-valued completed behavioral frontier kernel is the completed run
distribution pushed forward through the source payoff projection. -/
theorem behavioralFrontierOptionOutcomeKernel_eq_sourceMap
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierSemantics.behavioral.optionOutcomeKernel profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        ((program.frontierSemantics.behavioral.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core)) profile) := by
  simpa [frontierSemantics, BehavioralFrontierProfile] using
    program.frontierSemantics.behavioralOptionOutcomeKernel_eq_sourceMap
      profile

/-- A Nash equilibrium of the induced product mixed pure frontier profile is a
behavioral Nash equilibrium. -/
theorem behavioralFrontier_nash_of_induced_mixedPure_nash
    (program : WFProgram P L) [FiniteDomains program]
    {behavioral : program.BehavioralFrontierProfile}
    (hNash :
      program.mixedPureFrontierGame.IsNash
        (program.behavioralFrontierToMixedPure behavioral)) :
    program.behavioralFrontierGame.IsNash behavioral := by
  simpa [behavioralFrontierToMixedPure, frontierSemantics,
    behavioralFrontierGame, mixedPureFrontierGame,
    BehavioralFrontierProfile, MixedPureFrontierProfile] using
    program.frontierSemantics.behavioralNash_of_inducedMixedPureNash hNash

/-- A deviation-preserving mixed-to-behavioral frontier realization transports
mixed-pure Nash equilibria to behavioral Nash equilibria. -/
theorem behavioralFrontier_nash_of_mixedPure_nash
    (program : WFProgram P L) [FiniteDomains program]
    (simulation :
      program.MixedPureToBehavioralFrontierDeviationSimulation)
    {mixed : program.MixedPureFrontierProfile}
    (hNash : program.MixedPureFrontierNash mixed) :
    program.BehavioralFrontierNash (simulation.realize mixed) := by
  simpa [MixedPureToBehavioralFrontierDeviationSimulation,
    MixedPureFrontierNash, BehavioralFrontierNash, frontierSemantics,
    mixedPureFrontierGame, behavioralFrontierGame,
    MixedPureFrontierProfile, BehavioralFrontierProfile] using
    simulation.behavioralNash_of_mixedPureNash hNash

/-- Bounded mixed Nash existence for the completed pure frontier payoff game. -/
theorem mixedPureFrontier_nash_exists_of_bounded
    (program : WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ mixed : program.MixedPureFrontierProfile,
      program.mixedPureFrontierGame.IsNash mixed := by
  simpa [frontierSemantics, pureFrontierGame, mixedPureFrontierGame,
    MixedPureFrontierProfile] using
    program.frontierSemantics.mixedPureNash_exists_of_bounded hbd

/-- Bounded correlated-equilibrium existence for the completed pure frontier
payoff game. -/
theorem pureFrontier_correlatedEq_exists_of_bounded
    (program : WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ correlated : PMF program.PureFrontierProfile,
      program.pureFrontierGame.IsCorrelatedEq correlated := by
  classical
  letI : Finite P := Finite.of_fintype P
  letI :
      ∀ player,
        Finite (program.pureFrontierGame.Strategy player) :=
    fun player => by
      letI : Fintype (program.pureFrontierGame.Strategy player) :=
        program.pureFrontierStrategyFintype player
      exact Finite.of_fintype _
  letI :
      ∀ player,
        Nonempty (program.pureFrontierGame.Strategy player) :=
    program.pureFrontierStrategyNonempty
  simpa [PureFrontierProfile] using
    program.pureFrontierGame.correlatedEq_exists_of_bounded hbd

/-- Bounded coarse-correlated-equilibrium existence for the completed pure
frontier payoff game. -/
theorem pureFrontier_coarseCorrelatedEq_exists_of_bounded
    (program : WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ correlated : PMF program.PureFrontierProfile,
      program.pureFrontierGame.IsCoarseCorrelatedEq correlated := by
  classical
  letI : Finite P := Finite.of_fintype P
  letI :
      ∀ player,
        Finite (program.pureFrontierGame.Strategy player) :=
    fun player => by
      letI : Fintype (program.pureFrontierGame.Strategy player) :=
        program.pureFrontierStrategyFintype player
      exact Finite.of_fintype _
  letI :
      ∀ player,
        Nonempty (program.pureFrontierGame.Strategy player) :=
    program.pureFrontierStrategyNonempty
  simpa [PureFrontierProfile] using
    program.pureFrontierGame.coarseCorrelatedEq_exists_of_bounded hbd

/-- With bounded compiled payoff utilities, a deviation-preserving
mixed-to-behavioral frontier realization yields behavioral Nash existence. -/
theorem behavioralFrontier_nash_exists_of_bounded
    (program : WFProgram P L) [FiniteDomains program]
    (simulation :
      program.MixedPureToBehavioralFrontierDeviationSimulation)
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ behavioral : program.BehavioralFrontierProfile,
      program.BehavioralFrontierNash behavioral := by
  simpa [MixedPureToBehavioralFrontierDeviationSimulation,
    BehavioralFrontierNash, frontierSemantics, pureFrontierGame,
    behavioralFrontierGame, BehavioralFrontierProfile] using
    simulation.behavioralNash_exists_of_bounded hbd

/-- Correlated-equilibrium existence for the finite terminal-public frontier
game. -/
theorem pureTerminalPublicFrontier_correlatedEq_exists
    (program : WFProgram P L) [FiniteDomains program] :
    ∃ correlated : PMF program.PureTerminalPublicFrontierProfile,
      program.pureTerminalPublicFrontierGame.IsCorrelatedEq correlated := by
  classical
  letI : Finite P := Finite.of_fintype P
  letI :
      ∀ player,
        Finite (program.pureTerminalPublicFrontierGame.Strategy player) :=
    fun player => by
      letI : Fintype (program.pureFrontierGame.Strategy player) :=
        program.frontierSemantics.pureStrategyFintype player
      have hfinite : Finite (program.pureFrontierGame.Strategy player) :=
        Finite.of_fintype _
      simpa [pureTerminalPublicFrontierGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicKernelGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicGameForm,
        pureFrontierGame, frontierSemantics] using hfinite
  letI :
      ∀ player,
        Nonempty (program.pureTerminalPublicFrontierGame.Strategy player) :=
    fun player => by
      simpa [pureTerminalPublicFrontierGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicKernelGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicGameForm,
        pureFrontierGame, frontierSemantics] using
        program.frontierSemantics.pureStrategyNonempty player
  letI :
      ∀ field : Fin (ToEventGraph.compile program.core).graph.fieldCount,
        Fintype
          (L.Val ((ToEventGraph.compile program.core).graph.fieldRow field).ty) :=
    program.frontierSemantics.games.fieldFintype
  letI :
      Fintype
        (EventGraph.PublicObservation
          (ToEventGraph.compile program.core).graph) :=
    inferInstance
  letI :
      Finite program.pureTerminalPublicFrontierGame.Outcome := by
    change Finite
      (EventGraph.PublicObservation (ToEventGraph.compile program.core).graph)
    exact Finite.of_fintype _
  simpa [PureTerminalPublicFrontierProfile] using
    program.pureTerminalPublicFrontierGame.correlatedEq_exists

/-- Coarse-correlated-equilibrium existence for the finite terminal-public
frontier game. -/
theorem pureTerminalPublicFrontier_coarseCorrelatedEq_exists
    (program : WFProgram P L) [FiniteDomains program] :
    ∃ correlated : PMF program.PureTerminalPublicFrontierProfile,
      program.pureTerminalPublicFrontierGame.IsCoarseCorrelatedEq
        correlated := by
  classical
  letI : Finite P := Finite.of_fintype P
  letI :
      ∀ player,
        Finite (program.pureTerminalPublicFrontierGame.Strategy player) :=
    fun player => by
      letI : Fintype (program.pureFrontierGame.Strategy player) :=
        program.frontierSemantics.pureStrategyFintype player
      have hfinite : Finite (program.pureFrontierGame.Strategy player) :=
        Finite.of_fintype _
      simpa [pureTerminalPublicFrontierGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicKernelGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicGameForm,
        pureFrontierGame, frontierSemantics] using hfinite
  letI :
      ∀ player,
        Nonempty (program.pureTerminalPublicFrontierGame.Strategy player) :=
    fun player => by
      simpa [pureTerminalPublicFrontierGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicKernelGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicGameForm,
        pureFrontierGame, frontierSemantics] using
        program.frontierSemantics.pureStrategyNonempty player
  letI :
      ∀ field : Fin (ToEventGraph.compile program.core).graph.fieldCount,
        Fintype
          (L.Val ((ToEventGraph.compile program.core).graph.fieldRow field).ty) :=
    program.frontierSemantics.games.fieldFintype
  letI :
      Fintype
        (EventGraph.PublicObservation
          (ToEventGraph.compile program.core).graph) :=
    inferInstance
  letI :
      Finite program.pureTerminalPublicFrontierGame.Outcome := by
    change Finite
      (EventGraph.PublicObservation (ToEventGraph.compile program.core).graph)
    exact Finite.of_fintype _
  simpa [PureTerminalPublicFrontierProfile] using
    program.pureTerminalPublicFrontierGame.coarseCorrelatedEq_exists

/-- Mixed Nash existence for the finite terminal-public frontier game. -/
theorem mixedPureTerminalPublicFrontier_nash_exists
    (program : WFProgram P L) [FiniteDomains program] :
    ∃ mixed : program.MixedPureTerminalPublicFrontierProfile,
      program.MixedPureTerminalPublicFrontierNash mixed := by
  simpa [frontierSemantics, mixedPureTerminalPublicFrontierGame,
    MixedPureTerminalPublicFrontierProfile,
    MixedPureTerminalPublicFrontierNash] using
    program.frontierSemantics.terminalPublicMixedNash_exists


end WFProgram

end Vegas
