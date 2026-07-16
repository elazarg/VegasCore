/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Strategic
import Vegas.Frontier.Games

/-!
# Raw source/frontier strategic surfaces

This file names the two strategic surfaces used by the source/frontier bridge:
the source-local strategic game and the completed behavioral frontier game
observed through source payoff outcomes.
-/

namespace Vegas

open GameTheory

namespace WFProgram

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Initial source configuration of a checked program. -/
def sourceInitialConfig (program : WFProgram P L) : SourceConfig P L :=
  ToEventGraph.sourceStart program.core

/-- Source-native strategic game for a checked program, using the program's
own normalization proof. -/
noncomputable def sourceStrategicGame
    (program : WFProgram P L) (horizon : Nat) (cutoff : Payoff P) :
    KernelGame P :=
  sourceTraceKernelGame
    (ToEventGraph.sourceStart program.core)
    program.core.normalized horizon cutoff

@[simp] theorem sourceStrategicGame_outcomeKernel
    (program : WFProgram P L) (horizon : Nat) (cutoff : Payoff P)
    (profile : (program.sourceStrategicGame horizon cutoff).Profile) :
    (program.sourceStrategicGame horizon cutoff).outcomeKernel profile =
      SourceStrategicHistory.traceDist
        (ToEventGraph.sourceStart program.core)
        program.core.normalized profile horizon := rfl

/-- Observe a raw source strategic history by the payoff outcome currently
reported by its source configuration.  Nonterminal finite-horizon truncations
are observed as `none`. -/
def sourceStrategicOptionOutcomeView
    (program : WFProgram P L) (horizon : Nat) (cutoff : Payoff P) :
    KernelGame.ViewFamily
      (program.sourceStrategicGame horizon cutoff) P
      (fun _ => Option (Outcome P)) where
  observe := fun _ state => state.history.current.outcome?

variable [Fintype P]

/-- Observe a completed behavioral frontier outcome through `some`, matching
the optional source observation surface. -/
def behavioralFrontierOptionOutcomeView
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.ViewFamily
      program.behavioralFrontierGame P (fun _ => Option (Outcome P)) where
  observe := fun _ => some

end WFProgram

end Vegas
