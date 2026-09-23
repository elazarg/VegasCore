/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.FinDist

/-! # Realizing private strategy memory through behavioral policies

A strategy may retain private memory and correlate responses across activations.
Its memory is internal to the strategy, not an action in the game history.
Conditioning on the player's own input/output transcript produces one behavioral
policy with the same external transcript law against every adaptive environment.

The environment evolves from its state and the emitted output, independently
of private memory conditional on that output. Inputs are observations of the
environment state. No game-theoretic equilibrium correspondence is asserted.
-/

noncomputable section

namespace GameTheory.Protocol.PrivateStrategy

open GameTheory.Math.Probability

universe um ui uo ue

structure Strategy (Memory : Type um) (Input : Type ui) (Output : Type uo) where
  initial : FinDist Memory
  respond : Memory → Input → FinDist (Output × Memory)

variable {Memory : Type um} {Input : Type ui} {Output : Type uo}

/-- Most recent input/output pair first. Only this player's observations and
outputs enter the transcript; it contains no hidden environment state. -/
abbrev Transcript (Input : Type ui) (Output : Type uo) := List (Input × Output)

def posterior (strategy : Strategy Memory Input Output) :
    Transcript Input Output → FinDist Memory
  | [] => strategy.initial
  | (input, output) :: past =>
      (((posterior strategy past).bind (fun memory => strategy.respond memory input)).condOnFibre
        Prod.fst output).map Prod.snd

/-- This policy is independent of the environment and of utilities. -/
def behavioral (strategy : Strategy Memory Input Output)
    (past : Transcript Input Output) (input : Input) : FinDist Output :=
  ((posterior strategy past).bind (fun memory => strategy.respond memory input)).map Prod.fst

variable {Environment : Type ue}

/-- The private implementation; memory is omitted from the external result. -/
def runPrivate (strategy : Strategy Memory Input Output) (observe : Environment → Input)
    (advance : Environment → Output → FinDist Environment) :
    Nat → Transcript Input Output → Environment → Memory →
      FinDist (Environment × Transcript Input Output)
  | 0, past, state, _ => FinDist.pure (state, past)
  | count + 1, past, state, memory =>
      (strategy.respond memory (observe state)).bind fun response =>
        (advance state response.1).bind fun next =>
          runPrivate strategy observe advance count ((observe state, response.1) :: past)
            next response.2

/-- The corresponding information-local behavioral policy. -/
def runBehavioral (policy : Transcript Input Output → Input → FinDist Output)
    (observe : Environment → Input) (advance : Environment → Output → FinDist Environment) :
    Nat → Transcript Input Output → Environment → FinDist (Environment × Transcript Input Output)
  | 0, past, state => FinDist.pure (state, past)
  | count + 1, past, state =>
      (policy past (observe state)).bind fun output =>
        (advance state output).bind fun next =>
          runBehavioral policy observe advance count ((observe state, output) :: past) next

/-- A single behavioral realization works against every adaptive environment.
The whole external final state and interaction transcript agree, not just payoffs. -/
theorem realize (strategy : Strategy Memory Input Output) (observe : Environment → Input)
    (advance : Environment → Output → FinDist Environment) (count : Nat)
    (past : Transcript Input Output) (state : Environment) :
    (posterior strategy past).bind (runPrivate strategy observe advance count past state) =
      runBehavioral (behavioral strategy) observe advance count past state := by
  induction count generalizing past state with
  | zero => simp [runPrivate, runBehavioral]
  | succ count ih =>
      let law := (posterior strategy past).bind fun memory =>
        strategy.respond memory (observe state)
      calc
        _ = law.bind (fun response => (advance state response.1).bind fun next =>
            runPrivate strategy observe advance count ((observe state, response.1) :: past)
              next response.2) := by simp only [law, runPrivate, FinDist.bind_bind]
        _ = (behavioral strategy past (observe state)).bind fun output =>
            (posterior strategy ((observe state, output) :: past)).bind fun memory =>
              (advance state output).bind fun next =>
                runPrivate strategy observe advance count ((observe state, output) :: past)
                  next memory := by
            conv_lhs => arg 1; rw [FinDist.eq_bind_fst_conditional_snd law]
            simp only [FinDist.bind_bind, FinDist.bind_map, behavioral, posterior, law]
        _ = (behavioral strategy past (observe state)).bind fun output =>
            (advance state output).bind fun next =>
              (posterior strategy ((observe state, output) :: past)).bind
                (runPrivate strategy observe advance count ((observe state, output) :: past)
                  next) := by
            apply FinDist.bind_congr
            intro output _
            exact FinDist.bind_comm ..
        _ = _ := by
            simp only [ih, runBehavioral]

end GameTheory.Protocol.PrivateStrategy
