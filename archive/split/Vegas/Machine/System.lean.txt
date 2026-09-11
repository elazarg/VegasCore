/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Math.Probability.FinDist

/-!
# Operational systems

An operational system is one stage of gradual runtime lowering.  Commands are
indexed by their source state, so validation evidence is part of the semantic
transition surface and invalid external requests need no invented behavior.

This structure intentionally contains no game-theoretic claim.  A pass may add
administrative events, scheduling state, encodings, or transaction boundaries;
separate certificates say which observations, trace properties, or strategic
properties survive that pass.
-/

noncomputable section

namespace Vegas.Machine

open GameTheory.Math.Probability

/-- One operational lowering stage. -/
structure System where
  State : Type
  Command : State → Type
  init : State
  step : (state : State) → Command state → FinDist State
  terminal : State → Prop

namespace System

variable (system : System)

/-- A public/private observation surface attached to an operational system. -/
structure Observation (Player : Type) where
  Public : Type
  Private : Player → Type
  publicView : system.State → Public
  privateView : (who : Player) → system.State → Private who

end System

end Vegas.Machine
