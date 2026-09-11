/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Refinement

/-!
# Administrative lowering

This is the smallest concrete lowering pass: attach a private machine metadata
state and permit stochastic administrative commands that cannot change the
projected semantic state.  Semantic commands retain their exact abstract law.

The construction supplies the step-projection and terminality certificates
automatically.  It deliberately does not claim that metadata is unobservable,
that administrative commands are fairly scheduled, or that their randomness
is independent of a larger execution context.  A concrete use of the layer
must state and prove those properties on its observation and control surfaces.
-/

noncomputable section

namespace Vegas.Machine

open GameTheory.Math.Probability

/-- An operational concern whose commands update only newly attached metadata.

Examples include audit counters, scheduler bookkeeping, transaction receipts,
or random padding.  The command type may depend on the current metadata, and
its update is an exact finite probability law. -/
structure AdministrativeLayer (abstract : System) where
  Metadata : Type
  initial : Metadata
  Command : Metadata → Type
  step : (metadata : Metadata) → Command metadata → FinDist Metadata

namespace AdministrativeLayer

variable {abstract : System}

/-- Commands of the lowered system distinguish semantic work from newly added
administrative work. -/
inductive LoweredCommand (layer : AdministrativeLayer abstract) :
    (abstract.State × layer.Metadata) → Type
  | semantic {state} (command : abstract.Command state.1) :
      LoweredCommand layer state
  | administrative {state} (command : layer.Command state.2) :
      LoweredCommand layer state

/-- Attach the administrative metadata and command surface to a system. -/
def lower (layer : AdministrativeLayer abstract) : System where
  State := abstract.State × layer.Metadata
  Command := layer.LoweredCommand
  init := (abstract.init, layer.initial)
  step := fun state command =>
    match command with
    | .semantic command =>
        (abstract.step state.1 command).map fun next => (next, state.2)
    | .administrative command =>
        (layer.step state.2 command).map fun next => (state.1, next)
  terminal := fun state => abstract.terminal state.1

/-- Forgetting metadata is an exact stochastic stuttering refinement. -/
def refinement (layer : AdministrativeLayer abstract) :
    Refinement abstract layer.lower where
  projectState := Prod.fst
  decodeCommand := fun _ command =>
    match command with
    | .semantic command => some command
    | .administrative _ => none
  init_eq := rfl
  step_eq := by
    intro state command
    cases command with
    | semantic command =>
        simp only [lower, FinDist.map_comp]
        change FinDist.map id (abstract.step state.1 command) = _
        exact FinDist.map_id _
    | administrative command =>
        simp [lower, FinDist.map_comp, Function.comp_def,
          FinDist.map_const]

/-- Administrative metadata does not delay or accelerate semantic
terminality. -/
theorem preservesTerminal (layer : AdministrativeLayer abstract) :
    layer.refinement.PreservesTerminal where
  terminal_iff := by
    intro state
    rfl

/-- An abstract observation can be lifted by ignoring the administrative
metadata.  This is the appropriate observation surface only when the metadata
really is hidden from the represented players. -/
def liftObservation
    {Player : Type}
    (layer : AdministrativeLayer abstract)
    (observation : abstract.Observation Player) :
    layer.lower.Observation Player where
  Public := observation.Public
  Private := observation.Private
  publicView := fun state => observation.publicView state.1
  privateView := fun who state => observation.privateView who state.1

@[simp] theorem liftObservation_publicView
    {Player : Type}
    (layer : AdministrativeLayer abstract)
    (observation : abstract.Observation Player)
    (state : layer.lower.State) :
    (layer.liftObservation observation).publicView state =
      observation.publicView (layer.refinement.projectState state) := rfl

@[simp] theorem liftObservation_privateView
    {Player : Type}
    (layer : AdministrativeLayer abstract)
    (observation : abstract.Observation Player)
    (who : Player)
    (state : layer.lower.State) :
    (layer.liftObservation observation).privateView who state =
      observation.privateView who (layer.refinement.projectState state) := rfl

end AdministrativeLayer

end Vegas.Machine
