/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Refinement

/-!
# Semantic-step instrumentation

This lowering attaches metadata that is updated atomically with every semantic
step.  It is the target-neutral shape needed for completion flags, sequence
numbers, receipts, or an execution-order log.  Projection forgets the metadata
and preserves the exact abstract stochastic transition.

Unlike `AdministrativeLayer`, this pass adds no target-only commands: every
concrete command decodes to one abstract command.  The metadata update may
inspect the prior state, command, and realized successor.  Exposing that
metadata remains a separate observation decision.
-/

noncomputable section

namespace Vegas.Machine

open GameTheory.Math.Probability

/-- Metadata updated as part of each realized semantic transition. -/
structure Instrumentation (abstract : System) where
  Metadata : Type
  initial : Metadata
  record :
    (state : abstract.State) → Metadata →
      abstract.Command state → abstract.State → Metadata

namespace Instrumentation

variable {abstract : System}

/-- Attach the instrumentation state to the abstract system. -/
def lower (instrumentation : Instrumentation abstract) : System where
  State := abstract.State × instrumentation.Metadata
  Command := fun state => abstract.Command state.1
  init := (abstract.init, instrumentation.initial)
  step := fun state command =>
    (abstract.step state.1 command).map fun next =>
      (next, instrumentation.record state.1 state.2 command next)
  terminal := fun state => abstract.terminal state.1

/-- Forgetting instrumentation is an exact, non-stuttering refinement. -/
def refinement (instrumentation : Instrumentation abstract) :
    Refinement abstract instrumentation.lower where
  projectState := Prod.fst
  decodeCommand := fun _ command => some command
  init_eq := rfl
  step_eq := by
    intro state command
    simp only [lower, FinDist.map_comp]
    change FinDist.map id (abstract.step state.1 command) = _
    exact FinDist.map_id _

/-- Instrumentation does not change semantic terminality. -/
theorem preservesTerminal (instrumentation : Instrumentation abstract) :
    instrumentation.refinement.PreservesTerminal where
  terminal_iff := by
    intro state
    rfl

/-- Hide the instrumentation metadata from an existing abstract observation.
This construction is not a theorem that a concrete runtime actually hides it. -/
def liftObservation
    {Player : Type}
    (instrumentation : Instrumentation abstract)
    (observation : abstract.Observation Player) :
    instrumentation.lower.Observation Player where
  Public := observation.Public
  Private := observation.Private
  publicView := fun state => observation.publicView state.1
  privateView := fun who state => observation.privateView who state.1

@[simp] theorem liftObservation_publicView
    {Player : Type}
    (instrumentation : Instrumentation abstract)
    (observation : abstract.Observation Player)
    (state : instrumentation.lower.State) :
    (instrumentation.liftObservation observation).publicView state =
      observation.publicView
        (instrumentation.refinement.projectState state) := rfl

@[simp] theorem liftObservation_privateView
    {Player : Type}
    (instrumentation : Instrumentation abstract)
    (observation : abstract.Observation Player)
    (who : Player)
    (state : instrumentation.lower.State) :
    (instrumentation.liftObservation observation).privateView who state =
      observation.privateView who
        (instrumentation.refinement.projectState state) := rfl

/-- One full semantic transition recorded by an instrumentation layer. -/
structure StepRecord (abstract : System) where
  prior : abstract.State
  command : abstract.Command prior
  next : abstract.State

/-- Record the realized semantic steps in reverse chronological order.  This is
a proof-facing reference pass; a concrete backend normally lowers records to
stable action ids, completion bits, or receipts rather than storing dependent
Lean values. -/
def executionLog (abstract : System) : Instrumentation abstract where
  Metadata := List (StepRecord abstract)
  initial := []
  record := fun prior records command next =>
    { prior := prior, command := command, next := next } :: records

@[simp] theorem executionLog_init_metadata (abstract : System) :
    (executionLog abstract).lower.init.2 = [] := rfl

theorem executionLog_step
    (abstract : System)
    (state : abstract.State)
    (records : List (StepRecord abstract))
    (command : abstract.Command state) :
    (executionLog abstract).lower.step (state, records) command =
      (abstract.step state command).map fun next =>
        (next,
          ({ prior := state, command := command, next := next } :
            StepRecord abstract) :: records) := rfl

end Instrumentation

end Vegas.Machine
