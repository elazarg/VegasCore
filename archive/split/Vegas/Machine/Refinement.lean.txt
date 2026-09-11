/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.System

/-!
# Gradual operational refinement

`Refinement abstract concrete` is a single small lowering step.  Concrete
state projects to abstract state.  A concrete command either decodes to one
abstract command or is administrative noise.  The exact step law says that
projection turns administrative commands into stuttering and all other
commands into the decoded abstract transition.

This is a functional stochastic simulation, not by itself a secure-compilation
or game-preservation theorem.  In particular it says nothing about extra
observations, target-only strategies, adversarial scheduling, timing, or
liveness.  Those obligations must be attached to the pass that introduces the
corresponding implementation detail.
-/

noncomputable section

namespace Vegas.Machine

open GameTheory.Math.Probability

/-- A stuttering projection from a more concrete system to an abstract one. -/
structure Refinement
    (abstract : System)
    (concrete : System) where
  projectState : concrete.State → abstract.State
  decodeCommand :
    (state : concrete.State) → concrete.Command state →
      Option (abstract.Command (projectState state))
  init_eq : projectState concrete.init = abstract.init
  step_eq :
    ∀ state command,
      (concrete.step state command).map projectState =
        match decodeCommand state command with
        | none => FinDist.pure (projectState state)
        | some decoded => abstract.step (projectState state) decoded

namespace Refinement

variable {abstract : System}
variable {concrete : System}

/-- A command is administrative when it changes only concrete state. -/
def Administrative (refinement : Refinement abstract concrete)
    (state : concrete.State) (command : concrete.Command state) : Prop :=
  refinement.decodeCommand state command = none

/-- Administrative commands stutter after state projection. -/
theorem step_eq_pure_of_administrative
    (refinement : Refinement abstract concrete)
    (state : concrete.State) (command : concrete.Command state)
    (administrative : refinement.Administrative state command) :
    (concrete.step state command).map refinement.projectState =
      FinDist.pure (refinement.projectState state) := by
  rw [refinement.step_eq, administrative]

/-- The identity lowering. -/
def refl (system : System) : Refinement system system where
  projectState := id
  decodeCommand := fun _ command => some command
  init_eq := rfl
  step_eq := by
    intro state command
    simp

/-- Compose adjacent lowering stages.  Administrative commands at either stage
remain administrative in the composite projection. -/
def trans
    {middle : System}
    (first : Refinement abstract middle)
    (second : Refinement middle concrete) :
    Refinement abstract concrete where
  projectState := fun state => first.projectState (second.projectState state)
  decodeCommand := fun state command =>
    match second.decodeCommand state command with
    | none => none
    | some middleCommand =>
        first.decodeCommand (second.projectState state) middleCommand
  init_eq := by
    rw [second.init_eq, first.init_eq]
  step_eq := by
    intro state command
    change
      FinDist.map (first.projectState ∘ second.projectState)
          (concrete.step state command) = _
    rw [← FinDist.map_comp, second.step_eq]
    cases hmiddle : second.decodeCommand state command with
    | none =>
        simp
    | some middleCommand =>
        have hstep :=
          first.step_eq (second.projectState state) middleCommand
        cases habstract :
            first.decodeCommand (second.projectState state) middleCommand with
        | none =>
            rw [habstract] at hstep
            simpa [habstract] using hstep
        | some abstractCommand =>
            rw [habstract] at hstep
            simpa [habstract] using hstep

/-- A lowering may additionally preserve terminality exactly.  This is kept
separate because transaction finalization or payout stages often add concrete
work after the abstract game has terminated. -/
structure PreservesTerminal
    (refinement : Refinement abstract concrete) : Prop where
  terminal_iff :
    ∀ state, concrete.terminal state ↔
      abstract.terminal (refinement.projectState state)

end Refinement

end Vegas.Machine
