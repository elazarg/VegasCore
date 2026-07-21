/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.RoundView
import Vegas.EventGraph.FiniteState

/-!
# Checked programs as finite primitive machines

Compilation already produces the canonical event graph and payoff projection.
This module records that the primitive operational machine has a finite state
carrier for finite-domain checked programs. The machine itself is the canonical
reachable-configuration machine from `EventGraph.ToMachine`; `StateSnapshot`
is used only to prove finiteness.
-/

namespace Vegas

namespace ToEventGraph

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- State carrier of the primitive machine for a compiled checked program. -/
abbrev FinitePrimitiveState (program : WFProgram P L) : Type :=
  (PrimitiveMachine (compile program.core)).State

/-- Finite-state primitive operational machine for a compiled checked program.

This is the operational machine, not the strategic frontier game. Its events
are primitive graph events, while the frontier game layer quotients primitive
event order into checkpoint observations. -/
noncomputable def finitePrimitiveMachine
    (program : WFProgram P L) : Machine P :=
  PrimitiveMachine (compile program.core)

end ToEventGraph

namespace WFProgram

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Program-facing finite primitive operational machine. -/
noncomputable def finitePrimitiveMachine
    (program : WFProgram P L) : Machine P :=
  ToEventGraph.finitePrimitiveMachine program

omit [Fintype P] in
/-- The state carrier of the finite primitive machine is the finite graph
snapshot carrier. -/
theorem finitePrimitiveMachine_state_eq
    (program : WFProgram P L) :
    program.finitePrimitiveMachine.State =
      ToEventGraph.FinitePrimitiveState program := rfl

/-- Checked finite-domain programs have a finite primitive operational state
space. Reachability keeps the machine state semantic; finite graph snapshots
provide the injection used for the `Fintype` instance. -/
@[reducible] noncomputable def finitePrimitiveMachine_stateFintype
    (program : WFProgram P L) [FiniteDomains program] :
    Fintype program.finitePrimitiveMachine.State := by
  change Fintype
    (EventGraph.ReachableConfig (ToEventGraph.compile program.core).graph)
  letI :
      ∀ field : Fin (ToEventGraph.compile program.core).graph.fieldCount,
        Fintype
          (L.Val (((ToEventGraph.compile program.core).graph).fieldRow field).ty) :=
    ToEventGraph.compile_fieldFintype program
  exact
    EventGraph.StateSnapshot.reachableConfigFintype
      (ToEventGraph.compile program.core).graph
      (ToEventGraph.compile program.core).graphWF

omit [Fintype P] in
/-- Initial finite primitive state of a checked program. -/
@[simp] theorem finitePrimitiveMachine_init
    (program : WFProgram P L) :
    program.finitePrimitiveMachine.init =
      ⟨EventGraph.Config.initial (ToEventGraph.compile program.core).graph,
        EventGraph.Reachable.initial⟩ := rfl

omit [Fintype P] in
/-- Terminal finite primitive states are exactly terminal graph snapshots. -/
@[simp] theorem finitePrimitiveMachine_terminal
    (program : WFProgram P L)
    (state : program.finitePrimitiveMachine.State) :
    program.finitePrimitiveMachine.terminal state =
      EventGraph.Terminal
        (ToEventGraph.compile program.core).graph state.1 := rfl

end WFProgram

end Vegas
