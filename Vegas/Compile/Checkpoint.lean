/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler
import Vegas.EventGraph.Batch

/-!
# Checked programs as checkpoint models

Compilation produces the event graph and payoff projection. A strategic game
presentation also needs a checkpoint policy: which reachable checkpoints are
allowed as one strategic observation step.

Primitive downset checkpoints are available as an operational presentation:
checked source guard legality compiles to graph guard liveness, and graph guard
liveness gives downset progress.  They are not the default strategic frontier
semantics; custom checkpoint policies and frontier round semantics are attached
explicitly with their own progress proofs.
-/

namespace Vegas

namespace ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A compiled checked program together with a checkpoint-level presentation.

This is not yet a strategic game form: it has no action carrier or transition
kernel. It is the checkpoint observation model used by later strategic
presentations. Histories expose checkpoint observations, not primitive event
linearizations. -/
structure CheckpointModel (P : Type) [DecidableEq P] (L : IExpr) where
  compiled : CompiledProgram P L
  presentation : EventGraph.CheckpointPresentation compiled.graph

namespace CheckpointModel

variable (model : CheckpointModel P L)

/-- Reachable checkpoint states of a compiled checkpoint model. -/
abbrev State : Type :=
  EventGraph.ReachableConfig model.compiled.graph

/-- Checkpoint histories for the game's presentation policy. -/
abbrev History (src dst : model.State) : Type :=
  model.presentation.History src dst

/-- Initial reachable checkpoint. -/
def init : model.State :=
  ⟨EventGraph.Config.initial model.compiled.graph, EventGraph.Reachable.initial⟩

/-- Terminal checkpoint predicate. -/
def terminal (state : model.State) : Prop :=
  EventGraph.Terminal model.compiled.graph state.1

/-- Common public checkpoint observation. -/
noncomputable def publicView (state : model.State) :
    EventGraph.PublicObservation model.compiled.graph :=
  EventGraph.publicObserve model.compiled.graph state.1

/-- Player checkpoint observation. -/
noncomputable def observe (who : P) (state : model.State) :
    EventGraph.Observation model.compiled.graph who :=
  EventGraph.observe model.compiled.graph state.1 who

/-- Allowed checkpoint successors according to the presentation policy. -/
def allowed (src dst : model.State) : Prop :=
  model.presentation.policy.allowed src dst

/-- Allowed checkpoint successors are backed by some primitive event batch. -/
theorem allowed_realizable {src dst : model.State}
    (hallowed : model.allowed src dst) :
    EventGraph.CheckpointStep model.compiled.graph src dst :=
  model.presentation.policy.realizable hallowed

/-- Allowed checkpoint successors strictly advance the completed-node downset. -/
theorem allowed_advances {src dst : model.State}
    (hallowed : model.allowed src dst) :
    src.1.done ⊂ dst.1.done :=
  model.presentation.policy.advances hallowed

/-- Nonterminal checkpoints have at least one allowed checkpoint successor. -/
theorem nonterminal_exists_allowed {state : model.State}
    (hterminal : ¬ model.terminal state) :
    ∃ dst, model.allowed state dst :=
  model.presentation.nonterminal_exists_allowed hterminal

end CheckpointModel

/-- Compile a checked program and attach an explicit checkpoint presentation.

The presentation argument is where the game designer/theorem layer commits to
maximal frontiers, an explicit scheduler, downset transitions, or another
checkpoint policy. -/
noncomputable def checkpointModel
    (program : WFProgram P L)
    (presentation :
      EventGraph.CheckpointPresentation
        (ToEventGraph.compile program.core).graph) :
    CheckpointModel P L where
  compiled := ToEventGraph.compile program.core
  presentation := presentation

/-- Compile a checked program using the primitive downset checkpoint policy
from an explicit graph-level progress theorem.

This is the generic construction point for externally proved or
backend-specific progress facts. -/
noncomputable def primitiveDownsetCheckpointModelOfProgress
    (program : WFProgram P L)
    (progress :
      EventGraph.DownsetProgress
        (ToEventGraph.compile program.core).graph) :
    CheckpointModel P L :=
  checkpointModel program
    (EventGraph.primitiveDownsetCheckpointPresentation
      (ToEventGraph.compile program.core).graph progress)

/-- Compile a checked program using the primitive downset checkpoint policy
from the graph-level guard-liveness obligation.

The remaining proof obligation is the graph-level nondeadlock condition:
every compiled commit guard admits some legal action for every declared choice
environment. Graph well-formedness and internal event availability are carried
by compilation and event-graph execution. -/
noncomputable def primitiveDownsetCheckpointModelOfGuardLive
    (program : WFProgram P L)
    (guards :
      EventGraph.GuardLive
        (ToEventGraph.compile program.core).graph) :
    CheckpointModel P L :=
  primitiveDownsetCheckpointModelOfProgress program
    (EventGraph.primitiveDownsetProgress_of_availableEventProgress
      (EventGraph.availableEventProgress_of_guardLive
        (ToEventGraph.compile program.core).graphWF guards))

/-- Compile a checked program using the primitive downset checkpoint policy.

Source guard legality is compiled to graph guard liveness, and graph
well-formedness plus guard liveness gives nonterminal checkpoint progress. -/
noncomputable def primitiveDownsetCheckpointModel
    (program : WFProgram P L) :
    CheckpointModel P L :=
  primitiveDownsetCheckpointModelOfGuardLive program
    (ToEventGraph.compile_guardLive program)

end ToEventGraph

end Vegas
