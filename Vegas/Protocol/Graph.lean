/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Protocol.Code

/-! # Event graph to typed logical protocol lowering

Lowering is total on graph syntax: chance, guarded commit, and every reveal
source are retained. Graph well-formedness, when available, proves that reveal
sources resolve to same-typed sealed initial or event fields; lowering itself
does not disable a constructor or turn a raw candidate into a legal value.
-/

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Erase an initial value while retaining its type and visibility owner. -/
def InitialField.publicMetadata (field : InitialField Player L) :
    Protocol.InitialField Player L :=
  ⟨field.ty, field.owner⟩

/-- Retain every event-node semantic constructor as a typed protocol
operation. -/
def EventNode.protocolOperation (node : EventNode Player L) :
    Protocol.Operation Player L :=
  match node.sem with
  | .sample dist => .chance dist
  | .commit owner guard => .commit owner guard
  | .reveal source => .reveal ⟨source, node.ty⟩

/-- Public logical code generated from a graph. Initial values are erased. -/
def Graph.protocolCode (G : Graph Player L) : Protocol.Code Player L where
  initial := G.initialFields.map InitialField.publicMetadata
  operations := G.nodes.map EventNode.protocolOperation

@[simp] theorem Graph.protocolCode_initial_length (G : Graph Player L) :
    G.protocolCode.initial.length = G.initialFields.length := by
  simp [Graph.protocolCode]

@[simp] theorem Graph.protocolCode_operations_length (G : Graph Player L) :
    G.protocolCode.operations.length = G.nodeCount := by
  simp [Graph.protocolCode, Graph.nodeCount]

@[simp] theorem Graph.protocolCode_operation (G : Graph Player L)
    (node : Fin G.nodeCount) :
    G.protocolCode.operations.get
        ⟨node, by simp⟩ =
      (G.nodeRow node).protocolOperation := by
  simp [Graph.protocolCode, Graph.nodeRow, Graph.nodeCount]

/-- Proof-facing ideal setup corresponding to the graph's initial values. It is
not a field of `protocolCode` and must not be serialized with public code. -/
def Graph.protocolInitialInput (G : Graph Player L) :
    G.protocolCode.InitialInput := fun slot =>
  cast (by simp [Graph.protocolCode, InitialField.publicMetadata])
    (G.initialFields.get ⟨slot, by
      rw [← G.protocolCode_initial_length]
      exact slot.isLt⟩).value

@[simp] theorem Graph.protocolCode_chance (G : Graph Player L)
    (node : Fin G.nodeCount) (dist : EventDist L)
    (hsem : (G.nodeRow node).sem = .sample dist) :
    G.protocolCode.operations.get ⟨node, by simp⟩ =
      .chance dist := by
  rw [G.protocolCode_operation]
  simp [EventNode.protocolOperation, hsem]

@[simp] theorem Graph.protocolCode_commit (G : Graph Player L)
    (node : Fin G.nodeCount) (owner : Player) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit owner guard) :
    G.protocolCode.operations.get ⟨node, by simp⟩ =
      .commit owner guard := by
  rw [G.protocolCode_operation]
  simp [EventNode.protocolOperation, hsem]

@[simp] theorem Graph.protocolCode_reveal (G : Graph Player L)
    (node : Fin G.nodeCount) (source : Nat)
    (hsem : (G.nodeRow node).sem = .reveal source) :
    G.protocolCode.operations.get ⟨node, by simp⟩ =
      .reveal ⟨source, (G.nodeRow node).ty⟩ := by
  rw [G.protocolCode_operation]
  simp [EventNode.protocolOperation, hsem]

end Vegas.EventGraph
