/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceBridge
import Vegas.Core.Trace

/-!
# Source-to-graph bridge: the value dimension

The structural bridge (`Vegas.Compile.SourceBridge`) ties the compiled graph's
*shape* — node count, owners, readable order — to the source program. This file
begins the *value* dimension: a source run carries, in its labels, the value
drawn, chosen, or disclosed at each step, and these are the values the graph
nodes receive.

`Label.toTypedValue` packs a label's value as a graph `TypedValue`.
`LabeledStar.length_eq_instrCount_of_terminal` shows a terminal run takes exactly
`instrCount` steps, so — with `compile_graph_nodeCount` — a terminal run from the
initial configuration produces exactly one value per graph node, the raw material
for the per-node value assignment `w` the graph completion consumes.

The deeper claim that completing the graph with these values reproduces the
source's terminal environment (and that the assignment is node-typed, discharging
`StoreCoherent`) is the next milestone; this file lays the counting groundwork.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The value a labelled step produced, packed as a graph `TypedValue`. -/
def Label.toTypedValue : Label P L → EventGraph.TypedValue L
  | .sample _ v => ⟨_, v⟩
  | .commit _ _ v => ⟨_, v⟩
  | .reveal _ _ _ v => ⟨_, v⟩

/-- A labelled step consumes exactly one instruction: the continuation has one
fewer. -/
theorem LStep.instrCount_cont {cfg b : SourceConfig P L} {ℓ : Label P L}
    (h : LStep cfg ℓ b) :
    cfg.cont.instrCount = b.cont.instrCount + 1 := by
  cases h <;> rfl

namespace SourceConfig

/-- A run that reaches a terminal configuration takes exactly as many steps as
the program has instructions. -/
theorem LabeledStar.length_eq_instrCount_of_terminal
    {cfg final : SourceConfig P L} {labels : List (Label P L)}
    (h : SourceConfig.LabeledStar cfg labels final) :
    final.IsTerminal → labels.length = cfg.cont.instrCount := by
  induction h with
  | refl c =>
      intro hterm
      obtain ⟨p, hp⟩ := hterm
      simp [hp, VegasCore.instrCount]
  | cons step _rest ih =>
      intro hterm
      rw [List.length_cons, ih hterm, ← step.instrCount_cont]

/-- A terminal run from the initial configuration produces exactly one label —
hence one value — per source instruction (and per compiled graph node). -/
theorem labeledStar_initial_length {prog : VegasCore P L []}
    {labels : List (Label P L)} {final : SourceConfig P L}
    (h : SourceConfig.LabeledStar (SourceConfig.initial prog) labels final)
    (hterm : final.IsTerminal) :
    labels.length = prog.instrCount := by
  simpa [SourceConfig.initial] using
    h.length_eq_instrCount_of_terminal hterm

end SourceConfig

end Vegas
