/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedRules

/-! # Resolution admission for compiled sealed-message programs

Compiled sealed fragments contain only executable commit and reveal rules, and
every rule prerequisite points to a strictly earlier rule. These are the two
program-level facts required by source-ordered resolution runtimes.
-/

namespace Vegas.EventGraph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}

namespace SealedFragment

/-- Every rule emitted for an admitted sealed fragment is executable. -/
theorem compile_rule_kind_ne_disabled (supported : SealedFragment G ty)
    {index : Nat} {rule : SealedRule Player}
    (hrule : supported.compile.rules[index]? = some rule) :
    rule.kind ≠ .disabled := by
  rcases supported.ruleAt_exists_node hrule with ⟨node, _hindex, rfl⟩
  cases hsem : (G.nodeRow node).sem with
  | sample dist => exact (supported.noSamples node dist hsem).elim
  | commit owner guard =>
      rw [G.sealedRule_commit node owner guard hsem]
      simp
  | reveal source =>
      rcases supported.revealSource node source hsem with
        ⟨producer, owner, guard, hsource, hproducer⟩
      rw [hsource] at hsem
      rw [G.sealedRule_reveal node producer owner guard hsem hproducer]
      simp

/-- Every prerequisite of a compiled rule has a strictly smaller rule index. -/
theorem compile_rule_requires_lt (supported : SealedFragment G ty)
    {index dependency : Nat} {rule : SealedRule Player}
    (hrule : supported.compile.rules[index]? = some rule)
    (hdependency : dependency ∈ rule.requires) :
    dependency < index := by
  rcases supported.ruleAt_exists_node hrule with ⟨node, hindex, rfl⟩
  change dependency ∈ G.messagePrerequisites node at hdependency
  simp only [Graph.messagePrerequisites, List.mem_map, List.mem_filter,
    Graph.mem_nodeOrder, true_and, decide_eq_true_eq] at hdependency
  rcases hdependency with ⟨prior, hprior, rfl⟩
  exact (G.prereq_lt hprior).trans_le (Nat.le_of_eq hindex)

end SealedFragment

end Vegas.EventGraph
