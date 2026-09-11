/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedCompiler
import VegasTests.PendingSource
import VegasTests.PendingExecution

/-! # Regressions for the strict sealed compiler edge -/

namespace VegasTests.SealedCompiler

open Interaction Vegas Vegas.EventGraph VegasTests.PendingSource VegasTests.PendingExecution

noncomputable section

theorem compilation : SealedCompilation source (.option .bool) where
  supported := sealedFragment

theorem one_rule_per_graph_node :
    compilation.program.rules.length = graph.nodeCount := by
  exact compilation.program_rule_count

theorem source_commit_and_reveal_are_distinct_rules :
    (∃ rule, compilation.program.rules[0]? = some rule ∧
        rule.kind = SealedRuleKind.commit (0 : PendingSource.Player)) ∧
      compilation.program.rules[2]? =
        some (SealedRule.mk (SealedRuleKind.reveal (0 : PendingSource.Player) 0) [0, 1]) := by
  change (∃ rule, sealedFragment.compile.rules[0]? = some rule ∧
      rule.kind = SealedRuleKind.commit (0 : PendingSource.Player)) ∧
    sealedFragment.compile.rules[2]? =
      some (SealedRule.mk (SealedRuleKind.reveal (0 : PendingSource.Player) 0) [0, 1])
  constructor
  · have h := sealedFragment.compile_rule (node 0)
    refine ⟨graph.sealedRule (node 0), h, ?_⟩
    rw [Graph.sealedRule_commit_eq graph (node 0) 0 _ rfl]
  · have h := sealedFragment.compile_rule (node 2)
    have hrule : graph.sealedRule (node 2) =
        SealedRule.mk (SealedRuleKind.reveal (0 : PendingSource.Player) 0) [0, 1] := by
      rw [Graph.sealedRule_reveal_eq graph (node 2) (node 0) 0 _ rfl rfl]
      rw [PendingSource.node2_messagePrerequisites]
      rfl
    rw [hrule] at h
    exact h

theorem cleartext_never_advances_application :
    SealedProgram.validateMessage? compilation.program
        (SealedProgram.State.empty PendingSource.Player Value).service
        (SealedProgram.State.empty PendingSource.Player Value).events
        ⟨(0, 0), .cleartext 0 none⟩ = none := by
  exact SealedProgram.validateMessage?_cleartext_none _ _ _ _ _

theorem strict_source_edge :
    ∀ actions : List (SealedProgram.Action PendingSource.Player Value),
      ∃ cfg : Config PendingSource.graph,
        graph.decodeSealed (.option .bool)
            (SealedProgram.run compilation.program
              (SealedProgram.State.empty PendingSource.Player Value) actions) = some cfg ∧
          Reachable PendingSource.graph cfg := by
  intro actions
  obtain ⟨cfg, hdecode, hreachable, _⟩ := compilation.run_source actions
  exact ⟨cfg, hdecode, hreachable⟩

end

end VegasTests.SealedCompiler
