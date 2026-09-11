/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureTrace

/-! # Reachability of canonical disclosure prefixes -/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory.Math.Probability

private theorem typedValue_eq_cast {left right : simpleExpr.Ty} (h : left = right)
    (value : simpleExpr.Val left) :
    (⟨left, value⟩ : TypedValue simpleExpr) =
      ⟨right, cast (congrArg simpleExpr.Val h) value⟩ := by
  cases h
  rfl

private theorem guard_eval_cast {left right : EventGuard simpleExpr}
    (h : left = right) (value : simpleExpr.Val left.ty)
    (env : ReadEnv simpleExpr right.choiceReads)
    (hok : left.eval value
      (cast (congrArg (ReadEnv simpleExpr ∘ EventGuard.choiceReads) h.symm) env) = true) :
    right.eval (cast (congrArg simpleExpr.Val (congrArg EventGuard.ty h)) value) env = true := by
  cases h
  exact hok

private theorem reachable_commit_value {G : Graph TestPlayer simpleExpr}
    {state : Config G} (hreach : Reachable G state) {who : TestPlayer}
    {action : CommitAction G who} (step : CommitStep G state who action)
    (value : simpleExpr.Val step.guard.ty) (hvalue : step.guard.eval value step.env = true) :
    Reachable G
      (state.completeNode action.node ⟨step.guard.ty, value⟩) := by
  let selected : CommitAction G who :=
    ⟨action.node, ⟨step.guard.ty, value⟩⟩
  let selectedStep : CommitStep G state who selected :=
    { row := step.row
      guard := step.guard
      row_get := step.row_get
      sem_eq := step.sem_eq
      ready := step.ready
      value := value
      value_ok := by simp [selected, TypedValue.as?]
      env := step.env
      env_ok := step.env_ok
      guard_ok := hvalue }
  apply Reachable.step hreach (.commit who selected selectedStep)
  simp [stepAvailableEvent, stepCommit, selected, selectedStep]

private theorem opening_guard_valid (data : RunData) (hvalid : data.Valid)
    (guard : EventGuard simpleExpr)
    (hsem : (graph.nodeRow (node 4)).sem = .commit 0 guard)
    (env : ReadEnv simpleExpr guard.choiceReads)
    (henv : ReadEnv.ofStore? (cfg data 4).store guard.choiceReads = some env) :
    ∃ value : simpleExpr.Val guard.ty,
      guard.eval value env = true ∧
      (⟨guard.ty, value⟩ : TypedValue simpleExpr) = data.value 4 := by
  have hguard := (NodeSem.commit.inj hsem).2
  subst guard
  refine ⟨data.opening, ?_, rfl⟩
  have hsecret := ReadEnv.ofStore?_read henv (ref := ⟨0, .bool⟩) (by decide)
  change some data.secret = some (env.read ⟨0, .bool⟩ _) at hsecret
  have hsecret' := Option.some.inj hsecret
  change (if data.opening.isNone then true
    else decide (data.opening = some (env.read ⟨0, .bool⟩ (by decide)))) = true
  rw [← hsecret']
  rcases hvalid with h | h <;> simp [h]

private theorem sample3 (data : RunData) (hreach : Reachable graph (cfg data 3)) :
    Reachable graph (cfg data 4) := by
  have hready := (ready_iff data 3 (node 3)).mpr rfl
  obtain ⟨event, hevent⟩ := exists_availableEvent_of_ready compiled.graphWF
    (ToEventGraph.compile_guardLive source legal) (state := ⟨_, hreach⟩) hready
  have hn : event.node = node 3 := hevent
  cases event with
  | commit who action step =>
      have hr := Option.some.inj
        (step.row_get.symm.trans (graph.nodes_get?_nodeRow action.node))
      have hs := step.sem_eq
      change action.node = node 3 at hn
      rw [hr, hn] at hs
      cases hs
  | internal event step =>
      change event.node = node 3 at hn
      cases step with
      | reveal row sf row_get sem_eq ready value value_ok =>
          have hr := Option.some.inj
            (row_get.symm.trans (graph.nodes_get?_nodeRow event.node))
          rw [hr, hn] at sem_eq
          cases sem_eq
      | sample row dist row_get sem_eq ready env env_ok =>
          have hr : row = graph.nodeRow event.node := Option.some.inj
            (row_get.symm.trans (graph.nodes_get?_nodeRow event.node))
          have hs := sem_eq
          rw [hr, hn] at hs
          cases hs
          rw [show cfg data 4 = (cfg data 3).completeNode (node 3) (data.value 3) from
            cfg_succ data 3, ← hn]
          apply Reachable.step hreach (.internal event
            (.sample row _ row_get sem_eq ready env env_ok))
          simp only [stepAvailableEvent, stepInternal]
          rw [FinDist.support_map]
          refine ⟨data.signal, ?_, ?_⟩
          · have hsupp : data.signal ∈ fairCoin.denote.support := by
              apply FinDist.prob_pos_iff.mp
              rw [RationalLaw.prob_denote]
              cases data.signal <;> simp [fairCoin, Fin.sum_univ_two]
            simp only [EventDist.eval, EventDist.evalLaw, ToEventGraph.eventDistOf,
              evalLawDistExprDeps]
            split <;> exact hsupp
          · rfl

private theorem cfg_step (data : RunData) (hvalid : data.Valid) (phase : Fin 8)
    (hreach : Reachable graph (cfg data phase.castSucc)) :
    Reachable graph (cfg data phase.succ) := by
  have hready : Ready graph (cfg data phase.castSucc) (node phase) :=
    (ready_iff data phase.castSucc (node phase)).mpr rfl
  obtain ⟨event, hevent⟩ := exists_availableEvent_of_ready compiled.graphWF
    (ToEventGraph.compile_guardLive source legal) (state := ⟨_, hreach⟩) hready
  have heventNode : event.node = node phase := hevent
  fin_cases phase
  · cases event with
    | commit who action step =>
        simp only [AvailableEvent.node_commit] at heventNode
        have hrow : step.row = graph.nodeRow action.node := by
          exact Option.some.inj (step.row_get.symm.trans
            (graph.nodes_get?_nodeRow action.node))
        have hsem := step.sem_eq
        rw [hrow] at hsem
        rw [heventNode] at hsem
        change NodeSem.commit 0 _ = NodeSem.commit who step.guard at hsem
        obtain ⟨rfl, hguard⟩ := NodeSem.commit.inj hsem
        have hty : (.bool : simpleExpr.Ty) = step.guard.ty :=
          congrArg EventGuard.ty hguard
        let desired := cast (congrArg simpleExpr.Val hty) data.secret
        have hall : ∀ value : simpleExpr.Val step.guard.ty,
            ∀ env : ReadEnv simpleExpr step.guard.choiceReads,
              step.guard.eval value env = true := by
          rw [← hguard]
          intro value env
          rfl
        have hnext := reachable_commit_value hreach step desired (hall desired step.env)
        rw [cfg_succ, ← heventNode]
        simpa only [desired, RunData.value, typedValue_eq_cast hty data.secret] using hnext
    | internal internal step =>
        simp only [AvailableEvent.node_internal] at heventNode
        cases step with
        | sample row dist row_get sem_eq ready env env_ok =>
            have hrow : row = graph.nodeRow internal.node := by
              exact Option.some.inj (row_get.symm.trans
                (graph.nodes_get?_nodeRow internal.node))
            rw [hrow] at sem_eq
            rw [heventNode] at sem_eq
            cases sem_eq
        | reveal row sourceField row_get sem_eq ready value value_ok =>
            have hrow : row = graph.nodeRow internal.node := by
              exact Option.some.inj (row_get.symm.trans
                (graph.nodes_get?_nodeRow internal.node))
            rw [hrow] at sem_eq
            rw [heventNode] at sem_eq
            cases sem_eq
  · cases event with
    | commit who action step =>
        simp only [AvailableEvent.node_commit] at heventNode
        have hrow : step.row = graph.nodeRow action.node :=
          Option.some.inj (step.row_get.symm.trans (graph.nodes_get?_nodeRow action.node))
        have hsem := step.sem_eq
        rw [hrow, heventNode] at hsem
        change NodeSem.commit 0 _ = NodeSem.commit who step.guard at hsem
        obtain ⟨rfl, hguard⟩ := NodeSem.commit.inj hsem
        have hty : (.bool : simpleExpr.Ty) = step.guard.ty :=
          congrArg EventGuard.ty hguard
        let desired := cast (congrArg simpleExpr.Val hty) false
        have hok : step.guard.eval desired step.env = true := by
          apply guard_eval_cast hguard false step.env
          rfl
        have hnext := reachable_commit_value hreach step desired hok
        rw [cfg_succ, ← heventNode]
        simpa only [desired, RunData.value, typedValue_eq_cast hty false] using hnext
    | internal internal step =>
        simp only [AvailableEvent.node_internal] at heventNode
        cases step with
        | sample row dist row_get sem_eq ready env env_ok =>
            have hrow : row = graph.nodeRow internal.node := by
              exact Option.some.inj (row_get.symm.trans
                (graph.nodes_get?_nodeRow internal.node))
            rw [hrow] at sem_eq
            rw [heventNode] at sem_eq
            cases sem_eq
        | reveal row sourceField row_get sem_eq ready value value_ok =>
            have hrow : row = graph.nodeRow internal.node := by
              exact Option.some.inj (row_get.symm.trans
                (graph.nodes_get?_nodeRow internal.node))
            rw [hrow] at sem_eq
            rw [heventNode] at sem_eq
            cases sem_eq
  · let step : InternalStep graph (cfg data 2) ⟨node 2⟩ :=
      .reveal (graph.nodeRow (node 2)) 1 rfl rfl
        ((ready_iff data 2 (node 2)).mpr rfl) false (by rfl)
    have hnext := Reachable.step hreach (.internal ⟨node 2⟩ step)
      (next := (cfg data 2).completeNode (node 2) ⟨.bool, false⟩)
      (by
        simp only [stepAvailableEvent, stepInternal, step, FinDist.mem_support_pure]
        rfl)
    change Reachable graph ((cfg data 2).completeNode (node 2) ⟨.bool, false⟩)
    exact hnext
  · exact sample3 data hreach
  · cases event with
    | commit who action step =>
        simp only [AvailableEvent.node_commit] at heventNode
        have hrow : step.row = graph.nodeRow action.node := Option.some.inj
          (step.row_get.symm.trans (graph.nodes_get?_nodeRow action.node))
        have hsem := step.sem_eq
        rw [hrow, heventNode] at hsem
        obtain ⟨rfl, _⟩ := NodeSem.commit.inj hsem
        obtain ⟨value, hok, hvalue⟩ := opening_guard_valid data hvalid step.guard hsem
          step.env step.env_ok
        have hnext := reachable_commit_value hreach step value hok
        rw [cfg_succ, ← heventNode]
        simpa [RunData.value, hvalue] using hnext
    | internal internal step =>
        simp only [AvailableEvent.node_internal] at heventNode
        cases step <;> rename_i row arg row_get sem_eq _ _ _
        all_goals
          have hrow := Option.some.inj (row_get.symm.trans
            (graph.nodes_get?_nodeRow internal.node))
          rw [hrow, heventNode] at sem_eq
          cases sem_eq
  · let step : InternalStep graph (cfg data 5) ⟨node 5⟩ :=
      .reveal (graph.nodeRow (node 5)) 4 rfl rfl
        ((ready_iff data 5 (node 5)).mpr rfl) data.opening (by rfl)
    have hnext := Reachable.step hreach (.internal ⟨node 5⟩ step)
      (next := (cfg data 5).completeNode (node 5) ⟨.option .bool, data.opening⟩)
      (by
        simp only [stepAvailableEvent, stepInternal, step, FinDist.mem_support_pure]
        rfl)
    change Reachable graph
      ((cfg data 5).completeNode (node 5) ⟨.option .bool, data.opening⟩)
    exact hnext
  · cases event with
    | commit who action step =>
        simp only [AvailableEvent.node_commit] at heventNode
        have hrow : step.row = graph.nodeRow action.node := Option.some.inj
          (step.row_get.symm.trans (graph.nodes_get?_nodeRow action.node))
        have hsem := step.sem_eq
        rw [hrow, heventNode] at hsem
        change NodeSem.commit 1 _ = NodeSem.commit who step.guard at hsem
        obtain ⟨rfl, hguard⟩ := NodeSem.commit.inj hsem
        have hty : (.bool : simpleExpr.Ty) = step.guard.ty :=
          congrArg EventGuard.ty hguard
        let desired := cast (congrArg simpleExpr.Val hty) data.response
        have hall : ∀ value : simpleExpr.Val step.guard.ty,
            ∀ env : ReadEnv simpleExpr step.guard.choiceReads,
              step.guard.eval value env = true := by
          rw [← hguard]
          intro value env
          rfl
        have hnext := reachable_commit_value hreach step desired (hall desired step.env)
        rw [cfg_succ, ← heventNode]
        simpa only [desired, RunData.value, typedValue_eq_cast hty data.response] using hnext
    | internal internal step =>
        simp only [AvailableEvent.node_internal] at heventNode
        cases step <;> rename_i row arg row_get sem_eq _ _ _
        all_goals
          have hrow := Option.some.inj (row_get.symm.trans
            (graph.nodes_get?_nodeRow internal.node))
          rw [hrow, heventNode] at sem_eq
          cases sem_eq
  · let step : InternalStep graph (cfg data 7) ⟨node 7⟩ :=
      .reveal (graph.nodeRow (node 7)) 6 rfl rfl
        ((ready_iff data 7 (node 7)).mpr rfl) data.response (by rfl)
    have hnext := Reachable.step hreach (.internal ⟨node 7⟩ step)
      (next := (cfg data 7).completeNode (node 7) ⟨.bool, data.response⟩)
      (by
        simp only [stepAvailableEvent, stepInternal, step, FinDist.mem_support_pure]
        rfl)
    change Reachable graph
      ((cfg data 7).completeNode (node 7) ⟨.bool, data.response⟩)
    exact hnext

theorem cfg_reachable (data : RunData) (hvalid : data.Valid) (phase : Fin 9) :
    Reachable graph (cfg data phase) := by
  fin_cases phase
  · simpa [cfg_initial] using (Reachable.initial : Reachable graph (Config.initial graph))
  · exact cfg_step data hvalid 0 (Reachable.initial)
  · exact cfg_step data hvalid 1 (cfg_step data hvalid 0 Reachable.initial)
  · exact cfg_step data hvalid 2 (cfg_step data hvalid 1
      (cfg_step data hvalid 0 Reachable.initial))
  · exact cfg_step data hvalid 3 (cfg_step data hvalid 2
      (cfg_step data hvalid 1 (cfg_step data hvalid 0 Reachable.initial)))
  · exact cfg_step data hvalid 4 (cfg_step data hvalid 3
      (cfg_step data hvalid 2 (cfg_step data hvalid 1
        (cfg_step data hvalid 0 Reachable.initial))))
  · exact cfg_step data hvalid 5 (cfg_step data hvalid 4
      (cfg_step data hvalid 3 (cfg_step data hvalid 2
        (cfg_step data hvalid 1 (cfg_step data hvalid 0 Reachable.initial)))))
  · exact cfg_step data hvalid 6 (cfg_step data hvalid 5
      (cfg_step data hvalid 4 (cfg_step data hvalid 3
        (cfg_step data hvalid 2 (cfg_step data hvalid 1
          (cfg_step data hvalid 0 Reachable.initial))))))
  · exact cfg_step data hvalid 7 (cfg_step data hvalid 6
      (cfg_step data hvalid 5 (cfg_step data hvalid 4
        (cfg_step data hvalid 3 (cfg_step data hvalid 2
          (cfg_step data hvalid 1 (cfg_step data hvalid 0 Reachable.initial)))))))

end VegasTests.OptionalDisclosure
