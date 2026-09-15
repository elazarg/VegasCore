/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.ProtocolOrder

/-! # Realizing semantically valid graph assignments

A canonical completion is ordinarily only store assembly.  This module shows
that, when every assembled node value has the declared type and satisfies its
node semantics in the completed store, the assignment is also realized by an
actual graph execution.  The proof executes the canonical ready order and
uses well-formedness to show that later writes cannot change the current
node's read environment.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace Config

variable {G : Graph Player L}

/-- Completing a node-typed schedule preserves graph-store coherence. -/
private theorem scheduleComplete_storeCoherent
    (values : Fin G.nodeCount → TypedValue L)
    (htyped : ∀ node, (values node).ty = (G.nodeRow node).ty) :
    ∀ (cfg : Config G) (order : List (Fin G.nodeCount)),
      StoreCoherent G cfg → StoreCoherent G (cfg.scheduleComplete values order) := by
  intro cfg order hcoherent
  induction order generalizing cfg with
  | nil => exact hcoherent
  | cons node rest ih =>
      rw [scheduleComplete, List.map_cons, completeNodes_cons]
      exact ih (cfg := cfg.completeNode node (values node))
        (hcoherent.completeNodeTyped
        (G.nodes_get?_nodeRow node) (values node) (htyped node))

/-- A node-typed canonical completion has a coherent store, independently of
whether its values satisfy the graph's local semantics. -/
theorem canonicalCompletion_storeCoherent
    (G : Graph Player L) (values : Fin G.nodeCount → TypedValue L)
    (htyped : ∀ node, (values node).ty = (G.nodeRow node).ty) :
    StoreCoherent G (Config.canonicalCompletion G values) := by
  unfold canonicalCompletion
  exact scheduleComplete_storeCoherent values htyped
    (Config.initial G) G.nodeOrder (initial_storeCoherent G)

/-- Along a legal schedule, completing the current node and every later node
does not change any field read by the current row. -/
private theorem scheduleComplete_getAs_of_current_read
    (hwf : G.WF) {cfg : Config G} {node : Fin G.nodeCount}
    {row : EventNode Player L} (hrow : G.nodes[node]? = some row)
    (hready : Ready G cfg node) {rest : List (Fin G.nodeCount)}
    (hrest : G.ReadyOrder (insert node cfg.done) rest)
    (hclosed : DonePrereqs G cfg)
    (values : Fin G.nodeCount → TypedValue L)
    {field : Nat} {ty : L.Ty} (hread : field ∈ row.sem.reads) :
    Store.getAs (cfg.scheduleComplete values (node :: rest)).store field ty =
      Store.getAs cfg.store field ty := by
  unfold scheduleComplete
  apply completeNodes_getAs_of_not_targets
  intro step hstep
  rcases List.mem_map.mp hstep with ⟨other, hother, rfl⟩
  rcases List.mem_cons.mp hother with heq | htail
  · subst other
    intro hfield
    apply G.nodeTarget_not_mem_own_reads hwf hrow
    simpa [hfield] using hread
  · rcases G.nodes_get_of_fin other with ⟨otherRow, hotherRow⟩
    have hclosedAfter :
        DonePrereqs G (cfg.completeNode node (values node)) :=
      hclosed.completeNode hready (values node)
    have hotherNotDone :
        other ∉ (cfg.completeNode node (values node)).done := by
      simpa [Config.completeNode] using hrest.not_mem_of_mem htail
    have hnotRead : G.nodeTarget other ∉ row.sem.reads :=
      hclosedAfter.nodeTarget_not_mem_reads_of_not_done hwf hrow hotherRow
        (by simp [Config.completeNode]) hotherNotDone
    intro hfield
    apply hnotRead
    simpa [hfield] using hread

/-- Semantic validity in the completed schedule supplies an actual supported
event writing the prescribed value at the current ready node. -/
private theorem prescribed_step_supported
    (hwf : G.WF) (values : Fin G.nodeCount → TypedValue L)
    (_htyped : ∀ node, (values node).ty = (G.nodeRow node).ty)
    {cfg : Config G} {node : Fin G.nodeCount}
    (hready : Ready G cfg node) {rest : List (Fin G.nodeCount)}
    (hrest : G.ReadyOrder (insert node cfg.done) rest)
    (hclosed : DonePrereqs G cfg)
    (hvalid : NodeValueValid G (cfg.scheduleComplete values (node :: rest)) node) :
    ∃ event : AvailableEvent G cfg,
      cfg.completeNode node (values node) ∈
        (stepAvailableEvent G cfg event).support := by
  rcases hvalid with ⟨row, hrow, hvalid⟩
  have htarget (ty : L.Ty) :
      Store.getAs (cfg.scheduleComplete values (node :: rest)).store
          (G.nodeTarget node) ty =
        (values node).as? ty := by
    unfold scheduleComplete
    apply completeNodes_getAs_of_mem cfg
    · have horder : G.ReadyOrder cfg.done (node :: rest) :=
        ⟨hready.1, hready.2, hrest⟩
      rw [map_fst_pair]
      exact horder.nodup
    · simp
  have henvCurrent {refs : Finset (FieldRef L)} {env : ReadEnv L refs}
      (hsemReads : refs.image FieldRef.field ⊆ row.sem.reads)
      (henv : ReadEnv.ofStore?
        (cfg.scheduleComplete values (node :: rest)).store refs = some env) :
      ReadEnv.ofStore? cfg.store refs = some env := by
    apply ReadEnv.ofStore?_eq_of_getAs_eq henv
    intro ref href
    exact scheduleComplete_getAs_of_current_read hwf hrow hready hrest hclosed values
      (hsemReads (Finset.mem_image.mpr ⟨ref, href, rfl⟩))
  cases hsem : row.sem with
  | sample dist =>
      rw [hsem] at hvalid
      rcases hvalid with ⟨value, hvalue, env, henv, hsupport⟩
      have hwrite : values node = { ty := dist.ty, value := value } := by
        apply TypedValue.eq_mk_of_as?_eq_some
        rw [← htarget dist.ty]
        exact hvalue
      have henv' : ReadEnv.ofStore? cfg.store dist.reads = some env :=
        henvCurrent (by simp [FieldRef.fields, hsem, NodeSem.reads]) henv
      let event : AvailableEvent G cfg := .internal { node := node }
        (.sample row dist hrow hsem hready env henv')
      refine ⟨event, ?_⟩
      change cfg.completeNode node (values node) ∈
        (FinDist.map
          (fun sampled => cfg.completeNode node { ty := dist.ty, value := sampled })
          (dist.eval env)).support
      rw [FinDist.support_map]
      exact ⟨value, hsupport, by rw [hwrite]⟩
  | commit who guard =>
      rw [hsem] at hvalid
      rcases hvalid with ⟨value, hvalue, env, henv, hguard⟩
      have hwrite : values node = { ty := guard.ty, value := value } := by
        apply TypedValue.eq_mk_of_as?_eq_some
        rw [← htarget guard.ty]
        exact hvalue
      have henv' : ReadEnv.ofStore? cfg.store guard.choiceReads = some env :=
        henvCurrent (by simp [FieldRef.fields, hsem, NodeSem.reads]) henv
      let action : CommitAction G who := { node := node, value := values node }
      have hvalueOk : action.value.as? guard.ty = some value := by
        change (values node).as? guard.ty = some value
        rw [hwrite]
        simp [TypedValue.as?]
      let event : AvailableEvent G cfg := .commit who action
        { row := row
          guard := guard
          row_get := hrow
          sem_eq := hsem
          ready := hready
          value := value
          value_ok := hvalueOk
          env := env
          env_ok := henv'
          guard_ok := hguard }
      refine ⟨event, ?_⟩
      change cfg.completeNode node (values node) ∈
        (FinDist.pure (cfg.completeNode node { ty := guard.ty, value := value })).support
      exact FinDist.mem_support_pure.mpr (by rw [hwrite])
  | reveal source =>
      rw [hsem] at hvalid
      rcases hvalid with ⟨value, hvalue, hsource⟩
      have hwrite : values node = { ty := row.ty, value := value } := by
        apply TypedValue.eq_mk_of_as?_eq_some
        rw [← htarget row.ty]
        exact hvalue
      have hsourceCurrent : Store.getAs cfg.store source row.ty = some value := by
        rw [← hsource]
        exact (scheduleComplete_getAs_of_current_read
          (field := source) (ty := row.ty) hwf hrow hready hrest hclosed values
          (by simp [hsem, NodeSem.reads])).symm
      let event : AvailableEvent G cfg := .internal { node := node }
        (.reveal row source hrow hsem hready value hsourceCurrent)
      refine ⟨event, ?_⟩
      change cfg.completeNode node (values node) ∈
        (FinDist.pure (cfg.completeNode node { ty := row.ty, value := value })).support
      exact FinDist.mem_support_pure.mpr (by rw [hwrite])

/-- A legal schedule whose assembled result validates every scheduled node is
realizable by graph execution. -/
private theorem scheduleComplete_reachable
    (hwf : G.WF) (values : Fin G.nodeCount → TypedValue L)
    (htyped : ∀ node, (values node).ty = (G.nodeRow node).ty) :
    ∀ {cfg : Config G} {order : List (Fin G.nodeCount)},
      Reachable G cfg → G.ReadyOrder cfg.done order →
      (∀ node ∈ order, NodeValueValid G (cfg.scheduleComplete values order) node) →
      Reachable G (cfg.scheduleComplete values order) := by
  intro cfg order hreach horder hvalid
  induction order generalizing cfg with
  | nil => simpa [scheduleComplete] using hreach
  | cons node rest ih =>
      have hready : Ready G cfg node := ⟨horder.1, horder.2.1⟩
      have hstep := prescribed_step_supported hwf values htyped hready
        horder.2.2 (reachable_donePrereqs hreach) (hvalid node (by simp))
      rcases hstep with ⟨event, hstep⟩
      have hreach' : Reachable G (cfg.completeNode node (values node)) :=
        Reachable.step hreach event hstep
      rw [scheduleComplete, List.map_cons, completeNodes_cons]
      apply ih hreach' horder.2.2
      intro later hlater
      simpa [scheduleComplete] using hvalid later (by simp [hlater])

/-- Every node-typed, locally valid canonical completion is realized by an
actual graph execution.  Sample validity includes the required support witness;
commit validity includes the guard proof; reveals agree with their source. -/
theorem canonicalCompletion_reachable
    (G : Graph Player L) (hwf : G.WF)
    (values : Fin G.nodeCount → TypedValue L)
    (htyped : ∀ node, (values node).ty = (G.nodeRow node).ty)
    (hvalid : ∀ node, NodeValueValid G (Config.canonicalCompletion G values) node) :
    Reachable G (Config.canonicalCompletion G values) := by
  unfold canonicalCompletion
  apply scheduleComplete_reachable hwf values htyped Reachable.initial
    (Graph.nodeOrder_readyOrder G)
  intro node hnode
  exact hvalid node

end Config

end Vegas.EventGraph
