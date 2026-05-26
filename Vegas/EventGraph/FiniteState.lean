/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Execution

/-!
# Finite graph states

`Config` is the operational store shape: a total function from raw natural field
ids to optional dynamic values.  That is convenient for execution and backend
refinement, but it is not a finite semantic carrier.

`StateSnapshot` is the finite state carrier for graph-level game exports.  It
records exactly the graph-local state: completed node ids and typed values at
the finite set of graph fields.
-/

namespace Vegas

namespace EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Finite graph-local state: completed nodes plus typed values at graph
fields. -/
structure StateSnapshot (G : Graph Player L) where
  done : Finset (Fin G.nodeCount)
  fieldValue? :
    (field : Fin G.fieldCount) →
      Option (L.Val (G.fieldRow field).ty)

namespace StateSnapshot

variable {G : Graph Player L}

namespace Config

@[ext] theorem ext {left right : Config G}
    (hdone : left.done = right.done)
    (hstore : left.store = right.store) :
    left = right := by
  cases left
  cases right
  simp_all

end Config

@[ext] theorem ext {left right : StateSnapshot G}
    (hdone : left.done = right.done)
    (hfields : ∀ field, left.fieldValue? field = right.fieldValue? field) :
    left = right := by
  cases left with
  | mk leftDone leftFields =>
  cases right with
  | mk rightDone rightFields =>
  dsimp at hdone hfields
  subst rightDone
  congr
  funext field
  exact hfields field

noncomputable instance instFintype
    [∀ field : Fin G.fieldCount,
      Fintype (L.Val (G.fieldRow field).ty)] :
    Fintype (StateSnapshot G) := by
  classical
  let raw :=
    Finset (Fin G.nodeCount) ×
      ((field : Fin G.fieldCount) →
        Option (L.Val (G.fieldRow field).ty))
  let e : raw ≃ StateSnapshot G :=
    { toFun := fun data =>
        { done := data.1
          fieldValue? := data.2 }
      invFun := fun snap => (snap.done, snap.fieldValue?)
      left_inv := by
        intro data
        rfl
      right_inv := by
        intro snap
        cases snap
        rfl }
  exact Fintype.ofEquiv raw e

noncomputable instance instDecidableEq : DecidableEq (StateSnapshot G) :=
  Classical.decEq _

/-- Convert a finite graph snapshot to the operational total store.  Raw field
ids outside the graph are absent. -/
noncomputable def store (snapshot : StateSnapshot G) : Store L := by
  classical
  intro field
  exact
    if hfield : field < G.fieldCount then
      let fieldRef : Fin G.fieldCount := ⟨field, hfield⟩
      match snapshot.fieldValue? fieldRef with
      | none => none
      | some value =>
          some { ty := (G.fieldRow fieldRef).ty, value := value }
    else
      none

/-- View a finite graph snapshot as an operational configuration. -/
noncomputable def toConfig (snapshot : StateSnapshot G) : Config G where
  done := snapshot.done
  store := snapshot.store

/-- Project an operational configuration to its finite graph-local snapshot. -/
noncomputable def ofConfig (cfg : Config G) : StateSnapshot G where
  done := cfg.done
  fieldValue? := fun field =>
    Store.getAs cfg.store field (G.fieldRow field).ty

@[simp] theorem toConfig_done (snapshot : StateSnapshot G) :
    snapshot.toConfig.done = snapshot.done := rfl

@[simp] theorem ofConfig_done (cfg : Config G) :
    (ofConfig cfg : StateSnapshot G).done = cfg.done := rfl

@[simp] theorem store_of_ge (snapshot : StateSnapshot G)
    {field : Nat} (hfield : G.fieldCount ≤ field) :
    snapshot.store field = none := by
  simp [store, Nat.not_lt.mpr hfield]

@[simp] theorem store_getAs_field (snapshot : StateSnapshot G)
    (field : Fin G.fieldCount) :
    Store.getAs snapshot.store field (G.fieldRow field).ty =
      snapshot.fieldValue? field := by
  classical
  unfold store Store.getAs
  simp only [field.isLt, ↓reduceDIte]
  cases hvalue : snapshot.fieldValue? field with
  | none =>
      simp
  | some value =>
      simp [TypedValue.as?]

@[simp] theorem ofConfig_toConfig (snapshot : StateSnapshot G) :
    ofConfig snapshot.toConfig = snapshot := by
  apply StateSnapshot.ext
  · rfl
  · intro field
    exact store_getAs_field snapshot field

/-- A raw operational configuration is graph-canonical when its graph-local
finite snapshot reconstructs it exactly. -/
def Canonical (cfg : Config G) : Prop :=
  (ofConfig cfg).toConfig = cfg

/-- Initial stores are exactly the initial values of graph-local field rows. -/
theorem initialStore_eq_fieldRow_initialValue
    (G : Graph Player L) (field : Fin G.fieldCount) :
    G.initialStore field = (G.fieldRow field).initialValue? := by
  unfold Graph.initialStore
  rw [G.field?_fieldRow field]

/-- Reading an initial-store graph field at its declared graph type recovers
the corresponding initial value, when one exists. -/
theorem initialStore_getAs_field
    (G : Graph Player L) (field : Fin G.fieldCount) :
    Store.getAs G.initialStore field (G.fieldRow field).ty =
      match (G.fieldRow field).source with
      | .initial value => some value
      | .event _ => none := by
  unfold Store.getAs
  rw [initialStore_eq_fieldRow_initialValue G field]
  cases hsource : (G.fieldRow field).source with
  | initial value =>
      simp [FieldSpec.initialValue?, hsource, TypedValue.as?]
  | event node =>
      simp [FieldSpec.initialValue?, hsource]

/-- A graph node's canonical output field is a valid graph field. -/
theorem nodeTarget_lt_fieldCount
    (G : Graph Player L) (node : Fin G.nodeCount) :
    G.nodeTarget node < G.fieldCount := by
  unfold Graph.nodeTarget Graph.fieldCount Graph.nodeCount
  omega

/-- The field row at a node's canonical output field is the node row. -/
theorem fieldRow_nodeTarget
    (G : Graph Player L) (node : Fin G.nodeCount) :
    G.fieldRow ⟨G.nodeTarget node, nodeTarget_lt_fieldCount G node⟩ =
      { ty := (G.nodeRow node).ty
        owner := (G.nodeRow node).owner
        source := FieldSource.event (node : Nat) } := by
  apply G.fieldRow_eq_of_field?_some
  exact G.field?_nodeTarget (G.nodes_get?_nodeRow node)

/-- The initial operational configuration is already graph-canonical. -/
theorem canonical_initial (G : Graph Player L) :
    Canonical (Config.initial G) := by
  apply Config.ext
  · rfl
  · funext field
    by_cases hfield : field < G.fieldCount
    · let ref : Fin G.fieldCount := ⟨field, hfield⟩
      dsimp [toConfig, ofConfig, store, Config.initial]
      rw [dif_pos hfield]
      change
        (match Store.getAs G.initialStore field (G.fieldRow ref).ty with
        | none => none
        | some value => some { ty := (G.fieldRow ref).ty, value := value }) =
          G.initialStore field
      rw [initialStore_getAs_field G ref,
        initialStore_eq_fieldRow_initialValue G ref]
      cases hsource : (G.fieldRow ref).source with
      | initial value =>
          simp [FieldSpec.initialValue?, hsource]
      | event node =>
          simp [FieldSpec.initialValue?, hsource]
    · have hnone : G.field? field = none := by
        cases hget : G.field? field with
        | none => rfl
        | some spec =>
            have hlt := G.field_lt_fieldCount_of_field?_some hget
            exact False.elim (hfield hlt)
      simp [toConfig, ofConfig, store, Config.initial, hfield,
        Graph.initialStore, hnone]

/-- A canonical configuration remains canonical after completing a node with a
value at the node's declared output type. -/
theorem canonical_completeNodeTyped
    {G : Graph Player L} {cfg : Config G}
    (hcanonical : Canonical cfg)
    (node : Fin G.nodeCount) (value : TypedValue L)
    (hty : value.ty = (G.nodeRow node).ty) :
    Canonical (cfg.completeNode node value) := by
  apply Config.ext
  · rfl
  · funext field
    have hcanonicalStore :
        (ofConfig cfg).toConfig.store field = cfg.store field :=
      congrFun (congrArg Config.store hcanonical) field
    by_cases hfield : field < G.fieldCount
    · by_cases htarget : field = G.nodeTarget node
      · subst field
        have hrow :
            G.fieldRow
                (⟨G.nodeTarget node, hfield⟩ : Fin G.fieldCount) =
              { ty := (G.nodeRow node).ty
                owner := (G.nodeRow node).owner
                source := FieldSource.event (node : Nat) } := by
          rw [G.fieldRow_mk_eq_mk (G.nodeTarget node) hfield
            (nodeTarget_lt_fieldCount G node)]
          exact fieldRow_nodeTarget G node
        cases value with
        | mk valueTy valueValue =>
            dsimp at hty
            cases hty
            simp [toConfig, ofConfig, store, Config.completeNode, hfield,
              hrow, Store.getAs, Store.set_eq, TypedValue.as?]
      · dsimp [toConfig, ofConfig, store, Config.completeNode]
        rw [dif_pos hfield]
        rw [Store.getAs_set_ne cfg.store htarget value]
        have hcanonicalStore' := hcanonicalStore
        dsimp [toConfig, ofConfig, store] at hcanonicalStore'
        rw [dif_pos hfield] at hcanonicalStore'
        rw [Store.set_ne cfg.store htarget value]
        exact hcanonicalStore'
    · have hout : G.fieldCount ≤ field := Nat.le_of_not_gt hfield
      have htarget : field ≠ G.nodeTarget node := by
        intro heq
        apply hfield
        rw [heq]
        exact nodeTarget_lt_fieldCount G node
      have hcfgNone : cfg.store field = none := by
        have hleftNone : (ofConfig cfg).toConfig.store field = none := by
          change (ofConfig cfg).store field = none
          exact StateSnapshot.store_of_ge (ofConfig cfg) hout
        rw [hleftNone] at hcanonicalStore
        exact hcanonicalStore.symm
      simp [toConfig, ofConfig, store, Config.completeNode, hfield,
        Store.set_ne cfg.store htarget value, hcfgNone]

/-- Supported primitive graph steps complete the event node with a value at
the node row's declared type. -/
theorem stepAvailableEvent_support_completeNodeTyped
    {G : Graph Player L} (hwf : G.WF) {cfg next : Config G}
    (event : AvailableEvent G cfg)
    (hnext : next ∈ (stepAvailableEvent G cfg event).support) :
    ∃ written : TypedValue L,
      written.ty = (G.nodeRow event.node).ty ∧
      next = cfg.completeNode event.node written := by
  cases event with
  | commit who action step =>
      have hpmf :
          stepAvailableEvent G cfg (.commit who action step) =
            PMF.pure
              (cfg.completeNode action.node
                { ty := step.guard.ty, value := step.value }) := by
        rfl
      rw [hpmf, PMF.support_pure, Set.mem_singleton_iff] at hnext
      subst next
      have hrowEq : step.row = G.nodeRow action.node := by
        have hrowGet :
            G.nodes[(action.node : Nat)]? = some step.row := step.row_get
        rw [G.nodes_get?_nodeRow action.node] at hrowGet
        exact (Option.some.inj hrowGet).symm
      have hnodeWF := hwf (action.node : Nat) step.row step.row_get
      unfold Graph.nodeWFAt at hnodeWF
      rw [step.sem_eq] at hnodeWF
      have hrowTy :
          step.row.ty = (G.nodeRow action.node).ty := by
        rw [hrowEq]
      refine
        ⟨{ ty := step.guard.ty, value := step.value },
          hnodeWF.2.1.symm.trans hrowTy, rfl⟩
  | internal internalEvent step =>
      cases step with
      | sample row dist row_get sem_eq ready env env_ok =>
          have hpmf :
              stepAvailableEvent G cfg
                  (.internal internalEvent
                    (.sample row dist row_get sem_eq ready env env_ok)) =
                PMF.map
                  (fun value =>
                    cfg.completeNode internalEvent.node
                      { ty := dist.ty, value := value })
                  (dist.eval env) := by
            rfl
          rw [hpmf] at hnext
          rcases (PMF.mem_support_map_iff _ _ _).mp hnext with
            ⟨value, _hvalue, hnextEq⟩
          subst next
          have hrowEq : row = G.nodeRow internalEvent.node := by
            have hrowGet :
                G.nodes[(internalEvent.node : Nat)]? = some row := row_get
            rw [G.nodes_get?_nodeRow internalEvent.node] at hrowGet
            exact (Option.some.inj hrowGet).symm
          have hnodeWF := hwf (internalEvent.node : Nat) row row_get
          unfold Graph.nodeWFAt at hnodeWF
          rw [sem_eq] at hnodeWF
          have hrowTy :
              row.ty = (G.nodeRow internalEvent.node).ty := by
            rw [hrowEq]
          refine
            ⟨{ ty := dist.ty, value := value },
              hnodeWF.2.1.symm.trans hrowTy, rfl⟩
      | reveal row source row_get sem_eq ready value value_ok =>
          have hpmf :
              stepAvailableEvent G cfg
                  (.internal internalEvent
                    (.reveal row source row_get sem_eq ready value
                      value_ok)) =
                PMF.pure
                  (cfg.completeNode internalEvent.node
                    { ty := row.ty, value := value }) := by
            rfl
          rw [hpmf, PMF.support_pure, Set.mem_singleton_iff] at hnext
          subst next
          have hrowEq : row = G.nodeRow internalEvent.node := by
            have hrowGet :
                G.nodes[(internalEvent.node : Nat)]? = some row := row_get
            rw [G.nodes_get?_nodeRow internalEvent.node] at hrowGet
            exact (Option.some.inj hrowGet).symm
          have hrowTy :
              row.ty = (G.nodeRow internalEvent.node).ty := by
            rw [hrowEq]
          refine
            ⟨{ ty := row.ty, value := value },
              hrowTy, rfl⟩

/-- Canonicality is preserved by supported primitive graph steps. -/
theorem canonical_of_stepAvailableEvent_support
    {G : Graph Player L} (hwf : G.WF) {cfg next : Config G}
    (hcanonical : Canonical cfg)
    (event : AvailableEvent G cfg)
    (hnext : next ∈ (stepAvailableEvent G cfg event).support) :
    Canonical next := by
  rcases stepAvailableEvent_support_completeNodeTyped hwf event hnext with
    ⟨written, hty, rfl⟩
  exact canonical_completeNodeTyped hcanonical event.node written hty

/-- Every reachable raw operational configuration is the reconstruction of its
finite graph snapshot. -/
theorem canonical_reachable
    {G : Graph Player L} (hwf : G.WF) :
    ∀ {cfg : Config G}, Reachable G cfg → Canonical cfg := by
  intro cfg hreach
  induction hreach with
  | initial =>
      exact canonical_initial G
  | step hprev event hnext ih =>
      exact canonical_of_stepAvailableEvent_support hwf ih event hnext

/-- Finite snapshots injectively represent reachable raw configurations. -/
theorem ofConfig_injective_on_reachable
    {G : Graph Player L} (hwf : G.WF) :
    Function.Injective
      (fun state : ReachableConfig G => StateSnapshot.ofConfig state.1) := by
  intro left right hsnapshot
  apply Subtype.ext
  have hleft := canonical_reachable hwf left.2
  have hright := canonical_reachable hwf right.2
  calc
    left.1 = (ofConfig left.1).toConfig := hleft.symm
    _ = (ofConfig right.1).toConfig := by
      rw [show ofConfig left.1 = ofConfig right.1 from hsnapshot]
    _ = right.1 := hright

/-- Reachable graph configurations form a finite state space whenever every
graph field has a finite value domain. -/
@[reducible]
noncomputable def reachableConfigFintype
    (G : Graph Player L) (hwf : G.WF)
    [∀ field : Fin G.fieldCount,
      Fintype (L.Val (G.fieldRow field).ty)] :
    Fintype (ReachableConfig G) :=
  Fintype.ofInjective
    (fun state : ReachableConfig G => StateSnapshot.ofConfig state.1)
    (ofConfig_injective_on_reachable hwf)

/-- The finite snapshot of the operational initial configuration. -/
noncomputable def initial (G : Graph Player L) : StateSnapshot G :=
  ofConfig (Config.initial G)

@[simp] theorem initial_done (G : Graph Player L) :
    (initial G).done = ∅ := rfl

end StateSnapshot

end EventGraph

end Vegas
