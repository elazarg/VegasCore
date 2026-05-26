/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Basic

/-!
# Event graph construction lemmas

This module proves the structural facts used to extend event graphs while
preserving field lookup, visibility, availability, and well-formedness.
-/

namespace Vegas

namespace EventGraph

namespace Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

theorem field?_append_node_of_some
    (initialFields : List (InitialField Player L))
    (nodes : List (EventNode Player L)) (extra : EventNode Player L)
    {field : Nat} {spec : FieldSpec Player L}
    (h :
      ({ initialFields := initialFields, nodes := nodes } :
        Graph Player L).field? field = some spec) :
    ({ initialFields := initialFields, nodes := nodes ++ [extra] } :
      Graph Player L).field? field = some spec := by
  unfold field? at h ⊢
  by_cases hlt : field < initialFields.length
  · simp only [dite_eq_ite, hlt, ↓reduceIte] at h ⊢
    exact h
  · simp only [dite_eq_ite, hlt, ↓reduceIte] at h ⊢
    cases hget : nodes[field - initialFields.length]? with
    | none => simp [hget] at h
    | some event =>
        have hidx : field - initialFields.length < nodes.length :=
          (List.getElem?_eq_some_iff.mp hget).1
        rw [List.getElem?_append_left hidx]
        exact h

theorem fieldRefPublic_append_node
    (initialFields : List (InitialField Player L))
    (nodes : List (EventNode Player L)) (extra : EventNode Player L)
    {ref : FieldRef L}
    (h :
      ({ initialFields := initialFields, nodes := nodes } :
        Graph Player L).fieldRefPublic ref) :
    ({ initialFields := initialFields, nodes := nodes ++ [extra] } :
      Graph Player L).fieldRefPublic ref := by
  rcases h with ⟨spec, hget, hty, howner⟩
  exact
    ⟨spec, field?_append_node_of_some initialFields nodes extra hget,
      hty, howner⟩

theorem fieldRefVisibleTo_append_node
    (initialFields : List (InitialField Player L))
    (nodes : List (EventNode Player L)) (extra : EventNode Player L)
    (who : Player) {ref : FieldRef L}
    (h :
      ({ initialFields := initialFields, nodes := nodes } :
        Graph Player L).fieldRefVisibleTo who ref) :
    ({ initialFields := initialFields, nodes := nodes ++ [extra] } :
      Graph Player L).fieldRefVisibleTo who ref := by
  rcases h with ⟨spec, hget, hty, howner⟩
  exact
    ⟨spec, field?_append_node_of_some initialFields nodes extra hget,
      hty, howner⟩

theorem fieldAvailableBefore_append_node_of_true
    (initialFields : List (InitialField Player L))
    (nodes : List (EventNode Player L)) (extra : EventNode Player L)
    {node field : Nat}
    (h :
      ({ initialFields := initialFields, nodes := nodes } :
        Graph Player L).fieldAvailableBefore node field = true) :
    ({ initialFields := initialFields, nodes := nodes ++ [extra] } :
      Graph Player L).fieldAvailableBefore node field = true := by
  unfold fieldAvailableBefore at h ⊢
  cases hget :
      ({ initialFields := initialFields, nodes := nodes } :
        Graph Player L).field? field with
  | none => simp [hget] at h
  | some spec =>
      rw [field?_append_node_of_some initialFields nodes extra hget]
      simpa [hget] using h

theorem fieldAvailableBefore_next_of_true
    (initialFields : List (InitialField Player L))
    (nodes : List (EventNode Player L)) (extra : EventNode Player L)
    {field : Nat}
    (h :
      ({ initialFields := initialFields, nodes := nodes } :
        Graph Player L).fieldAvailableBefore nodes.length field = true) :
    ({ initialFields := initialFields, nodes := nodes ++ [extra] } :
      Graph Player L).fieldAvailableBefore (nodes ++ [extra]).length field = true := by
  unfold fieldAvailableBefore at h ⊢
  cases hget :
      ({ initialFields := initialFields, nodes := nodes } :
        Graph Player L).field? field with
  | none => simp [hget] at h
  | some spec =>
      rw [field?_append_node_of_some initialFields nodes extra hget]
      cases hsource : spec.source with
      | initial value => simp [hsource]
      | event writer =>
          have hwriter : writer < nodes.length := by
            simpa [hget, hsource] using h
          exact by
            simpa [hsource] using Nat.le_of_lt hwriter

theorem nodeWFAt_append_node
    (initialFields : List (InitialField Player L))
    (nodes : List (EventNode Player L)) (extra : EventNode Player L)
    (node : Nat) (event : EventNode Player L)
    (h :
      ({ initialFields := initialFields, nodes := nodes } :
        Graph Player L).nodeWFAt node event) :
    ({ initialFields := initialFields, nodes := nodes ++ [extra] } :
      Graph Player L).nodeWFAt node event := by
  cases event with
  | mk ty owner sem =>
      cases sem with
      | sample dist =>
          rcases h with ⟨havail, hty, howner, hpublic⟩
          exact
            ⟨by
                intro field hfield
                exact fieldAvailableBefore_append_node_of_true
                  initialFields nodes extra (havail field hfield),
              hty, howner,
              by
                intro ref href
                exact fieldRefPublic_append_node
                  initialFields nodes extra (hpublic ref href)⟩
      | commit who guard =>
          rcases h with ⟨havail, hty, howner, hvisible⟩
          exact
            ⟨by
                intro field hfield
                exact fieldAvailableBefore_append_node_of_true
                  initialFields nodes extra (havail field hfield),
              hty, howner,
              by
                intro ref href
                exact fieldRefVisibleTo_append_node
                  initialFields nodes extra who (hvisible ref href)⟩
      | reveal source =>
          rcases h with
            ⟨havail, sourceSpec, hsource, hty, hsourceOwner, howner⟩
          refine
            ⟨by
                intro field hfield
                exact fieldAvailableBefore_append_node_of_true
                  initialFields nodes extra (havail field hfield),
              sourceSpec,
              field?_append_node_of_some initialFields nodes extra hsource,
              hty, hsourceOwner, howner⟩

theorem WF_empty (initialFields : List (InitialField Player L)) :
    ({ initialFields := initialFields, nodes := [] } : Graph Player L).WF := by
  intro node event hget
  simp at hget

theorem WF_append_event
    (initialFields : List (InitialField Player L))
    (nodes : List (EventNode Player L)) (event : EventNode Player L)
    (hnode :
      ({ initialFields := initialFields, nodes := nodes ++ [event] } :
        Graph Player L).nodeWFAt nodes.length event)
    (hwf :
      ({ initialFields := initialFields, nodes := nodes } :
        Graph Player L).WF) :
    ({ initialFields := initialFields, nodes := nodes ++ [event] } :
      Graph Player L).WF := by
  intro node query hget
  by_cases hlt : node < nodes.length
  · have hold : nodes[node]? = some query := by
      change (nodes ++ [event])[node]? = some query at hget
      rw [List.getElem?_append_left hlt] at hget
      exact hget
    exact nodeWFAt_append_node initialFields nodes event node query
      (hwf node query hold)
  · have hidx : node < (nodes ++ [event]).length :=
      (List.getElem?_eq_some_iff.mp hget).1
    have hnodeEq : node = nodes.length := by
      simp only [List.length_append, List.length_singleton] at hidx
      omega
    subst hnodeEq
    have hquery : query = event := by
      change (nodes ++ [event])[nodes.length]? = some query at hget
      rw [List.getElem?_concat_length] at hget
      exact (Option.some.inj hget).symm
    subst hquery
    simpa using hnode

end Graph

end EventGraph

end Vegas
