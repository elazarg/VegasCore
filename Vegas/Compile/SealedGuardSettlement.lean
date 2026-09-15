/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedGuardValidation
import Vegas.Compile.SealedPublicStorePersistence
import Interaction.SealedOpeningHistory

/-! # Guard legality of public settlement values

Historical admission and unique event indices imply that every non-default
opening passes its compiled guard against the final public store. A default
instead uses the source's separate default-legality premise. These statements
apply to the actual guarded candidate host; they do not assume every candidate
has a legal hidden value. Constructing a whole graph realization additionally
requires agreement of the graph decision's guard dependencies with this store.
-/

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A compiled opening check that succeeded at admission remains true after
extending the event log without repeating node indices. -/
theorem sealedOpeningValidator_preserved (G : Graph Player L) (ty : L.Ty)
    (beforeEvents afterEvents : List (SealedProgram.Event Player (L.Val ty)))
    (hnodup : ((beforeEvents ++ afterEvents).map SealedProgram.Event.node).Nodup)
    (node : Nat) (value : L.Val ty)
    (hvalid : G.sealedOpeningValidator ty node beforeEvents value = true) :
    G.sealedOpeningValidator ty node (beforeEvents ++ afterEvents) value = true := by
  cases hnode : G.node? node with
  | none => simp [sealedOpeningValidator, hnode] at hvalid
  | some sem =>
      cases sem with
      | sample dist => simp [sealedOpeningValidator, hnode] at hvalid
      | commit owner guard => simp [sealedOpeningValidator, hnode] at hvalid
      | reveal source =>
          by_cases hsource : source < G.initialFields.length
          · simp [sealedOpeningValidator, hnode, hsource] at hvalid
          · cases hproducer : G.node? (source - G.initialFields.length) with
            | none => simp [sealedOpeningValidator, hnode, hsource, hproducer] at hvalid
            | some producer =>
                cases producer with
                | sample dist =>
                    simp [sealedOpeningValidator, hnode, hsource, hproducer] at hvalid
                | reveal prior =>
                    simp [sealedOpeningValidator, hnode, hsource, hproducer] at hvalid
                | commit owner guard =>
                    simp only [sealedOpeningValidator, hnode, hsource, ↓reduceIte,
                      hproducer] at hvalid ⊢
                    cases htyped : (⟨ty, value⟩ : TypedValue L).as? guard.ty with
                    | none => simp [htyped] at hvalid
                    | some checked =>
                        simp only [htyped, Option.bind_some] at hvalid ⊢
                        have hcheck : guard.evalValidationStore? checked
                            (G.publicSealedStore ty beforeEvents) = some true := by
                          cases hresult : guard.evalValidationStore? checked
                              (G.publicSealedStore ty beforeEvents) with
                          | none => simp [hresult] at hvalid
                          | some result => cases result <;> simp_all
                        rw [G.guard_validation_prefix ty beforeEvents afterEvents hnodup
                          guard checked hcheck]
                        rfl

/-- Each public opening in an invariant guarded execution is the declared
default or passes the compiled validator against the final public store.
No deadline-relative service or honest-player premise is needed. -/
theorem opened_valid_or_default (G : Graph Player L) (ty : L.Ty)
    (runtime : SealedResolution Player (L.Val ty))
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hhistory : runtime.OpeningHistoryInvariant (G.sealedOpeningValidator ty) state)
    (node : Nat) (value : L.Val ty) (hopened : .opened node value ∈ state.events) :
    value = runtime.nullValue ∨ G.sealedOpeningValidator ty node state.events value = true := by
  rcases hhistory.opening node value hopened with
    ⟨beforeEvents, afterEvents, hevents, hvalid⟩ |
      ⟨owner, source, requires, _hrule, hdefault, _htimeout⟩
  · right
    rw [hevents]
    exact G.sealedOpeningValidator_preserved ty beforeEvents (.opened node value :: afterEvents)
      (hevents ▸ hhistory.nodes_unique) node value hvalid
  · exact Or.inl hdefault

/-- A settled value is legal at any graph decision view agreeing on the guard's
stored dependencies. Normal openings use the recorded validation; timeouts
use legality of the source's designated default. Private choice-only reads do
not need to agree with the public store. -/
theorem opened_guard_legal (G : Graph Player L)
    (node producer : Nat) (owner : Player) (guard : EventGuard L)
    (hnode : G.node? node = some (.reveal (G.nodeTarget producer)))
    (hproducer : G.node? producer = some (.commit owner guard))
    (runtime : SealedResolution Player (L.Val guard.ty))
    (state : SealedResolution.PublicState Player (L.Val guard.ty))
    (hhistory : runtime.OpeningHistoryInvariant (G.sealedOpeningValidator guard.ty) state)
    (hdefault : ∀ reads, guard.eval runtime.nullValue reads = true)
    (value : L.Val guard.ty) (hopened : .opened node value ∈ state.events)
    (reads : ReadEnv L guard.choiceReads)
    (hagrees : ∀ ref (href : ref ∈ guard.validationReads),
      Store.getAs (G.publicSealedStore guard.ty state.events) ref.field ref.ty =
        some (reads.read ref (guard.validationReads_subset href))) :
    guard.eval value reads = true := by
  rcases G.opened_valid_or_default guard.ty runtime state hhistory node value hopened with
    rfl | hvalid
  · exact hdefault reads
  · rw [G.sealedOpeningValidator_reveal node producer owner guard hnode hproducer,
      guard.evalValidationStore?_eq_some value reads _ hagrees] at hvalid
    exact hvalid

end Vegas.EventGraph.Graph

/-- info: 'Vegas.EventGraph.Graph.opened_guard_legal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.Graph.opened_guard_legal
