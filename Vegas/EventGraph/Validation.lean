/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Information

/-! # Observation-local prevalidation

An owner can evaluate a proposed resolution using its own binding and public
data. It needs no foreign hidden binding. Thus checking whether an opening
would publish success can happen before sending that opening publicly.
These laws concern the ideal graph kernel; the public protocol must implement
the corresponding emission rule and preserve its information dependencies.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Every store operand of a deferred guard is a public field. Pending and
the current proposal are literal operands rather than hidden store reads. -/
theorem GuardOperand.field?_isPublic {currentPayload payload : L.Ty}
    (operand : GuardOperand graph.layout currentPayload payload)
    (field : graph.Field) (found : operand.field? = some field) :
    graph.fieldPublic field := by
  cases operand with
  | pending | proposed => cases found
  | publicData ref =>
      have same : ref.field = field := Option.some.inj found
      subst field
      change (graph.layout ref.field).IsPublic
      rw [ref.layout_eq]
      trivial
  | publication ref =>
      have same : ref.field = field := Option.some.inj found
      subst field
      change (graph.layout ref.field).IsPublic
      rw [ref.layout_eq]
      trivial

omit [DecidableEq Player] in
/-- A proposed guard verdict depends only on public store data and the
explicit proposal, irrespective of other players' hidden bindings. -/
theorem DeferredCheck.eval?_publicStore {payload : L.Ty}
    (check : DeferredCheck graph.layout payload)
    (store : Store graph.layout) (proposal : PublicationResult (L.Val payload)) :
    check.eval? (graph.publicStore store) proposal = check.eval? store proposal := by
  apply check.eval?_congr_reads
  · intro field found
    exact graph.publicStore_of_public store field
      (check.subjectRead.field?_isPublic field found)
  · intro name input ref field found
    exact graph.publicStore_of_public store field
      ((check.reads ref).field?_isPublic field found)

theorem DeferredCheck.eval?_playerStore {payload : L.Ty}
    (check : DeferredCheck graph.layout payload) (who : Player)
    (store : Store graph.layout) (proposal : PublicationResult (L.Val payload)) :
    check.eval? (graph.playerStore who store) proposal = check.eval? store proposal := by
  have unchanged : ∀ field, graph.fieldPublic field →
      graph.playerStore who store field = store field := by
    intro field isPublic
    apply graph.playerStore_of_visible
    change (graph.layout field).VisibleTo who
    change (graph.layout field).IsPublic at isPublic
    cases kind : graph.layout field <;> simp_all [EventField.IsPublic, EventField.VisibleTo]
  apply check.eval?_congr_reads
  · intro field found
    exact unchanged field (check.subjectRead.field?_isPublic field found)
  · intro name input ref field found
    exact unchanged field ((check.reads ref).field?_isPublic field found)

theorem DeferredCheck.allAccepted?_playerStore {payload : L.Ty}
    (checks : List (DeferredCheck graph.layout payload)) (who : Player)
    (store : Store graph.layout) (proposal : PublicationResult (L.Val payload)) :
    DeferredCheck.allAccepted? checks (graph.playerStore who store) proposal =
      DeferredCheck.allAccepted? checks store proposal := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      simp only [DeferredCheck.allAccepted?, check.eval?_playerStore who store proposal, ih]

/-- Owner-local prevalidation computes exactly the resolution kernel that the
semantic store would compute, including rejection and failure. This does not
require a successful opening or a feasible guard. -/
theorem EventCode.resolve_eval?_playerStore {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (store : Store graph.layout) (disclose : Bool) :
    (EventCode.resolve owner payload binding checks).eval? disclose
        (graph.playerStore owner store) =
      (EventCode.resolve owner payload binding checks).eval? disclose store := by
  simp only [EventCode.eval?]
  rw [binding.get?_playerStore owner store rfl]
  congr 1
  funext bound
  rw [DeferredCheck.allAccepted?_playerStore]

end Vegas.EventGraph
