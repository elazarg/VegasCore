/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSettledVerdict

/-! # The settled content of a packet is fixed once its event is ready

The settled verdict checks a commitment's handle against the author's bindings
completed before the event, and an opening's guards against the public store.
Both are fixed from the moment the event is ready: later completions append to
the completion order after the event, and write only fields that the event's
guards do not read, since every field an event reads is an input or the output
of a predecessor (`Vegas.EventGraph.reads_available`).
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem takeWhile_ne_append_of_mem {α : Type} [DecidableEq α] (first second : List α)
    (target : α) (member : target ∈ first) :
    (first ++ second).takeWhile (· ≠ target) = first.takeWhile (· ≠ target) := by
  induction first with
  | nil => cases member
  | cons head rest ih =>
      by_cases same : head = target
      · subst same
        simp
      · have inside : target ∈ rest := by
          rcases List.mem_cons.mp member with equal | inside
          · exact (same equal.symm).elim
          · exact inside
        simp only [List.cons_append, List.takeWhile_cons, ne_eq, same, not_false_eq_true,
          decide_true, ih inside]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem takeWhile_ne_append_cons_of_not_mem {α : Type} [DecidableEq α]
    (first second : List α) (target : α) (absent : target ∉ first) :
    (first ++ target :: second).takeWhile (· ≠ target) = first := by
  induction first with
  | nil => simp
  | cons head rest ih =>
      have different : head ≠ target := fun same => absent (same ▸ List.mem_cons_self)
      have restAbsent : target ∉ rest := fun inside => absent (List.mem_cons_of_mem _ inside)
      simp only [List.cons_append, List.takeWhile_cons, ne_eq, different, not_false_eq_true,
        decide_true, ih restAbsent, ↓reduceIte]

/-- Completions after a completed event leave the bindings counted before it
unchanged. -/
theorem PublicView.bindingCountBefore_append (first second : PublicView graph) (who : Player)
    (event : graph.EventId) (member : event ∈ first.observation.completionOrder)
    (rest : List graph.EventId)
    (extended : second.observation.completionOrder = first.observation.completionOrder ++ rest) :
    second.bindingCountBefore who event = first.bindingCountBefore who event := by
  unfold PublicView.bindingCountBefore
  rw [extended, takeWhile_ne_append_of_mem _ _ _ member]

/-- Completing an unfinished event fixes the bindings counted before it at the
count when it completed. -/
theorem PublicView.bindingCountBefore_complete (first second : PublicView graph) (who : Player)
    (event : graph.EventId) (absent : event ∉ first.observation.completionOrder)
    (rest : List graph.EventId)
    (extended : second.observation.completionOrder =
      first.observation.completionOrder ++ event :: rest) :
    second.bindingCountBefore who event = first.bindingCount who := by
  unfold PublicView.bindingCountBefore
  rw [extended, takeWhile_ne_append_cons_of_not_mem _ _ _ absent,
    PublicView.bindingCount_eq_countP]

omit [DecidableEq Player] in
/-- Every field an event reads is available once its predecessors completed. -/
theorem read_available_of_predecessors (config : graph.Config) (event : graph.EventId)
    (settled : ∀ predecessor ∈ graph.order.predecessors event,
      predecessor ∈ config.cut.completed)
    {field : graph.Field} (read : field ∈ (graph.nodes event).readFields) :
    (config.store field).isSome := by
  cases field with
  | inl input => simp [Config.store]
  | inr producer =>
      rw [Config.store_output, config.output_available]
      exact settled producer (graph.reads_available event (.inr producer) read)

omit [DecidableEq Player] in
/-- The public guard verdict on an opening is fixed by every store that retains
the fields available once the event's predecessors completed. -/
theorem State.openingGuardsAccepted_congr (first second : State graph)
    (packet : WitnessedPacket graph) (event : graph.EventId)
    (named : packet.call.event? graph = some event)
    (settled : ∀ predecessor ∈ graph.order.predecessors event,
      predecessor ∈ first.config.cut.completed)
    (retained : ∀ field value, first.config.store field = some value →
      second.config.store field = some value) :
    second.publicView.openingGuardsAccepted packet =
      first.publicView.openingGuardsAccepted packet := by
  rcases packet with ⟨call, evidence, token⟩
  cases call with
  | commitment _ _ => rfl
  | withhold _ => rfl
  | malformed _ => rfl
  | opening actual candidate raw =>
      cases Option.some.inj named
      unfold PublicView.openingGuardsAccepted
      dsimp only
      cases view : nodeView graph event with
      | bind _ _ _ _ => rfl
      | sample _ _ _ _ => rfl
      | resolve owner payload binding checks outputEq codeEq =>
          dsimp only
          have readsEq : (graph.nodes event).readFields =
              insert binding.field (GuardCheck.listReadFields checks) := by
            calc
              (graph.nodes event).readFields =
                  (cast (congrArg (EventCode graph.layout) outputEq)
                    (graph.nodes event)).readFields :=
                (EventCode.readFields_cast outputEq (graph.nodes event)).symm
              _ = (EventCode.resolve owner payload binding checks).readFields :=
                congrArg EventCode.readFields codeEq
              _ = insert binding.field (GuardCheck.listReadFields checks) := rfl
          have agree : Store.AgreeOn first.config.store second.config.store
              (GuardCheck.listReadFields checks) := by
            intro field member
            have read : field ∈ (graph.nodes event).readFields := by
              rw [readsEq]
              exact Finset.mem_insert_of_mem member
            obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
              (read_available_of_predecessors first.config event settled read)
            rw [stored, retained field value stored]
          change ((raw.as? payload).any fun value => decide
              (GuardCheck.allAccepted? checks (graph.publicStore second.config.store)
                (.success value) = some true)) =
            ((raw.as? payload).any fun value => decide
              (GuardCheck.allAccepted? checks (graph.publicStore first.config.store)
                (.success value) = some true))
          simp only [GuardCheck.allAccepted?_publicStore,
            fun proposal => GuardCheck.allAccepted?_congr checks first.config.store
              second.config.store proposal agree]

end Vegas.EventGraphRuntime
