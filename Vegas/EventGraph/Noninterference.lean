/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Execution

/-!
# Interim-view value non-interference

`Vegas.Core.Noninterference` proves, at the source level, that another player's
sealed value is invisible to a player's knowledge. This module proves the
event-graph twin at an *intermediate cut*: a value written to a field a player
cannot read does not change that player's graph observation `observe`.

`observe G cfg who` reads the store only at the choice footprint
(`choiceReads`) of `who`'s own ready commit nodes; everything else is sealed.
So completing a node whose output field lies outside every such footprint —
in particular another player's sealed commit — leaves `who`'s observation fixed,
whatever value is written (`observe_completeNode_value_irrel`).

This is the value half of interim-view invariance; the order/occurrence half is
the schedule commutation already recorded as `observe_completeNode_comm`.
Together with `Vegas.EventGraph.Confluence` (outcome confluence) it pins down
that the schedule's freedom and the secrets' content are both inert for a
player's interim view, leaving only that player's own readable data.
-/

namespace Vegas

namespace EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- **Interim-view value non-interference.** If no commit node owned by `who`
reads the field that `node` writes, then completing `node` leaves `who`'s graph
observation independent of the value written. The hypothesis is the visibility
premise: `node`'s output field is outside `who`'s choice footprints — which holds
in particular when `node` is another player's sealed commit.

This is the *private leg* of schedule-conditioning inertness
(**noninterference / observational determinism**): the schedule cannot leak
another player's sealed value, so no schedule a player observes can correlate
with a hidden choice. Confluence (payoff) and a public token (signal) are the
other two legs. -/
theorem observe_completeNode_value_irrel
    (G : Graph Player L) (cfg : Config G) (who : Player)
    {node : Fin G.nodeCount} (v v' : TypedValue L)
    (hsealed :
      ∀ (cnode : Fin G.nodeCount) (guard : EventGuard L),
        G.node? cnode = some (.commit who guard) →
        ∀ ref ∈ guard.choiceReads, ref.field ≠ G.nodeTarget node) :
    observe G (cfg.completeNode node v) who =
      observe G (cfg.completeNode node v') who := by
  apply Observation.ext
  · rfl
  · intro cnode field
    simp only [observe, Config.completeNode, Ready]
    cases hnode : G.node? cnode with
    | none => rfl
    | some body =>
        cases body with
        | sample _ => rfl
        | reveal _ => rfl
        | commit actor guard =>
            by_cases hactor : actor = who
            · by_cases hread :
                  ({ field := (field : Nat), ty := (G.fieldRow field).ty } :
                    FieldRef L) ∈ guard.choiceReads
              · -- the read gate passes, so the value is read; but `hsealed`
                -- forbids reading the field `node` writes, so both stores agree
                have hne : (field : Nat) ≠ G.nodeTarget node :=
                  hsealed cnode guard (hactor ▸ hnode) _ hread
                rw [Store.getAs_set_ne cfg.store hne v ((G.fieldRow field).ty),
                  Store.getAs_set_ne cfg.store hne v' ((G.fieldRow field).ty)]
              · -- the read gate fails on both sides; the differing leaf is unreached
                simp only [dif_neg hread]
            · -- `who` does not own this commit; nothing is read on either side
              simp only [dif_neg hactor]

end EventGraph

end Vegas
