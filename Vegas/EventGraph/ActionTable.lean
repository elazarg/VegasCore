module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.PrefixRestriction
public import Vegas.EventGraph.OwnedStep
public import Vegas.EventGraph.CanonicalStep

@[expose] public section

/-! # Deterministic prefix runs from event-action tables -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Read a supplied event-action table at every owned callback. -/
def actionTableProfile (table : (event : graph.EventId) → graph.Action event) :
    graph.BehavioralProfile := fun _ event _ _ _ => PMF.pure (table event)

/-- Fixed actions on an interval of owned events give a deterministic canonical fill.
Every shorter fill is the exact source-prefix restriction of the full fill. -/
theorem runPlan_actionTable_prefix
    (table : (event : graph.EventId) → graph.Action event) :
    ∀ count start (config : graph.Config),
      config.cut.IsPrefix start → start + count ≤ graph.order.eventCount →
      (∀ event : graph.EventId, start ≤ event.val → event.val < start + count →
        ∃ owner, graph.actor? event = some owner) →
      ∃ final,
        graph.runPlan (graph.policyPlan (actionTableProfile table) graph.canonicalScheduler)
          count config = PMF.pure final ∧
        final.cut.IsPrefix (start + count) ∧
        Relation.ReflTransGen Config.Step config final ∧
        ∀ smaller, smaller ≤ count → ∃ prefixConfig,
          graph.runPlan (graph.policyPlan (actionTableProfile table) graph.canonicalScheduler)
              smaller config = PMF.pure prefixConfig ∧
            prefixConfig.RestrictionOf (fun event => event.val < start + smaller) final := by
  intro count
  induction count with
  | zero =>
      intro start config ordered _bounded _owned
      refine ⟨config, rfl, ?_, .refl, ?_⟩
      · simpa only [Nat.add_zero] using ordered
      · intro smaller below
        have same : smaller = 0 := Nat.eq_zero_of_le_zero below
        subst smaller
        exact ⟨config, rfl, by simpa only [Nat.add_zero] using
          (Config.restrictionOf_path ordered Relation.ReflTransGen.refl)⟩
  | succ count ih =>
      intro start config ordered bounded owned
      have inside : start < graph.order.eventCount := by omega
      let event : graph.EventId := ⟨start, inside⟩
      have ready : config.cut.Ready event := ordered.ready inside
      have least (other : graph.EventId) (otherReady : config.cut.Ready other) : event ≤ other := by
        apply Fin.le_iff_val_le_val.mpr
        change start ≤ other.val
        by_contra earlier
        exact otherReady.1 ((ordered.2 other).mpr (by omega))
      obtain ⟨owner, actor⟩ := owned event (by rfl) (by dsimp only [event]; omega)
      have pureAction : ∃ action,
          actionLaw (actionTableProfile table) config event = PMF.pure action := by
        rw [actionLaw_of_actor _ _ actor]
        split
        · exact ⟨_, rfl⟩
        · exact ⟨table event, rfl⟩
      obtain ⟨action, actionEq⟩ := pureAction
      obtain ⟨next, stepEq⟩ := config.step_eq_pure_of_actor event ready action owner actor
      have moved : next ∈ (config.step event ready action).support := by
        rw [stepEq]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
      have first (fuel : Nat) :
          graph.runPlan (graph.policyPlan (actionTableProfile table) graph.canonicalScheduler)
              (fuel + 1) config =
            graph.runPlan (graph.policyPlan (actionTableProfile table) graph.canonicalScheduler)
              fuel next := by
        rw [runPlan_canonical_succ _ _ _ ready.not_terminal event ready least,
          eventStep, actionEq, PMF.pure_bind, stepEq, PMF.pure_bind]
      have nextPrefix : next.cut.IsPrefix (start + 1) := by
        rw [config.step_cut event ready action next moved]
        exact ordered.complete inside
      have nextBound : start + 1 + count ≤ graph.order.eventCount := by omega
      have nextOwned (other : graph.EventId) (lower : start + 1 ≤ other.val)
          (upper : other.val < start + 1 + count) : ∃ actor, graph.actor? other = some actor :=
        owned other (by omega) (by omega)
      obtain ⟨final, law, prefixConfig, path, prefixes⟩ :=
        ih (start + 1) next nextPrefix nextBound nextOwned
      have wholePath : Relation.ReflTransGen Config.Step config final :=
        (Relation.ReflTransGen.single ⟨event, ready, action, moved⟩).trans path
      refine ⟨final, (first count).trans law, ?_, wholePath, ?_⟩
      · simpa only [Nat.add_assoc, Nat.add_comm 1 count] using prefixConfig
      · intro smaller below
        cases smaller with
        | zero =>
            exact ⟨config, rfl, by simpa only [Nat.add_zero] using
              (Config.restrictionOf_path ordered wholePath)⟩
        | succ smaller =>
            obtain ⟨middle, middleLaw, restricted⟩ := prefixes smaller (by omega)
            refine ⟨middle, (first smaller).trans middleLaw, ?_⟩
            simpa only [Nat.add_assoc, Nat.add_comm 1 smaller] using restricted

end Vegas.EventGraph
