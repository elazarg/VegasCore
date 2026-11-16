module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.SchedulerErasure
public import Vegas.EventGraph.PolicyCongruence

@[expose] public section

/-! # Patching one event of a policy

A policy patched at one event follows a head policy at that event and a tail
policy elsewhere. Once that event has completed, every run from the
configuration is the tail policy's run: a profile matters only at the events
still to be decided.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Follow `head` at `event` and `tail` at every other event. -/
def patchPolicy {who : Player} (event : graph.EventId) (head tail : graph.BehavioralPolicy who) :
    graph.BehavioralPolicy who :=
  fun current actor observation active =>
    if current = event then head current actor observation active
    else tail current actor observation active

/-- Away from the patched event, the patched deviation has the tail's action
laws. -/
theorem actionLaw_update_patch_of_ne (profile : graph.BehavioralProfile) (who : Player)
    (event : graph.EventId) (head tail : graph.BehavioralPolicy who) (config : graph.Config)
    {other : graph.EventId} (different : other ≠ event) :
    actionLaw (Function.update profile who (patchPolicy event head tail)) config other =
      actionLaw (Function.update profile who tail) config other := by
  cases ownerEq : (graph.nodes other).actor with
  | none => rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
  | some owner =>
      rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
      by_cases inactive : owner ∈ config.defaulted
      · rw [dite_eq_left inactive, dite_eq_left inactive]
      · rw [dite_eq_right inactive, dite_eq_right inactive]
        by_cases same : owner = who
        · subst owner
          simp only [Function.update_self, patchPolicy, different, ↓reduceIte]
        · simp only [Function.update_of_ne same]

/-- At the patched event, the patched deviation has the head's action law. -/
theorem actionLaw_update_patch_self (profile : graph.BehavioralProfile) (who : Player)
    (event : graph.EventId) (head tail : graph.BehavioralPolicy who) (config : graph.Config) :
    actionLaw (Function.update profile who (patchPolicy event head tail)) config event =
      actionLaw (Function.update profile who head) config event := by
  cases ownerEq : (graph.nodes event).actor with
  | none => rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
  | some owner =>
      rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
      by_cases inactive : owner ∈ config.defaulted
      · rw [dite_eq_left inactive, dite_eq_left inactive]
      · rw [dite_eq_right inactive, dite_eq_right inactive]
        by_cases same : owner = who
        · subst owner
          simp only [Function.update_self, patchPolicy, ↓reduceIte]
        · simp only [Function.update_of_ne same]

/-- **Only undecided events matter.** Two profiles with the same action laws at
every event outside a set of completed events have the same runs. -/
theorem runPlan_congr_of_actionLaw (scheduler : graph.PublicScheduler)
    {left right : graph.BehavioralProfile} (decided : graph.EventId → Prop)
    (agree : ∀ config event, ¬ decided event →
      actionLaw left config event = actionLaw right config event) :
    ∀ fuel (config : graph.Config), (∀ event, decided event → event ∈ config.cut.completed) →
      graph.runPlan (graph.policyPlan left scheduler) fuel config =
        graph.runPlan (graph.policyPlan right scheduler) fuel config := by
  intro fuel
  induction fuel with
  | zero => intro config _; rfl
  | succ fuel ih =>
      intro config completed
      by_cases terminal : config.cut.Terminal
      · simp only [EventGraph.runPlan, dite_eq_left terminal]
      · rw [runPlan_policyPlan_succ left scheduler fuel config terminal,
          runPlan_policyPlan_succ right scheduler fuel config terminal]
        apply bind_congr_on_support _
        intro selected _
        have ready := (EventOrder.Cut.mem_enabled _ _).mp selected.2
        have undecided : ¬ decided selected.1 := fun done => ready.1 (completed _ done)
        unfold eventStep
        rw [agree config selected.1 undecided, PMF.bind_bind, PMF.bind_bind]
        apply bind_congr_on_support _
        intro action _
        apply bind_congr_on_support _
        intro next member
        apply ih next
        intro event done
        rw [config.step_cut selected.1 ready action next member, EventOrder.Cut.mem_complete]
        exact Or.inr (completed event done)

/-- One policy realizes a canonical head window followed by one common tail policy. -/
theorem exists_canonical_policy_splice
    (reference : graph.BehavioralProfile) (focal : Player)
    (head tail : graph.BehavioralPolicy focal) (start headCount tailCount : Nat)
    (bounded : start + headCount ≤ graph.order.eventCount) :
    ∃ policy : graph.BehavioralPolicy focal, ∀ origin : graph.Config,
      origin.cut.IsPrefix start →
      graph.runPlan (graph.policyPlan (Function.update reference focal policy)
        graph.canonicalScheduler) (headCount + tailCount) origin =
        (graph.runPlan (graph.policyPlan (Function.update reference focal head)
          graph.canonicalScheduler) headCount origin).bind
          (graph.runPlan (graph.policyPlan (Function.update reference focal tail)
            graph.canonicalScheduler) tailCount) := by
  classical
  let policy : graph.BehavioralPolicy focal := fun event actor observation active =>
    if event.val < start + headCount then head event actor observation active
    else tail event actor observation active
  let full := Function.update reference focal policy
  let initial := Function.update reference focal head
  let final := Function.update reference focal tail
  have outside (config : graph.Config) (event : graph.EventId)
      (later : ¬ event.val < start + headCount) :
      actionLaw full config event = actionLaw final config event := by
    cases owned : (graph.nodes event).actor with
    | none => rw [actionLaw_of_ownerless _ _ owned, actionLaw_of_ownerless _ _ owned]
    | some owner =>
        rw [actionLaw_of_actor _ _ owned, actionLaw_of_actor _ _ owned]
        by_cases inactive : owner ∈ config.defaulted
        · rw [dite_eq_left inactive, dite_eq_left inactive]
        · rw [dite_eq_right inactive, dite_eq_right inactive]
          by_cases same : owner = focal
          · subst owner
            simp only [full, final, Function.update_self, policy, ite_eq_right later]
          · simp only [full, final, Function.update_of_ne same]
  refine ⟨policy, ?_⟩
  intro origin ordered
  have headEq : graph.runPlan (graph.policyPlan full graph.canonicalScheduler) headCount origin =
      graph.runPlan (graph.policyPlan initial graph.canonicalScheduler) headCount origin := by
    apply runPlan_canonical_prefix_congr _ _ headCount start origin ordered bounded
    intro event _lower upper owner actor observation active
    by_cases same : owner = focal
    · subst owner
      simp only [full, initial, Function.update_self, policy, ite_eq_left upper]
    · simp only [full, initial, Function.update_of_ne same]
  change graph.runPlan (graph.policyPlan full graph.canonicalScheduler)
    (headCount + tailCount) origin = _
  rw [graph.runPlan_add _ headCount tailCount origin, headEq]
  apply bind_congr_on_support _
  intro next reached
  apply runPlan_congr_of_actionLaw graph.canonicalScheduler
    (fun event => event.val < start + headCount) outside tailCount next
  intro event earlier
  exact ((runPlan_canonical_isPrefix initial headCount start origin ordered bounded next
    reached).2 event).mpr earlier

end Vegas.EventGraph
