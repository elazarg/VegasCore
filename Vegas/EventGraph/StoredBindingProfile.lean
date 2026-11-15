module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.BindingSubmission
public import Vegas.EventGraph.PolicyPatch

@[expose] public section

/-! # Freezing binding policies at stored prefix results

A stored configuration fixes earlier binding kernels while leaving the current
source head and every other event unchanged. One supported head completion
extends this frozen prefix by one ordinary policy patch.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

namespace EventField

variable {Player : Type} {L : IExpr}

/-- Freeze a binding at its stored result, with an accepted failure for a missing output.
Other node laws are unchanged. -/
def storedBindingLaw : (field : EventField Player L) → Option field.Value →
    PMF field.Action → PMF field.Action
  | .binding _ _, stored, _ => PMF.pure (some (stored.getD .failure))
  | .publicData _, _, original | .privateInput _ _, _, original
  | .publication _, _, original => original

@[simp] theorem storedBindingLaw_binding (owner : Player) (payload : L.Ty)
    (stored : Option (PublicationResult (L.Val payload)))
    (original : PMF (Option (PublicationResult (L.Val payload)))) :
    storedBindingLaw (.binding owner payload) stored original =
      PMF.pure (some (stored.getD .failure)) := rfl

/-- Frozen binding laws always submit, including the off-support missing-output branch. -/
theorem storedBindingLaw_submits (field : EventField Player L) (stored : Option field.Value)
    (original : PMF field.Action) (action : field.Action)
    (supported : action ∈ (field.storedBindingLaw stored original).support) :
    field.Submitted action := by
  cases field with
  | binding owner payload =>
      rw [storedBindingLaw, PMF.mem_support_pure_iff] at supported
      subst action
      rfl
  | publicData | privateInput | publication => trivial

/-- An available binding output freezes the prescribed submitted result exactly. -/
theorem storedBindingLaw_eq_pure_of_binding {field : EventField Player L}
    {owner : Player} {payload : L.Ty} (binding : field = .binding owner payload)
    (stored : Option field.Value) (original : PMF field.Action)
    (value : PublicationResult (L.Val payload))
    (filled : cast (congrArg (fun field => Option field.Value) binding) stored = some value) :
    field.storedBindingLaw stored original =
      PMF.pure (cast (congrArg Action binding.symm) (some value)) := by
  cases binding
  change stored = some value at filled
  rw [filled]
  rfl

end EventField

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable (graph : Vegas.EventGraph Player L)

/-- Freeze precisely the earlier bindings in one source interval using existing outputs. -/
def freezeBindingsBefore (profile : graph.BehavioralProfile) (start rank : Nat)
    (ghost : graph.Config) : graph.BehavioralProfile :=
  fun who event actor observation active =>
    if start ≤ event.val ∧ event.val < rank then
      (graph.outputLayout event).storedBindingLaw (ghost.outputs event)
        (profile who event actor observation active)
    else profile who event actor observation active

variable {graph}

theorem SubmitsBindings.freezeBindingsBefore {profile : graph.BehavioralProfile}
    (submits : graph.SubmitsBindings profile) (start rank : Nat) (ghost : graph.Config) :
    graph.SubmitsBindings (graph.freezeBindingsBefore profile start rank ghost) := by
  intro who event actor observation active action supported
  unfold Vegas.EventGraph.freezeBindingsBefore at supported
  split at supported
  · exact EventField.storedBindingLaw_submits _ _ _ action supported
  · exact submits who event actor observation active action supported

/-- The current source head retains its original kernel until it is added to the prefix. -/
theorem freezeBindingsBefore_at_rank (profile : graph.BehavioralProfile) (start rank : Nat)
    (ghost : graph.Config) (who : Player) (event : graph.EventId)
    (actor : graph.actor? event = some who) (observation : graph.PlayerObservation who)
    (active : who ∉ observation.defaulted) (atRank : event.val = rank) :
    graph.freezeBindingsBefore profile start rank ghost who event actor observation active =
      profile who event actor observation active := by
  simp only [freezeBindingsBefore, atRank, lt_self_iff_false, and_false, ite_false]

@[simp] theorem freezeBindingsBefore_at_start (profile : graph.BehavioralProfile) (start : Nat)
    (ghost : graph.Config) : graph.freezeBindingsBefore profile start start ghost = profile := by
  funext who event actor observation active
  have outside : ¬ (start ≤ event.val ∧ event.val < start) := by omega
  simp only [freezeBindingsBefore, ite_eq_right outside]

/-- A filled binding in the frozen interval prescribes its recorded result at every view. -/
theorem freezeBindingsBefore_binding (profile : graph.BehavioralProfile) (start rank : Nat)
    (ghost : graph.Config) (who : Player) (event : graph.EventId)
    (actor : graph.actor? event = some who) (observation : graph.PlayerObservation who)
    (active : who ∉ observation.defaulted) (inside : start ≤ event.val ∧ event.val < rank)
    {owner : Player} {payload : L.Ty}
    (binding : graph.outputLayout event = .binding owner payload)
    (value : PublicationResult (L.Val payload))
    (filled : cast (congrArg (fun field => Option field.Value) binding) (ghost.outputs event) =
      some value) :
    graph.freezeBindingsBefore profile start rank ghost who event actor observation active =
      PMF.pure (cast (congrArg EventField.Action binding.symm) (some value)) := by
  rw [freezeBindingsBefore, ite_eq_left inside]
  exact EventField.storedBindingLaw_eq_pure_of_binding binding _ _ value filled

private theorem freezeBindingsBefore_step_other
    (profile : graph.BehavioralProfile) (start : Nat) (before after : graph.Config)
    (event : graph.EventId) (ready : before.cut.Ready event) (action : graph.Action event)
    (supported : after ∈ (before.step event ready action).support)
    (who : Player) (current : graph.EventId) (actor : graph.actor? current = some who)
    (observation : graph.PlayerObservation who) (active : who ∉ observation.defaulted)
    (different : current ≠ event) :
    graph.freezeBindingsBefore profile start (event.val + 1) after
        who current actor observation active =
      graph.freezeBindingsBefore profile start event.val before
        who current actor observation active := by
  have differentValues : current.val ≠ event.val := fun same => different (Fin.ext same)
  have window : (start ≤ current.val ∧ current.val < event.val + 1) ↔
      (start ≤ current.val ∧ current.val < event.val) := by omega
  have outputs : after.outputs current = before.outputs current := by
    obtain ⟨value, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact before.complete_output_of_ne event current ready action value different
  simp only [freezeBindingsBefore, window, outputs]

/-- One supported head completion extends the frozen prefix by exactly one owned policy patch. -/
theorem freezeBindingsBefore_step_patch
    (profile : graph.BehavioralProfile) (start : Nat) (before after : graph.Config)
    (event : graph.EventId) (ready : before.cut.Ready event) (action : graph.Action event)
    (supported : after ∈ (before.step event ready action).support)
    (owner : Player) (owned : graph.actor? event = some owner) :
    Function.update (graph.freezeBindingsBefore profile start event.val before) owner
      (patchPolicy event
        (graph.freezeBindingsBefore profile start (event.val + 1) after owner)
        (graph.freezeBindingsBefore profile start event.val before owner)) =
      graph.freezeBindingsBefore profile start (event.val + 1) after := by
  funext who current actor observation active
  by_cases sameOwner : who = owner
  · subst who
    rw [Function.update_self]
    by_cases sameEvent : current = event
    · simp only [patchPolicy, sameEvent, ite_true]
    · rw [patchPolicy, ite_eq_right sameEvent]
      exact (freezeBindingsBefore_step_other profile start before after event ready action
        supported owner current actor observation active sameEvent).symm
  · rw [Function.update_of_ne sameOwner]
    by_cases sameEvent : current = event
    · subst current
      have same : owner = who := Option.some.inj (owned.symm.trans actor)
      exact (sameOwner same.symm).elim
    · exact (freezeBindingsBefore_step_other profile start before after event ready action
        supported who current actor observation active sameEvent).symm

end Vegas.EventGraph
