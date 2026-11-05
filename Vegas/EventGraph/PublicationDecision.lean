/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.WithholdingCoupling

/-! # Opening and withholding at a publication

A publication is produced by a reveal node, whose only actions are opening and
withholding; withholding is the node's failure action, and taking it makes the
active owner default. A kernel that plays opening as a point mass at every one
of its owner's publications therefore opens decisively.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

namespace EventField

/-- A stored value that records a failed publication. -/
def FailedValue : (field : EventField Player L) → field.Value → Prop
  | .publication _, value => value.isFailure = true
  | .publicData _, _ | .binding _ _, _ | .privateInput _ _, _ => False

/-- Opening, the action of a publication that is not its failure. -/
def openAction : (field : EventField Player L) → field.IsPublication → field.Action
  | .publication _, _ => true
  | .publicData _, isPublication | .binding _ _, isPublication
  | .privateInput _ _, isPublication => isPublication.elim

end EventField

namespace EventCode

variable {Field : Type} [DecidableEq Field] {layout : Field → EventField Player L}

omit [DecidableEq Player] in
/-- At a publication, opening is not the failure action, and every other action is. -/
theorem publication_actions {output : EventField Player L} (code : EventCode layout output)
    (publication : output.IsPublication) (owner : Player) (owned : code.actor = some owner) :
    EventField.openAction output publication ≠ code.failureAction owner owned ∧
      ∀ action, action ≠ EventField.openAction output publication →
        action = code.failureAction owner owned := by
  cases code with
  | bind => exact publication.elim
  | sample => exact publication.elim
  | resolve who payload binding checks =>
      refine ⟨by simp [EventField.openAction, failureAction], fun action different => ?_⟩
      change Bool at action
      cases action
      · rfl
      · simp [EventField.openAction] at different

end EventCode

variable {graph : Vegas.EventGraph Player L}

/-- A kernel that opens as a point mass at its owner's active publications opens decisively. -/
theorem opensDecisively_of_opens (who : Player) (honest : graph.BehavioralPolicy who)
    (opens : ∀ (config : graph.Config) (event : graph.EventId)
      (actor : graph.actor? event = some who)
      (publication : (graph.outputLayout event).IsPublication)
      (active : who ∉ config.defaulted),
      honest event actor (graph.playerObserve who config) active =
        PMF.pure (EventField.openAction _ publication)) :
    graph.OpensDecisively who honest := by
  intro config event ready actor publication active
  have owned : (graph.nodes event).actor = some who := actor
  refine ⟨_, opens config event actor publication active, fun action different next member => ?_⟩
  have failure := ((graph.nodes event).publication_actions publication who owned).2 action
    different
  subst failure
  obtain ⟨value, evaluated, defaults⟩ := (graph.nodes event).failureAction_eval? who owned
    config.store (fun _ read => config.read_available ready read)
  have effective : config.effectiveAction event ((graph.nodes event).failureAction who owned) =
      (graph.nodes event).failureAction who owned := by
    unfold Config.effectiveAction EventCode.effectiveAction
    split
    · next owner ownerEq =>
        obtain rfl : owner = who := Option.some.inj (ownerEq.symm.trans owned)
        rw [ite_eq_right active]
    · rfl
  have decision : config.actualDecision event ((graph.nodes event).failureAction who owned) =
      some ((graph.nodes event).failureAction who owned) := by
    unfold Config.actualDecision EventCode.actualDecision
    simp [owned, active]
  rw [Config.step, PMF.support_map] at member
  obtain ⟨output, supported, rfl⟩ := member
  have same : output = value := by
    have law : ((graph.nodes event).eval? (config.effectiveAction event
        ((graph.nodes event).failureAction who owned)) config.store) =
          some (PMF.pure value) := by
      rw [effective, evaluated]
    simp only [law, Option.get_some, PMF.support_pure, Set.mem_singleton_iff] at supported
    exact supported
  subst same
  change who ∈ (config.complete event ready _ output).defaults.defaulted
  rw [Config.complete_defaults, decision]
  simp [EventGraph.completion, EventCode.defaultEvent, defaults, owned]

end Vegas.EventGraph
