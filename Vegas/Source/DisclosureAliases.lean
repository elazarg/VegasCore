/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.PublicObservation

/-! # Ineffective disclosure choices are private action aliases

A rejected disclosure and withholding have the same typed cells, obligations,
and publication status. Only the owner's action history differs. Whether a
disclosure would be effective is determined by that owner's observation and
the registry and publication status fixed at the program point.

These are operational facts about the source executor. They do not
assert that an arbitrary strategy can discard its private action history.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
  {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}

/-- The reveal's publication, including default control and deferred guard checks. -/
def disclosureResult (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) : PublicationResult (L.Val payload) :=
  (revealSuccessor published source config disclose).state.get .here

@[simp] theorem disclosureResult_false (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ) :
    disclosureResult published source config false = .failure := by
  simp [disclosureResult, revealSuccessor]

/-- Guard rejection is observable before choosing, without reading any other
player's unpublished binding or private input. -/
theorem disclosureResult_observation_congr (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (left right : Config Player L Γ)
    (registry : left.registry = right.registry)
    (revelations : @left.revelations = @right.revelations)
    (sameView : left.view owner = right.view owner)
    (disclose : Bool) :
    disclosureResult published source left disclose =
      disclosureResult published source right disclose := by
  have observed := congrArg DecisionView.observation sameView
  have defaults := congrArg DecisionView.defaulted sameView
  change left.defaulted = right.defaulted at defaults
  have own : left.state.get source = right.state.get source := by
    have same := congrArg (fun view => view.cells.get source) observed
    change (if owner = owner then some (left.state.get source) else none) =
      (if owner = owner then some (right.state.get source) else none) at same
    simpa only [ite_true, Option.some.injEq] using same
  have publicEq {x τ} (cell : HasVar Γ x (.publicData τ)) :
      left.state.get cell = right.state.get cell :=
    congrArg (fun view => view.cells.get cell) observed
  have publicationEq {x τ} (cell : HasVar Γ x (.publication τ)) :
      left.state.get cell = right.state.get cell :=
    congrArg (fun view => view.cells.get cell) observed
  have accepted (proposal : PublicationResult (L.Val payload)) :
      (right.registry.completedBy (published := published) right.revelations source).all
          (·.accepts (Revelations.reveal (published := published) right.revelations source)
            (Env.cons (Val := CellVal (Player := Player) L) (x := published)
              (τ := .publication payload) proposal left.state)) =
        (right.registry.completedBy (published := published) right.revelations source).all
          (·.accepts (Revelations.reveal (published := published) right.revelations source)
            (Env.cons (Val := CellVal (Player := Player) L) (x := published)
              (τ := .publication payload) proposal right.state)) := by
    refine congrArg (List.all _) (funext fun obligation => ?_)
    exact Obligation.accepts_congr obligation _ _ _
      (fun cell => match cell with | .there prior => publicEq prior)
      (fun cell => match cell with
        | .here => rfl
        | .there prior => publicationEq prior)
  simp only [disclosureResult, revealSuccessor, Env.cons_get_here, registry, revelations, own,
    defaults]
  rw [accepted]

/-- The canonical Boolean choice suppresses an ineffective request to reveal. -/
def effectiveDisclosure (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) : Bool :=
  match disclosureResult published source config disclose with
  | .failure => false
  | .success _ => true

@[simp] theorem effectiveDisclosure_false (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ) :
    effectiveDisclosure published source config false = false := by
  rw [effectiveDisclosure, disclosureResult_false]

theorem effectiveDisclosure_observation_congr (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (left right : Config Player L Γ)
    (registry : left.registry = right.registry)
    (revelations : @left.revelations = @right.revelations)
    (observed : left.view owner = right.view owner)
    (disclose : Bool) :
    effectiveDisclosure published source left disclose =
      effectiveDisclosure published source right disclose := by
  unfold effectiveDisclosure
  rw [disclosureResult_observation_congr published source left right registry revelations
    observed disclose]

theorem disclosureResult_effectiveDisclosure (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) :
    disclosureResult published source config
        (effectiveDisclosure published source config disclose) =
      disclosureResult published source config disclose := by
  cases disclose with
  | false => rw [effectiveDisclosure_false]
  | true =>
    cases result : disclosureResult published source config true with
    | failure => simp only [effectiveDisclosure, result, disclosureResult_false]
    | success value => simp only [effectiveDisclosure, result]

theorem effectiveDisclosure_idempotent (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) :
    effectiveDisclosure published source config
        (effectiveDisclosure published source config disclose) =
      effectiveDisclosure published source config disclose := by
  exact congrArg (fun result : PublicationResult (L.Val payload) =>
      match result with | .failure => false | .success _ => true)
    (disclosureResult_effectiveDisclosure published source config disclose)

end Vegas.SourceProgram
