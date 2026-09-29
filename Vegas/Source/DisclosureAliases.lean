/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ObservationRecall
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Support

/-! # Ineffective disclosure choices are private action aliases

A rejected disclosure and withholding have the same typed cells, obligations,
and publication status. Only the owner's action history differs. Whether a
disclosure would be effective is determined by that owner's observation and
the registry and publication status fixed at the program point.

These are operational facts about the existing source executor. They do not
assert that an arbitrary strategy can discard its private action history.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
  {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}

/-- The existing reveal's publication, including the deferred guard checks. -/
def disclosureResult (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) : PublicationResult (L.Val payload) :=
  (revealSuccessor published source config disclose).state.get .here

@[simp] theorem disclosureResult_false (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ) :
    disclosureResult published source config false = .failure := by
  simp only [disclosureResult, revealSuccessor, Bool.false_eq_true, ite_false, ite_self,
    Env.cons_get_here]

/-- Guard rejection is observable before choosing, without reading any other
player's unpublished binding or private input. -/
theorem disclosureResult_observation_congr (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (left right : Config Player L Γ)
    (registry : left.registry = right.registry)
    (revelations : @left.revelations = @right.revelations)
    (observed : sourceObserve owner left.state = sourceObserve owner right.state)
    (disclose : Bool) :
    disclosureResult published source left disclose =
      disclosureResult published source right disclose := by
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
  simp only [disclosureResult, revealSuccessor, Env.cons_get_here, registry, revelations, own]
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
    (observed : sourceObserve owner left.state = sourceObserve owner right.state)
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

/-- All semantic state is preserved; private own-action recall is considered
separately rather than included in this equality. -/
theorem revealSuccessor_effective_state (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) :
    (revealSuccessor published source config
        (effectiveDisclosure published source config disclose)).state =
      (revealSuccessor published source config disclose).state := by
  change Env.cons (Val := CellVal (Player := Player) L) (x := published)
      (τ := .publication payload)
      (disclosureResult published source config
        (effectiveDisclosure published source config disclose)) config.state =
    Env.cons (disclosureResult published source config disclose) config.state
  rw [disclosureResult_effectiveDisclosure]

theorem revealSuccessor_effective_other_view (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) (who : Player) (other : who ≠ owner) :
    (revealSuccessor published source config
        (effectiveDisclosure published source config disclose)).view who =
      (revealSuccessor published source config disclose).view who := by
  apply Prod.ext
  · exact congrArg (sourceObserve who)
      (revealSuccessor_effective_state published source config disclose)
  · simp only [Config.view, revealSuccessor, Function.update_of_ne other]

/-- Restore a just-completed private disclosure intention. This changes no
cell, obligation or publication, and uses no opponent's observation. -/
def Config.restoreDisclosure {context : SourceCtx Player L}
    (config : Config Player L context) (owner : Player) (name : VarId) (disclose : Bool) :
    Config Player L context :=
  { config with history := (Function.update config.history owner
      ((config.history owner).dropLast ++ [.reveal owner name disclose])) }

theorem revealSuccessor_restore_effective (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) :
    (revealSuccessor published source config
        (effectiveDisclosure published source config disclose)).restoreDisclosure
          owner name disclose =
      revealSuccessor published source config disclose := by
  have states := revealSuccessor_effective_state published source config disclose
  apply congrArg₂ (fun state history =>
    (⟨state, Registry.weaken config.registry,
      Revelations.reveal (published := published) config.revelations source, history⟩ :
        Config Player L ((published, .publication payload) :: Γ))) states
  funext who
  by_cases same : who = owner
  · subst who
    simp only [revealSuccessor, Function.update_self,
      List.dropLast_concat]
  · simp only [revealSuccessor, Function.update_of_ne same]

/-- A source reveal can be realized by its effective response and a posterior
over private intentions. The equality retains the entire original successor
configuration, including the intention used by every later source policy. -/
theorem disclosure_alias_disintegration (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (law : PMF Bool) :
    law.map (revealSuccessor published source config) =
      (law.map (effectiveDisclosure published source config)).bind fun response =>
        (fiberConditional law (effectiveDisclosure published source config) response).map
          (fun intention => (revealSuccessor published source config response).restoreDisclosure
            owner name intention) := by
  classical
  conv_lhs => arg 2; rw [eq_bind_fiberConditional law (effectiveDisclosure published source config)]
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro response reached
  obtain ⟨original, supported, responseEq⟩ := PMF.support_map .. ▸ reached
  have meets : ∃ intention ∈ (effectiveDisclosure published source config) ⁻¹' {response},
      intention ∈ law.support := ⟨original, responseEq, supported⟩
  apply map_congr_on_support _
  intro intention compatible
  rw [fiberConditional, dite_eq_left meets] at compatible
  have projects : effectiveDisclosure published source config intention = response :=
    ((PMF.mem_support_filter_iff _).mp compatible).1
  rw [← projects, revealSuccessor_restore_effective]

/-- A fully mixed intention law gives positive mass to every effective choice.
The removed choices are exact private aliases, not zero-probability moves left
in the effective menu. -/
theorem effectiveDisclosure_support (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (law : PMF Bool) (mixed : FullSupport law) :
    (law.map (effectiveDisclosure published source config)).support =
      Set.range (effectiveDisclosure published source config) := by
  ext response
  rw [PMF.support_map]
  constructor
  · rintro ⟨intention, _supported, rfl⟩
    exact ⟨intention, rfl⟩
  · rintro ⟨intention, rfl⟩
    exact ⟨intention, mixed intention, rfl⟩

end Vegas.SourceProgram
