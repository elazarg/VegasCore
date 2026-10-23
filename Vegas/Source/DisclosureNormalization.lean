/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosureAliases

/-! # Normalizing private disclosure intentions

An ineffective disclosure can be replaced by withholding. The owner reconstructs
its original intention before consulting each later source policy. This file
uses the existing source executor; it does not erase strategic history or assert
sequential equilibrium from equality of initialized outcomes.
-/

noncomputable section

namespace Vegas

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Complete an observation only to evaluate owner-local guards. Hidden cells
receive arbitrary defaults; no policy is given those defaults as observations. -/
def SourceObservation.guardState {who : Player} {Γ : SourceCtx Player L}
    (view : SourceObservation L who Γ) : State L Γ := fun _ cell selected =>
  match cell with
  | .publicData _ | .publication _ => view.cells.get selected
  | .commitment _ _ => (view.cells.get selected).getD .failure
  | .privateInput _ payload => (view.cells.get selected).getD (L.someValue payload)

theorem SourceObservation.observe_guardState {who : Player} {Γ : SourceCtx Player L}
    (state : State L Γ) :
    sourceObserve who (sourceObserve who state).guardState = sourceObserve who state := by
  apply sourceObserve_congr
  · intro name payload selected
    rfl
  · intro name payload selected
    rfl
  · intro name payload selected
    simp only [guardState, Env.get, sourceObserve, ↓reduceIte, Option.getD_some]
  · intro name payload selected
    simp only [guardState, Env.get, sourceObserve, ↓reduceIte, Option.getD_some]

namespace SourceProgram

open GameTheory.Math.Probability

variable {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}

/-- Effectiveness is computed from the owner's observation and the static
obligations/publication positions at this instruction. -/
def effectiveDisclosureView (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (registry : Registry Γ) (revelations : Revelations Γ)
    (view : SourceObservation L owner Γ) (disclose : Bool) : Bool :=
  effectiveDisclosure published source ⟨view.guardState, registry, revelations, fun _ => []⟩
    disclose

theorem effectiveDisclosureView_observe (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) :
    effectiveDisclosureView published source config.registry config.revelations
        (sourceObserve owner config.state) disclose =
      effectiveDisclosure published source config disclose := by
  unfold effectiveDisclosureView
  exact effectiveDisclosure_observation_congr published source
    ⟨(sourceObserve owner config.state).guardState, config.registry,
      config.revelations, fun _ => []⟩ config rfl rfl
    (SourceObservation.observe_guardState config.state) disclose

/-- Carry a remembered intention across an unchanged semantic cell. Only the
owner's private action list is reconstructed. -/
def ViewMap.afterPrivateAction {who : Player} (unpatch : ViewMap who Γ)
    (ownStep : Bool) (cellName : VarId) (cell : CellTy Player L)
    (original : DecisionView who Γ → Option (OwnAction Player L)) :
    ViewMap who ((cellName, cell) :: Γ) := fun view =>
  let prior := view.back ownStep
  (view.1, if ownStep then (unpatch prior).2 ++ (original prior).toList else (unpatch prior).2)

variable [IExpr.ResultTypes L]

/-- Normalize a pure source policy while recomputing each of its remembered
intentions from its restored earlier view. Bindings and chance are unchanged. -/
def PurePolicy.normalizeDisclosureFrom {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Registry Γ → Revelations Γ →
    ViewMap who Γ → PurePolicy who program → PurePolicy who program
  | _, _, .ret _, _, _, _, _ => PUnit.unit
  | _, _, .sample (payload := payload) name _ _ next, registry, revelations, unpatch, policy =>
      normalizeDisclosureFrom next registry.weaken revelations.weaken
        (unpatch.afterPrivateAction false name (.publicData payload) (fun _ => none)) policy
  | _, _, .commit (payload := payload) name owner _ guard next,
      registry, revelations, unpatch, policy =>
      let original := fun view => (PurePolicy.commitChoice unpatch owner payload policy.1 view).map
        (OwnAction.commit owner name payload)
      (fun own view => policy.1 own (unpatch view),
        normalizeDisclosureFrom next
          (({ owner := owner, subject := name, payload := payload, source := .here,
              guard := guard.weaken } : Obligation _) :: registry.weaken) revelations.weaken
          (unpatch.afterPrivateAction (decide (owner = who)) name
            (.commitment owner payload) original) policy.2)
  | _, _, .reveal (payload := payload) published owner name _ source _ next,
      registry, revelations, unpatch, policy =>
      let original := fun view => (PurePolicy.revealChoice unpatch owner policy.1 view).map
        (OwnAction.reveal owner name)
      (fun own view => effectiveDisclosureView published source registry revelations
          (own.symm ▸ view.1) (policy.1 own (unpatch view)),
        normalizeDisclosureFrom next registry.weaken
          (revelations.reveal (published := published) source)
          (unpatch.afterPrivateAction (decide (owner = who)) published
            (.publication payload) original) policy.2)

/-- Every supported disclosure is already its effective representative. The
registry and publication positions are carried by the source syntax. -/
def BehavioralPolicy.EffectiveDisclosures {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Registry Γ → Revelations Γ →
    BehavioralPolicy who program → Prop
  | _, _, .ret _, _, _, _ => True
  | _, _, .sample _ _ _ next, registry, revelations, policy =>
      EffectiveDisclosures next registry.weaken revelations.weaken policy
  | _, _, .commit (payload := payload) name owner _ guard next, registry, revelations, policy =>
      EffectiveDisclosures next
        ({ owner := owner, subject := name, payload := payload, source := .here,
            guard := guard.weaken } :: registry.weaken) revelations.weaken policy.2
  | _, _, .reveal published _ _ _ selected _ next, registry, revelations, policy =>
      (∀ own view disclose, disclose ∈ (policy.1 own view).support →
        effectiveDisclosureView published selected registry revelations
          (own.symm ▸ view.1) disclose = disclose) ∧
      EffectiveDisclosures next registry.weaken
        (revelations.reveal (published := published) selected) policy.2

theorem normalizeDisclosureFrom_effective {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (registry : Registry Γ) → (revelations : Revelations Γ) →
    (unpatch : ViewMap who Γ) → (policy : PurePolicy who program) →
    BehavioralPolicy.EffectiveDisclosures program registry revelations
      ((policy.normalizeDisclosureFrom program registry revelations unpatch).toBehavioral program)
  | _, _, .ret _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, registry, revelations, unpatch, policy =>
      normalizeDisclosureFrom_effective next _ _ _ policy
  | _, _, .commit _ _ _ _ next, registry, revelations, unpatch, policy =>
      normalizeDisclosureFrom_effective next _ _ _ policy.2
  | _, _, .reveal published _ _ _ selected _ next, registry, revelations, unpatch, policy => by
      refine ⟨?_, normalizeDisclosureFrom_effective next _ _ _ policy.2⟩
      intro own view disclose supported
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp supported
      exact effectiveDisclosure_idempotent published selected _ _

end SourceProgram
end Vegas
