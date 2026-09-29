/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosureAliases
import Vegas.Source.Purification

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

theorem afterPrivateAction_view {who : Player} (unpatch : ViewMap who Γ)
    (cellName : VarId) (cell : CellTy Player L) (head : CellVal L cell)
    (state : State L Γ) (originalHistory actualHistory : List (OwnAction Player L))
    (restored : unpatch (sourceObserve who state, actualHistory) =
      (sourceObserve who state, originalHistory))
    (original actual : OwnAction Player L)
    (choose : DecisionView who Γ → Option (OwnAction Player L))
    (chosen : choose (sourceObserve who state, actualHistory) = some original) :
    unpatch.afterPrivateAction true cellName cell choose
        (sourceObserve who (Env.cons head state), actualHistory ++ [actual]) =
      (sourceObserve who (Env.cons head state), originalHistory ++ [original]) := by
  simp only [ViewMap.afterPrivateAction, back_sourceObserve, ite_true,
    List.dropLast_concat, restored, chosen, Option.toList_some]

theorem afterPrivateAction_foreign_view {who : Player} (unpatch : ViewMap who Γ)
    (cellName : VarId) (cell : CellTy Player L) (head : CellVal L cell)
    (state : State L Γ) (originalHistory actualHistory : List (OwnAction Player L))
    (restored : unpatch (sourceObserve who state, actualHistory) =
      (sourceObserve who state, originalHistory))
    (choose : DecisionView who Γ → Option (OwnAction Player L)) :
    unpatch.afterPrivateAction false cellName cell choose
        (sourceObserve who (Env.cons head state), actualHistory) =
      (sourceObserve who (Env.cons head state), originalHistory) := by
  simp only [ViewMap.afterPrivateAction, back_sourceObserve, Bool.false_eq_true, ite_false,
    restored]

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

/-- One translated pure policy works against every opponent profile and from
every configuration. The complete typed terminal state, including all initial
private types, is unchanged. Only its own private action recall is reconstructed. -/
theorem normalizeDisclosureFrom_runWith {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (registry : Registry Γ) → (revelations : Revelations Γ) →
    (unpatch : ViewMap who Γ) → (policy : PurePolicy who program) →
    (profile normalized : BehavioralProfile program) →
    (∀ other, other ≠ who → normalized other = profile other) →
    profile who = policy.toBehavioral program →
    normalized who =
      (policy.normalizeDisclosureFrom program registry revelations unpatch).toBehavioral program →
    (state : State L Γ) → (history actualHistory : History Player L) →
    (∀ other, other ≠ who → actualHistory other = history other) →
    unpatch (sourceObserve who state, actualHistory who) =
      (sourceObserve who state, history who) →
    runWith program normalized state registry revelations actualHistory =
      runWith program profile state registry revelations history
  | _, _, .ret _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, _, .sample (payload := payload) name fresh law next, registry, revelations,
      unpatch, policy, profile, normalized, others, prescribed, compiled,
      state, history, actualHistory, histories, restored => by
      simp only [runWith]
      apply bind_congr_on_support _
      intro value _
      exact normalizeDisclosureFrom_runWith next registry.weaken revelations.weaken
        _ policy _ _ others prescribed compiled _ _ _ histories
        (afterPrivateAction_foreign_view unpatch name (.publicData payload) value state
          (history who) (actualHistory who) restored _)
  | _, _, .commit (payload := payload) name owner fresh guard next, registry, revelations,
      unpatch, policy, profile, normalized, others, prescribed, compiled,
      state, history, actualHistory, histories, restored => by
      simp only [runWith]
      by_cases owned : owner = who
      · subst who
        have left : commitKernel normalized (sourceObserve owner state, actualHistory owner) =
            PMF.pure (policy.1 rfl (sourceObserve owner state, history owner)) := by
          rw [commitKernel, compiled]
          simp only [PurePolicy.toBehavioral, PurePolicy.normalizeDisclosureFrom, restored]
        have right : commitKernel profile (sourceObserve owner state, history owner) =
            PMF.pure (policy.1 rfl (sourceObserve owner state, history owner)) := by
          rw [commitKernel, prescribed]
          rfl
        rw [left, right, PMF.pure_bind, PMF.pure_bind]
        apply normalizeDisclosureFrom_runWith next _ _ _ policy.2
          (afterCommit profile) (afterCommit normalized)
          (fun other different => congrArg Prod.snd (others other different))
          (congrArg Prod.snd prescribed) (congrArg Prod.snd compiled)
        · intro other different
          simp only [Function.update_of_ne different, histories other different]
        · simp only [decide_true, Function.update_self]
          apply afterPrivateAction_view _ name (.commitment owner payload) _ state
            (history owner) (actualHistory owner) restored
          simp only [PurePolicy.commitChoice, dite_true, restored, Option.map_some]
      · have kernel : commitKernel normalized (sourceObserve owner state, actualHistory owner) =
            commitKernel profile (sourceObserve owner state, history owner) := by
          rw [commitKernel, others owner owned, histories owner owned]
          rfl
        rw [kernel]
        apply bind_congr_on_support _
        intro value _
        apply normalizeDisclosureFrom_runWith next _ _ _ policy.2
          (afterCommit profile) (afterCommit normalized)
          (fun other different => congrArg Prod.snd (others other different))
          (congrArg Prod.snd prescribed) (congrArg Prod.snd compiled)
        · intro other different
          by_cases same : other = owner
          · subst other
            simp only [Function.update_self, histories owner owned]
          · simp only [Function.update_of_ne same, histories other different]
        · simp only [show decide (owner = who) = false by simp [owned],
            Function.update_of_ne (Ne.symm owned)]
          exact afterPrivateAction_foreign_view unpatch name (.commitment owner payload) value
            state (history who) (actualHistory who) restored _
  | _, _, .reveal (payload := payload) published owner name fresh selected unresolved next,
      registry, revelations, unpatch, policy, profile, normalized, others, prescribed, compiled,
      state, history, actualHistory, histories, restored => by
      simp only [runWith]
      by_cases owned : owner = who
      · subst who
        let config : Config Player L _ := ⟨state, registry, revelations, history⟩
        let intended := policy.1 rfl (sourceObserve owner state, history owner)
        let effective := effectiveDisclosure published selected config intended
        have left : revealKernel normalized (sourceObserve owner state, actualHistory owner) =
            PMF.pure effective := by
          rw [revealKernel, compiled]
          simp only [PurePolicy.toBehavioral, PurePolicy.normalizeDisclosureFrom, restored]
          congr 1
          exact effectiveDisclosureView_observe published selected config intended
        have right : revealKernel profile (sourceObserve owner state, history owner) =
            PMF.pure intended := by
          rw [revealKernel, prescribed]
          rfl
        rw [left, right, PMF.pure_bind, PMF.pure_bind]
        change runWith next _
            (Env.cons (disclosureResult published selected config effective) state)
            _ _ _ =
          runWith next _ (Env.cons (disclosureResult published selected config intended) state)
            _ _ _
        rw [show disclosureResult published selected config effective =
          disclosureResult published selected config intended from
            disclosureResult_effectiveDisclosure published selected config intended]
        apply normalizeDisclosureFrom_runWith next _ _ _ policy.2
          (afterReveal profile) (afterReveal normalized)
          (fun other different => congrArg Prod.snd (others other different))
          (congrArg Prod.snd prescribed) (congrArg Prod.snd compiled)
        · intro other different
          simp only [Function.update_of_ne different, histories other different]
        · simp only [decide_true, Function.update_self]
          apply afterPrivateAction_view _ published (.publication payload) _ state
            (history owner) (actualHistory owner) restored
          simp only [PurePolicy.revealChoice, dite_true, restored, Option.map_some, intended]
      · have kernel : revealKernel normalized (sourceObserve owner state, actualHistory owner) =
            revealKernel profile (sourceObserve owner state, history owner) := by
          rw [revealKernel, others owner owned, histories owner owned]
          rfl
        rw [kernel]
        apply bind_congr_on_support _
        intro disclose _
        apply normalizeDisclosureFrom_runWith next _ _ _ policy.2
          (afterReveal profile) (afterReveal normalized)
          (fun other different => congrArg Prod.snd (others other different))
          (congrArg Prod.snd prescribed) (congrArg Prod.snd compiled)
        · intro other different
          by_cases same : other = owner
          · subst other
            simp only [Function.update_self, histories owner owned]
          · simp only [Function.update_of_ne same, histories other different]
        · simp only [show decide (owner = who) = false by simp [owned],
            Function.update_of_ne (Ne.symm owned)]
          exact afterPrivateAction_foreign_view unpatch published (.publication payload) _
            state (history who) (actualHistory who) restored _

/-- No reset of the existing private histories is needed to normalize a
continuation. One pure transformed policy works for every hidden state. -/
theorem normalizeDisclosure_runFrom {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (profile : BehavioralProfile program) (policy : PurePolicy who program)
    (config : Config Player L Γ) :
    runFrom program (Function.update profile who
        ((policy.normalizeDisclosureFrom program config.registry config.revelations id).toBehavioral
          program)) config =
      runFrom program (Function.update profile who (policy.toBehavioral program)) config :=
  normalizeDisclosureFrom_runWith program config.registry config.revelations id policy _ _
    (fun other different => by simp only [Function.update_of_ne different])
    (Function.update_self ..) (Function.update_self ..) config.state config.history config.history
    (fun _ _ => rfl) rfl

/-- A finite mixture of effective continuation policies preserves the joint
law of every initial parameter and the complete typed terminal state. The draw
is shared across the hidden configurations; it is not chosen after seeing them. -/
theorem exists_effectiveDisclosure_belief_mixture {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} {Parameter : Type}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (replacement : BehavioralPolicy who program) (registry : Registry Γ)
    (revelations : Revelations Γ) (belief : PMF (Config Player L Γ))
    (registryEq : ∀ config ∈ belief.support, config.registry = registry)
    (revelationsEq : ∀ config ∈ belief.support, @config.revelations = @revelations)
    (parameter : Config Player L Γ → Parameter) :
    ∃ mixture : PMF {policy : BehavioralPolicy who program //
        policy.EffectiveDisclosures program registry revelations},
      (belief.bind fun config =>
        (runFrom program (Function.update profile who replacement) config).map
          (fun result => (parameter config, result))) =
      mixture.bind fun alternative => belief.bind fun config =>
        (runFrom program (Function.update profile who alternative.1) config).map
          (fun result => (parameter config, result)) := by
  classical
  obtain ⟨mixture, laws⟩ :=
    exists_pureMixture program profile replacement belief.supportFinset.toList
  refine ⟨mixture.map (fun policy =>
    ⟨(policy.normalizeDisclosureFrom program registry revelations id).toBehavioral program,
      normalizeDisclosureFrom_effective program registry revelations id policy⟩), ?_⟩
  rw [PMF.bind_map, PMF.bind_comm]
  apply bind_congr_on_support _
  intro config supported
  rw [laws config (Finset.mem_toList.mpr (FinDist.mem_supportFinset.mpr supported)),
    PMF.map_bind]
  apply bind_congr_on_support _
  intro policy _
  have same := normalizeDisclosure_runFrom program profile policy config
  rw [registryEq config supported, revelationsEq config supported] at same
  exact congrArg (PMF.map fun result => (parameter config, result)) same.symm

end SourceProgram
end Vegas
