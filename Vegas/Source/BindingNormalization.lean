/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ValueBinding
import Vegas.Source.PublicObservation
import Vegas.Source.ObservationRecall
import GameTheory.Math.Probability.Support

/-! # Normalizing accepted unusable bindings

The policy reconstruction changes private binding observations and own recall.
It retains the actual public default record at every view. The source evaluator
and its canonical successors are used on both sides of the public-law certificate.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Reconstruct the private components of a view while retaining its public record. -/
abbrev ViewMap (who : Player) (Γ : SourceCtx Player L) :=
  DecisionView who Γ → SourceObservation L who Γ × List (OwnAction Player L)

/-- Restore private observations and recall without modifying public default history. -/
def ViewMap.restore {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (view : DecisionView who Γ) : DecisionView who Γ :=
  ⟨(unpatch view).1, view.defaults, (unpatch view).2⟩

/-- Mark an immutable binding introduced by the policy reconstruction. -/
abbrev PatchMap (who : Player) (Γ : SourceCtx Player L) :=
  ∀ {name : VarId} {owner : Player} {payload : L.Ty},
    HasVar Γ name (.commitment owner payload) → DecisionView who Γ → Bool

/-- Carry private reconstruction over a public sample. -/
def ViewMap.afterSample {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (name : VarId) (payload : L.Ty) : ViewMap who ((name, .publicData payload) :: Γ) :=
  fun view =>
    let earlier := unpatch (view.back false)
    (⟨fun _ cell selected => match selected with
      | .here => view.observation.cells name (.publicData payload) .here
      | .there prior => earlier.1.cells _ cell prior⟩, earlier.2)

/-- Samples introduce no patched binding. -/
def PatchMap.afterSample {who : Player} {Γ : SourceCtx Player L} (patched : PatchMap who Γ)
    (name : VarId) (payload : L.Ty) : PatchMap who ((name, .publicData payload) :: Γ) :=
  fun selected view => match selected with
    | .there prior => patched prior (view.back false)

/-- Restore an active original binding choice, distinguishing omission from no callback. -/
def ViewMap.afterCommit {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (ownStep : Bool) (name : VarId) (owner : Player) (payload : L.Ty)
    (original : DecisionView who Γ → Option (Option (PublicationResult (L.Val payload)))) :
    ViewMap who ((name, .commitment owner payload) :: Γ) := fun view =>
  let prior := view.back ownStep
  let earlier := unpatch prior
  let replaced := match original prior with | some (some .failure) => true | _ => false
  (⟨fun _ cell selected => match selected with
    | .here => if replaced then some .failure else view.observation.cells name _ .here
    | .there previous => earlier.1.cells _ cell previous⟩,
    earlier.2 ++ (original prior).toList.map (OwnAction.commit owner name payload))

/-- A fresh binding is patched precisely for an accepted unusable original choice. -/
def PatchMap.afterCommit {who : Player} {Γ : SourceCtx Player L} (patched : PatchMap who Γ)
    (ownStep : Bool) (name : VarId) (owner : Player) (payload : L.Ty)
    (original : DecisionView who Γ → Option (Option (PublicationResult (L.Val payload)))) :
    PatchMap who ((name, .commitment owner payload) :: Γ) := fun selected view =>
  match selected with
  | .here => match original (view.back ownStep) with
    | some (some .failure) => true
    | _ => false
  | .there prior => patched prior (view.back ownStep)

/-- Restore an original active disclosure intention after publishing the shared result. -/
def ViewMap.afterReveal {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (ownStep : Bool) (published name : VarId) (owner : Player) (payload : L.Ty)
    (original : DecisionView who Γ → Option Bool) :
    ViewMap who ((published, .publication payload) :: Γ) := fun view =>
  let prior := view.back ownStep
  let earlier := unpatch prior
  (⟨fun _ cell selected => match selected with
    | .here => view.observation.cells published (.publication payload) .here
    | .there previous => earlier.1.cells _ cell previous⟩,
    earlier.2 ++ (original prior).toList.map (OwnAction.reveal owner name))

/-- Revelations introduce no new patched binding. -/
def PatchMap.afterReveal {who : Player} {Γ : SourceCtx Player L} (patched : PatchMap who Γ)
    (ownStep : Bool) (published : VarId) (payload : L.Ty) :
    PatchMap who ((published, .publication payload) :: Γ) := fun selected view =>
  match selected with
  | .there prior => patched prior (view.back ownStep)

/-- Read a genuine active binding callback, with an outer option for no callback. -/
def PurePolicy.commitChoice {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (owner : Player) (payload : L.Ty)
    (kernel : (owner = who) → (view : DecisionView who Γ) → who ∉ view.defaulted →
      Option (PublicationResult (L.Val payload))) :
    DecisionView who Γ → Option (Option (PublicationResult (L.Val payload))) := fun view =>
  if own : owner = who then
    if active : who ∉ view.defaulted then some (kernel own (unpatch.restore view) active)
    else none
  else none

/-- Read a genuine active disclosure callback. -/
def PurePolicy.revealChoice {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (owner : Player)
    (kernel : (owner = who) → (view : DecisionView who Γ) → who ∉ view.defaulted → Bool) :
    DecisionView who Γ → Option Bool := fun view =>
  if own : owner = who then
    if active : who ∉ view.defaulted then some (kernel own (unpatch.restore view) active)
    else none
  else none

private def normalizeBindingChoice (payload : L.Ty) :
    Option (PublicationResult (L.Val payload)) → Option (PublicationResult (L.Val payload))
  | some .failure => some (.success (L.someValue payload))
  | choice => choice

/-- Replace accepted unusable bindings, retaining omission and all other active choices. -/
def PurePolicy.bindValuesFrom {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    ViewMap who Γ → PatchMap who Γ → PurePolicy who program → PurePolicy who program
  | _, _, .ret _, _, _, _ => PUnit.unit
  | _, _, .sample (payload := payload) name _ _ next, unpatch, patched, policy =>
      bindValuesFrom next (unpatch.afterSample name payload)
        (PatchMap.afterSample patched name payload)
        policy
  | _, _, .commit (payload := payload) name owner _ _ next, unpatch, patched, policy =>
      let ownStep := decide (owner = who)
      let original := PurePolicy.commitChoice unpatch owner payload policy.1
      (fun own view active =>
        normalizeBindingChoice payload (policy.1 own (unpatch.restore view) active),
        bindValuesFrom next (unpatch.afterCommit ownStep name owner payload original)
          (PatchMap.afterCommit patched ownStep name owner payload original) policy.2)
  | _, _, .reveal (payload := payload) published owner name _ selected _ next,
      unpatch, patched, policy =>
      let ownStep := decide (owner = who)
      let original := PurePolicy.revealChoice unpatch owner policy.1
      (fun own view active => if patched selected view then false
        else policy.1 own (unpatch.restore view) active,
        bindValuesFrom next (unpatch.afterReveal ownStep published name owner payload original)
          (PatchMap.afterReveal patched ownStep published payload) policy.2)

/-- Initialize private reconstruction with the actual view and no patched bindings. -/
def PurePolicy.bindValues {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (policy : PurePolicy who program) :
    PurePolicy who program :=
  policy.bindValuesFrom program (fun view => (view.observation, view.history)) (fun _ _ => false)

/-- The normalization always respects value admission, including unreachable views. -/
theorem valueBinding_bindValuesFrom {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (unpatch : ViewMap who Γ) → (patched : PatchMap who Γ) → (policy : PurePolicy who program) →
    ValueBinding program ((policy.bindValuesFrom program unpatch patched).toBehavioral program)
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, _, _, policy => valueBinding_bindValuesFrom next _ _ policy
  | _, _, .commit _ _ _ _ next, unpatch, _, policy => by
      refine ⟨?_, valueBinding_bindValuesFrom next _ _ policy.2⟩
      intro own view active
      simp only [PurePolicy.toBehavioral, PurePolicy.bindValuesFrom, PMF.mem_support_pure_iff]
      cases policy.1 own (unpatch.restore view) active with
      | none => simp [normalizeBindingChoice]
      | some result => cases result <;> simp [normalizeBindingChoice]
  | _, _, .reveal _ _ _ _ _ _ next, _, _, policy => valueBinding_bindValuesFrom next _ _ policy.2

/-- The initialized pure policy admits no accepted unusable binding. -/
theorem valueBinding_bindValues {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (policy : PurePolicy who program) :
    ValueBinding program ((policy.bindValues program).toBehavioral program) :=
  valueBinding_bindValuesFrom program _ _ policy

/-- The original and translated configurations differ only in tracked private bindings
and reconstructed own recall. Public history is retained by the reconstruction map. -/
structure Patched {who : Player} {Γ : SourceCtx Player L} (unpatch : ViewMap who Γ)
    (patched : PatchMap who Γ) (left right : Config Player L Γ) : Prop where
  registryEq : right.registry = left.registry
  revelationsEq : @right.revelations = @left.revelations
  publicEq : ∀ {name payload} (selected : HasVar Γ name (.publicData payload)),
    right.state.get selected = left.state.get selected
  inputEq : ∀ {name owner payload} (selected : HasVar Γ name (.privateInput owner payload)),
    right.state.get selected = left.state.get selected
  publicationEq : ∀ {name payload} (selected : HasVar Γ name (.publication payload)),
    right.state.get selected = left.state.get selected
  foreignEq : ∀ {name owner payload} (selected : HasVar Γ name (.commitment owner payload)),
    owner ≠ who → right.state.get selected = left.state.get selected
  replacedEq : ∀ {name payload} (selected : HasVar Γ name (.commitment who payload)),
    patched selected (right.view who) = true →
      left.state.get selected = .failure ∧ right.state.get selected = .success (L.someValue payload)
  keptEq : ∀ {name payload} (selected : HasVar Γ name (.commitment who payload)),
    patched selected (right.view who) = false → right.state.get selected = left.state.get selected
  historyEq : ∀ other, other ≠ who → right.history other = left.history other
  unpatchEq : unpatch.restore (right.view who) = left.view who

omit [IExpr.ResultTypes L] in
/-- Private reconstruction entails exact equality of the authoritative public record. -/
theorem Patched.defaults {who : Player} {Γ : SourceCtx Player L} {unpatch : ViewMap who Γ}
    {patched : PatchMap who Γ} {left right : Config Player L Γ}
    (valid : Patched unpatch patched left right) : right.defaults = left.defaults :=
  congrArg DecisionView.defaults valid.unpatchEq

omit [IExpr.ResultTypes L] in
/-- Every active/inactive test agrees between the paired executions. -/
theorem Patched.defaulted {who : Player} {Γ : SourceCtx Player L} {unpatch : ViewMap who Γ}
    {patched : PatchMap who Γ} {left right : Config Player L Γ}
    (valid : Patched unpatch patched left right) : right.defaulted = left.defaulted :=
  congrArg DefaultHistory.defaulted valid.defaults

omit [IExpr.ResultTypes L] in
/-- Every other player has precisely its original complete view. -/
theorem Patched.foreignView {who : Player} {Γ : SourceCtx Player L} {unpatch : ViewMap who Γ}
    {patched : PatchMap who Γ} {left right : Config Player L Γ}
    (valid : Patched unpatch patched left right) (other : Player) (different : other ≠ who) :
    right.view other = left.view other := by
  have observed := sourceObserve_congr other right.state left.state valid.publicEq
    valid.publicationEq valid.inputEq (fun selected => valid.foreignEq selected different)
  change (⟨sourceObserve other right.state, right.defaults, right.history other⟩ :
      DecisionView other Γ) = ⟨sourceObserve other left.state, left.defaults, left.history other⟩
  rw [observed, valid.defaults, valid.historyEq other different]

omit [IExpr.ResultTypes L] in
/-- An untouched configuration is related to itself without a reachability premise. -/
theorem Patched.refl {who : Player} {Γ : SourceCtx Player L} (config : Config Player L Γ) :
    Patched (who := who) (fun view => (view.observation, view.history))
      (fun _ _ => false) config config where
  registryEq := rfl
  revelationsEq := rfl
  publicEq _ := rfl
  inputEq _ := rfl
  publicationEq _ := rfl
  foreignEq _ _ := rfl
  replacedEq _ impossible := by contradiction
  keptEq _ _ := rfl
  historyEq _ _ := rfl
  unpatchEq := rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem decisionView_ext {who : Player} {Γ : SourceCtx Player L}
    {left right : DecisionView who Γ}
    (observed : left.observation = right.observation) (defaults : left.defaults = right.defaults)
    (history : left.history = right.history) : left = right := by
  cases left
  cases right
  cases observed
  cases defaults
  cases history
  rfl

omit [IExpr.ResultTypes L] in
/-- A shared public sample preserves the private reconstruction invariant. -/
theorem Patched.sample {who : Player} {Γ : SourceCtx Player L} {unpatch : ViewMap who Γ}
    {patched : PatchMap who Γ} {left right : Config Player L Γ}
    (valid : Patched unpatch patched left right) (name : VarId) (payload : L.Ty)
    (value : L.Val payload) :
    Patched (unpatch.afterSample name payload) (PatchMap.afterSample patched name payload)
      (sampleSuccessor name left value) (sampleSuccessor name right value) where
  registryEq := by simp only [sampleSuccessor, valid.registryEq]
  revelationsEq := by simp only [sampleSuccessor, valid.revelationsEq]
  publicEq selected := by
    cases selected with
    | here => rfl
    | there prior => exact valid.publicEq prior
  inputEq selected := match selected with | .there prior => valid.inputEq prior
  publicationEq selected := match selected with | .there prior => valid.publicationEq prior
  foreignEq selected different := match selected with
    | .there prior => valid.foreignEq prior different
  replacedEq selected replaced := by
    cases selected with
    | there prior =>
        simp only [PatchMap.afterSample, back_sample_view] at replaced
        exact valid.replacedEq prior replaced
  keptEq selected kept := by
    cases selected with
    | there prior =>
        simp only [PatchMap.afterSample, back_sample_view] at kept
        exact valid.keptEq prior kept
  historyEq := valid.historyEq
  unpatchEq := by
    apply decisionView_ext
    · change (unpatch.afterSample name payload ((sampleSuccessor name right value).view who)).1 =
        sourceObserve who (sampleSuccessor name left value).state
      simp only [ViewMap.afterSample, back_sample_view]
      have previous : (unpatch (right.view who)).1 = sourceObserve who left.state :=
        congrArg DecisionView.observation valid.unpatchEq
      rw [previous]
      apply congrArg SourceObservation.mk
      funext cellName cell selected
      cases selected with
      | here => rfl
      | there prior => cases cell <;> rfl
    · exact congrArg (fun defaults => defaults.record none) valid.defaults
    · change (unpatch.afterSample name payload ((sampleSuccessor name right value).view who)).2 =
        left.history who
      have previous : (unpatch (right.view who)).2 = left.history who :=
        congrArg DecisionView.history valid.unpatchEq
      simpa only [ViewMap.afterSample, back_sample_view] using previous

omit [IExpr.ResultTypes L] in
private theorem back_own_commit_view {who : Player} {Γ : SourceCtx Player L}
    {name : VarId} {payload : L.Ty} (guard : SourceGuard L Γ who name payload)
    (config : Config Player L Γ) (choice : Option (PublicationResult (L.Val payload))) :
    ((commitSuccessor name guard config choice).view who).back true = config.view who := by
  simpa only [decide_true] using back_commit_view who name guard config choice

omit [IExpr.ResultTypes L] in
/-- Own binding repair preserves the public status of omission versus acceptance. -/
theorem Patched.commit_own {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ} {left right : Config Player L Γ}
    (valid : Patched unpatch patched left right) (name : VarId) (payload : L.Ty)
    (guard : SourceGuard L Γ who name payload) (choice : Option (PublicationResult (L.Val payload)))
    (original : DecisionView who Γ → Option (Option (PublicationResult (L.Val payload))))
    (callback : original (right.view who) =
      if who ∈ right.defaulted then none else some choice) :
    Patched (unpatch.afterCommit true name who payload original)
      (PatchMap.afterCommit patched true name who payload original)
      (commitSuccessor name guard left choice)
      (commitSuccessor name guard right (normalizeBindingChoice payload choice)) where
  registryEq := by simp only [commitSuccessor, valid.registryEq]
  revelationsEq := by simp only [commitSuccessor, valid.revelationsEq]
  publicEq selected := match selected with | .there prior => valid.publicEq prior
  inputEq selected := match selected with | .there prior => valid.inputEq prior
  publicationEq selected := match selected with | .there prior => valid.publicationEq prior
  foreignEq selected different := by
    cases selected with
    | here => exact (different rfl).elim
    | there prior => exact valid.foreignEq prior different
  replacedEq selected replaced := by
    cases selected with
    | here =>
        simp only [PatchMap.afterCommit, back_own_commit_view, callback] at replaced
        by_cases inactive : who ∈ right.defaulted
        · simp only [inactive, ite_true] at replaced
          contradiction
        · have leftActive : who ∉ left.defaulted := valid.defaulted ▸ inactive
          cases choice with
          | none => simp only [inactive, ite_false] at replaced; contradiction
          | some result =>
              cases result with
              | failure => simp [normalizeBindingChoice, commitSuccessor, inactive, leftActive]
              | success value => simp only [inactive, ite_false] at replaced; contradiction
    | there prior =>
        simp only [PatchMap.afterCommit, back_own_commit_view] at replaced
        exact valid.replacedEq prior replaced
  keptEq selected kept := by
    cases selected with
    | here =>
        simp only [PatchMap.afterCommit, back_own_commit_view, callback] at kept
        by_cases inactive : who ∈ right.defaulted
        · have leftInactive : who ∈ left.defaulted := valid.defaulted ▸ inactive
          simp [commitSuccessor, inactive, leftInactive]
        · have leftActive : who ∉ left.defaulted := valid.defaulted ▸ inactive
          cases choice with
          | none => simp [normalizeBindingChoice, commitSuccessor, inactive, leftActive]
          | some result =>
              cases result with
              | failure => simp only [inactive, ite_false] at kept; contradiction
              | success value =>
                  simp [normalizeBindingChoice, commitSuccessor, inactive, leftActive]
    | there prior =>
        simp only [PatchMap.afterCommit, back_own_commit_view] at kept
        exact valid.keptEq prior kept
  historyEq other different := by
    by_cases inactive : who ∈ right.defaulted
    · have leftInactive : who ∈ left.defaulted := valid.defaulted ▸ inactive
      simp only [commitSuccessor, inactive, leftInactive, ite_true]
      exact valid.historyEq other different
    · have leftActive : who ∉ left.defaulted := valid.defaulted ▸ inactive
      simp only [commitSuccessor, inactive, leftActive, ite_false, Function.update_of_ne different]
      exact valid.historyEq other different
  unpatchEq := by
    apply decisionView_ext
    · change (unpatch.afterCommit true name who payload original
        ((commitSuccessor name guard right _).view who)).1 =
          sourceObserve who (commitSuccessor name guard left choice).state
      simp only [ViewMap.afterCommit, back_own_commit_view]
      have previous : (unpatch (right.view who)).1 = sourceObserve who left.state :=
        congrArg DecisionView.observation valid.unpatchEq
      rw [previous]
      apply congrArg SourceObservation.mk
      funext cellName cell selected
      cases selected with
      | here =>
          rw [callback]
          by_cases inactive : who ∈ right.defaulted
          · have leftInactive : who ∈ left.defaulted := valid.defaulted ▸ inactive
            simp [Config.view, sourceObserve, Env.get, Env.cons, commitSuccessor, inactive,
              leftInactive]
          · have leftActive : who ∉ left.defaulted := valid.defaulted ▸ inactive
            cases choice with
            | none =>
                simp [Config.view, sourceObserve, Env.get, Env.cons, normalizeBindingChoice,
                  commitSuccessor, inactive, leftActive]
            | some result => cases result <;>
                simp [Config.view, sourceObserve, Env.get, Env.cons, normalizeBindingChoice,
                  commitSuccessor, inactive, leftActive]
      | there prior => cases cell <;> rfl
    · change (commitSuccessor name guard right _).defaults =
        (commitSuccessor name guard left choice).defaults
      by_cases inactive : who ∈ right.defaulted
      · have leftInactive : who ∈ left.defaulted := valid.defaulted ▸ inactive
        simp only [commitSuccessor, inactive, leftInactive, ite_true, valid.defaults]
      · have leftActive : who ∉ left.defaulted := valid.defaulted ▸ inactive
        cases choice with
        | none =>
            simp [normalizeBindingChoice, commitSuccessor, inactive, leftActive, valid.defaults]
        | some result => cases result <;>
            simp [normalizeBindingChoice, commitSuccessor, inactive, leftActive, valid.defaults]
    · change (unpatch.afterCommit true name who payload original
        ((commitSuccessor name guard right _).view who)).2 =
          (commitSuccessor name guard left choice).history who
      simp only [ViewMap.afterCommit, back_own_commit_view]
      have previous : (unpatch (right.view who)).2 = left.history who :=
        congrArg DecisionView.history valid.unpatchEq
      rw [previous, callback]
      by_cases inactive : who ∈ right.defaulted
      · have leftInactive : who ∈ left.defaulted := valid.defaulted ▸ inactive
        simp [commitSuccessor, inactive, leftInactive]
      · have leftActive : who ∉ left.defaulted := valid.defaulted ▸ inactive
        simp [commitSuccessor, inactive, leftActive]


omit [IExpr.ResultTypes L] in
private theorem back_foreign_commit_view {who : Player} {Γ : SourceCtx Player L}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (guard : SourceGuard L Γ owner name payload) (different : owner ≠ who)
    (config : Config Player L Γ) (choice : Option (PublicationResult (L.Val payload))) :
    ((commitSuccessor name guard config choice).view who).back false = config.view who := by
  simpa only [different, decide_false] using back_commit_view who name guard config choice

omit [IExpr.ResultTypes L] in
/-- An unchanged foreign binding preserves all of the reconstructed private data. -/
theorem Patched.commit_foreign {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ} {left right : Config Player L Γ}
    (valid : Patched unpatch patched left right) (name : VarId) (owner : Player)
    (payload : L.Ty) (guard : SourceGuard L Γ owner name payload) (different : owner ≠ who)
    (choice : Option (PublicationResult (L.Val payload))) :
    Patched (unpatch.afterCommit false name owner payload (fun _ => none))
      (PatchMap.afterCommit patched false name owner payload (fun _ => none))
      (commitSuccessor name guard left choice) (commitSuccessor name guard right choice) where
  registryEq := by simp only [commitSuccessor, valid.registryEq]
  revelationsEq := by simp only [commitSuccessor, valid.revelationsEq]
  publicEq selected := match selected with | .there prior => valid.publicEq prior
  inputEq selected := match selected with | .there prior => valid.inputEq prior
  publicationEq selected := match selected with | .there prior => valid.publicationEq prior
  foreignEq selected foreign := by
    cases selected with
    | here => simp [commitSuccessor, valid.defaulted]
    | there prior => exact valid.foreignEq prior foreign
  replacedEq selected replaced := by
    cases selected with
    | here => exact (different rfl).elim
    | there prior =>
        simp only [PatchMap.afterCommit, back_foreign_commit_view guard different] at replaced
        exact valid.replacedEq prior replaced
  keptEq selected kept := by
    cases selected with
    | here => exact (different rfl).elim
    | there prior =>
        simp only [PatchMap.afterCommit, back_foreign_commit_view guard different] at kept
        exact valid.keptEq prior kept
  historyEq other foreign := by
    simp only [commitSuccessor, valid.defaulted]
    by_cases inactive : owner ∈ left.defaulted
    · simp only [inactive, ite_true]
      exact valid.historyEq other foreign
    · simp only [inactive, ite_false]
      by_cases own : other = owner
      · subst other
        simp only [Function.update_self, valid.historyEq owner different]
      · simp only [Function.update_of_ne own, valid.historyEq other foreign]
  unpatchEq := by
    apply decisionView_ext
    · change (unpatch.afterCommit false name owner payload (fun _ => none)
        ((commitSuccessor name guard right choice).view who)).1 =
          sourceObserve who (commitSuccessor name guard left choice).state
      simp only [ViewMap.afterCommit, back_foreign_commit_view guard different]
      have previous : (unpatch (right.view who)).1 = sourceObserve who left.state :=
        congrArg DecisionView.observation valid.unpatchEq
      rw [previous]
      apply congrArg SourceObservation.mk
      funext cellName cell selected
      cases selected with
      | here => simp [Config.view, sourceObserve, different]
      | there prior => cases cell <;> rfl
    · change (commitSuccessor name guard right choice).defaults =
        (commitSuccessor name guard left choice).defaults
      simp only [commitSuccessor, valid.defaulted, valid.defaults]
    · change (unpatch.afterCommit false name owner payload (fun _ => none)
        ((commitSuccessor name guard right choice).view who)).2 =
          (commitSuccessor name guard left choice).history who
      simp only [ViewMap.afterCommit, back_foreign_commit_view guard different,
        Option.toList_none, List.map_nil, List.append_nil]
      have previous : (unpatch (right.view who)).2 = left.history who :=
        congrArg DecisionView.history valid.unpatchEq
      rw [previous]
      simp only [commitSuccessor]
      split <;> simp only [Function.update_of_ne (Ne.symm different)]


omit [IExpr.ResultTypes L] in
/-- Identical actual publication proposals face identical completed guard checks. -/
theorem Patched.reveal_result {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ} {left right : Config Player L Γ}
    (valid : Patched unpatch patched left right) (published : VarId)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (selected : HasVar Γ name (.commitment owner payload)) (disclose repaired : Bool)
    (proposalEq :
      (if (if owner ∈ right.defaulted then false else repaired) then right.state.get selected
        else .failure) =
      (if (if owner ∈ left.defaulted then false else disclose) then left.state.get selected
        else .failure)) :
    (revealSuccessor published selected right repaired).state.get .here =
      (revealSuccessor published selected left disclose).state.get .here := by
  let leftProposal : PublicationResult (L.Val payload) :=
    if (if owner ∈ left.defaulted then false else disclose) then left.state.get selected
      else .failure
  let rightProposal : PublicationResult (L.Val payload) :=
    if (if owner ∈ right.defaulted then false else repaired) then right.state.get selected
      else .failure
  change (if (right.registry.completedBy (published := published) right.revelations selected).all
      (·.accepts (Revelations.reveal right.revelations selected)
        (Env.cons rightProposal right.state)) then
        rightProposal else .failure) =
    (if (left.registry.completedBy (published := published) left.revelations selected).all
      (·.accepts (Revelations.reveal left.revelations selected)
        (Env.cons leftProposal left.state)) then
        leftProposal else .failure)
  change rightProposal = leftProposal at proposalEq
  rw [valid.registryEq, valid.revelationsEq, proposalEq]
  apply congrArg (fun accepted : Bool => if accepted then leftProposal else .failure)
  apply congrArg (List.all (left.registry.completedBy left.revelations selected))
  funext obligation
  apply Obligation.accepts_congr
  · intro cellName cellPayload cell
    cases cell with | there prior => exact valid.publicEq prior
  · intro cellName cellPayload cell
    cases cell with
    | here => rfl
    | there prior => exact valid.publicationEq prior


omit [IExpr.ResultTypes L] in
/-- Matched actual publications preserve private reconstruction and public timing. -/
theorem Patched.reveal {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ} {left right : Config Player L Γ}
    (valid : Patched unpatch patched left right) (published name : VarId)
    (owner : Player) (payload : L.Ty)
    (selected : HasVar Γ name (.commitment owner payload)) (disclose repaired : Bool)
    (foreignChoice : owner ≠ who → repaired = disclose)
    (resultEq : (revealSuccessor published selected right repaired).state.get .here =
      (revealSuccessor published selected left disclose).state.get .here)
    (original : DecisionView who Γ → Option Bool)
    (callback : original (right.view who) =
      if owner = who ∧ owner ∉ right.defaulted then some disclose else none) :
    Patched (unpatch.afterReveal (decide (owner = who)) published name owner payload original)
      (PatchMap.afterReveal patched (decide (owner = who)) published payload)
      (revealSuccessor published selected left disclose)
      (revealSuccessor published selected right repaired) where
  registryEq := by simp only [revealSuccessor_registry, valid.registryEq]
  revelationsEq := by simp only [revealSuccessor_revelations, valid.revelationsEq]
  publicEq cell := match cell with | .there prior => valid.publicEq prior
  inputEq cell := match cell with | .there prior => valid.inputEq prior
  publicationEq cell := by
    cases cell with
    | here => exact resultEq
    | there prior => exact valid.publicationEq prior
  foreignEq cell different := match cell with | .there prior => valid.foreignEq prior different
  replacedEq cell replaced := by
    cases cell with
    | there prior =>
        simp only [PatchMap.afterReveal, back_reveal_view] at replaced
        exact valid.replacedEq prior replaced
  keptEq cell kept := by
    cases cell with
    | there prior =>
        simp only [PatchMap.afterReveal, back_reveal_view] at kept
        exact valid.keptEq prior kept
  historyEq other different := by
    simp only [revealSuccessor, valid.defaulted]
    by_cases inactive : owner ∈ left.defaulted
    · simp only [inactive, ite_true]
      exact valid.historyEq other different
    · simp only [inactive, ite_false]
      by_cases own : other = owner
      · subst other
        simp only [Function.update_self, valid.historyEq owner different,
          foreignChoice different]
      · simp only [Function.update_of_ne own, valid.historyEq other different]
  unpatchEq := by
    apply decisionView_ext
    · change (unpatch.afterReveal (decide (owner = who)) published name owner payload original
        ((revealSuccessor published selected right repaired).view who)).1 =
          sourceObserve who (revealSuccessor published selected left disclose).state
      simp only [ViewMap.afterReveal, back_reveal_view]
      have previous : (unpatch (right.view who)).1 = sourceObserve who left.state :=
        congrArg DecisionView.observation valid.unpatchEq
      rw [previous]
      apply congrArg SourceObservation.mk
      funext cellName cellKind cell
      cases cell with
      | here => exact resultEq
      | there prior => cases cellKind <;> rfl
    · change (revealSuccessor published selected right repaired).defaults =
        (revealSuccessor published selected left disclose).defaults
      rw [revealSuccessor_defaults, revealSuccessor_defaults, resultEq,
        valid.defaults, valid.defaulted]
    · change (unpatch.afterReveal (decide (owner = who)) published name owner payload original
        ((revealSuccessor published selected right repaired).view who)).2 =
          (revealSuccessor published selected left disclose).history who
      simp only [ViewMap.afterReveal, back_reveal_view]
      have previous : (unpatch (right.view who)).2 = left.history who :=
        congrArg DecisionView.history valid.unpatchEq
      rw [previous, callback]
      by_cases own : owner = who
      · subst owner
        by_cases inactive : who ∈ right.defaulted
        · have leftInactive : who ∈ left.defaulted := valid.defaulted ▸ inactive
          simp [revealSuccessor, inactive, leftInactive]
        · have leftActive : who ∉ left.defaulted := valid.defaulted ▸ inactive
          simp [revealSuccessor, inactive, leftActive]
      · simp only [own, false_and, ite_false, Option.toList_none, List.map_nil,
          List.append_nil, revealSuccessor]
        split <;> simp only [Function.update_of_ne (Ne.symm own)]


omit [IExpr.ResultTypes L] in
/-- A repaired private failure is withheld; every other proposal is unchanged. -/
theorem Patched.own_proposal {who : Player} {Γ : SourceCtx Player L}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ} {left right : Config Player L Γ}
    (valid : Patched unpatch patched left right) {name : VarId} {payload : L.Ty}
    (selected : HasVar Γ name (.commitment who payload)) (disclose : Bool) :
    (if (if who ∈ right.defaulted then false else
        if patched selected (right.view who) then false else disclose) then
      right.state.get selected else .failure) =
      (if (if who ∈ left.defaulted then false else disclose) then
        left.state.get selected else .failure) := by
  rw [valid.defaulted]
  by_cases inactive : who ∈ left.defaulted
  · simp only [inactive, ite_true, Bool.false_eq_true, ite_false]
  · simp only [inactive, ite_false]
    cases replaced : patched selected (right.view who) with
    | true => simp [(valid.replacedEq selected replaced).1]
    | false => simp [valid.keptEq selected replaced]


omit [IExpr.ResultTypes L] in
private theorem active_callback_congr {who : Player} {Γ : SourceCtx Player L} {α : Type}
    (callback : (view : DecisionView who Γ) → who ∉ view.defaulted → α)
    {left right : DecisionView who Γ} (same : left = right)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted) :
    callback left leftActive = callback right rightActive := by
  cases same
  rfl

/-- Private binding reconstruction preserves the complete public terminal law. -/
theorem bindValues_publicProjection_eq {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) :
    ∀ (unpatch : ViewMap who Γ) (patched : PatchMap who Γ),
    (policy : PurePolicy who program) → (profile translated : BehavioralProfile program) →
    (∀ other, other ≠ who → translated other = profile other) →
    profile who = policy.toBehavioral program →
    translated who = (policy.bindValuesFrom program unpatch patched).toBehavioral program →
    (left right : Config Player L Γ) → Patched unpatch patched left right →
    (runFrom program translated right).map
        (fun final => (sourcePublicEnv final.state, final.defaults)) =
      (runFrom program profile left).map
        (fun final => (sourcePublicEnv final.state, final.defaults)) := by
  induction program with
  | ret payoffs =>
      intro unpatch patched policy profile translated agree original normalized left right valid
      simp only [runFrom, PMF.pure_map]
      apply congrArg PMF.pure
      rw [sourcePublicEnv_congr right.state left.state valid.publicEq valid.publicationEq,
        valid.defaults]
  | sample name fresh law next ih =>
      intro unpatch patched policy profile translated agree original normalized left right valid
      simp only [runFrom, PMF.map_bind]
      rw [sourcePublicEnv_congr right.state left.state valid.publicEq valid.publicationEq]
      apply bind_congr_on_support _
      intro value _
      exact ih _ _ policy (afterSample profile)
        (afterSample translated) agree original normalized _ _ (valid.sample name _ value)
  | @commit Γ O name owner payload fresh guard next ih =>
      intro unpatch patched policy profile translated agree original normalized left right valid
      have tailsAgree : ∀ other, other ≠ who →
          afterCommit translated other = afterCommit profile other :=
        fun other different => congrArg Prod.snd (agree other different)
      have originalTail : afterCommit profile who = policy.2.toBehavioral next :=
        congrArg Prod.snd original
      by_cases own : owner = who
      · subst owner
        have normalizedTail : afterCommit translated who =
            (policy.2.bindValuesFrom next
              (unpatch.afterCommit true name who payload
                (PurePolicy.commitChoice unpatch who payload policy.1))
              (PatchMap.afterCommit patched true name who payload
                (PurePolicy.commitChoice unpatch who payload policy.1))).toBehavioral next := by
          simpa only [afterCommit, afterReveal, PurePolicy.toBehavioral,
            PurePolicy.bindValuesFrom, decide_true] using
            congrArg Prod.snd normalized
        by_cases inactive : who ∈ right.defaulted
        · have leftInactive : who ∈ left.defaulted := valid.defaulted ▸ inactive
          simp only [runFrom, inactive, leftInactive, dite_true, PMF.pure_bind]
          apply ih _ _ policy.2 (afterCommit profile)
            (afterCommit translated) tailsAgree originalTail normalizedTail
          apply valid.commit_own name payload guard none
          simp [PurePolicy.commitChoice, inactive]
        · have leftActive : who ∉ left.defaulted := valid.defaulted ▸ inactive
          have translatedKernel : commitKernel translated (right.view who) inactive =
              PMF.pure (normalizeBindingChoice payload
                (policy.1 rfl (left.view who) leftActive)) := by
            rw [commitKernel, normalized]
            simp only [PurePolicy.toBehavioral, PurePolicy.bindValuesFrom]
            rw [active_callback_congr (policy.1 rfl) valid.unpatchEq inactive leftActive]
          have originalKernel : commitKernel profile (left.view who) leftActive =
              PMF.pure (policy.1 rfl (left.view who) leftActive) := by
            rw [commitKernel, original]
            rfl
          simp only [runFrom, inactive, leftActive, dite_false,
            translatedKernel, originalKernel, PMF.pure_bind]
          apply ih _ _ policy.2 (afterCommit profile)
            (afterCommit translated) tailsAgree originalTail normalizedTail
          apply valid.commit_own name payload guard (policy.1 rfl (left.view who) leftActive)
          have restored := active_callback_congr (policy.1 rfl) valid.unpatchEq inactive leftActive
          simpa [PurePolicy.commitChoice, inactive] using congrArg some restored
      · have choices : PurePolicy.commitChoice unpatch owner payload policy.1 =
            fun _ => none := by funext view; simp only [PurePolicy.commitChoice, own, dite_false]
        have normalizedTail : afterCommit translated who =
            (policy.2.bindValuesFrom next
              (unpatch.afterCommit false name owner payload (fun _ => none))
              (PatchMap.afterCommit patched false name owner payload
                (fun _ => none))).toBehavioral next := by
          simpa only [afterCommit, afterReveal, PurePolicy.toBehavioral, PurePolicy.bindValuesFrom,
            own, decide_false, choices] using congrArg Prod.snd normalized
        have kernels : ∀ active : owner ∉ right.defaulted,
            commitKernel translated (right.view owner) active =
              commitKernel profile (left.view owner) (by
                change owner ∉ left.defaulted
                exact valid.defaulted ▸ active) := by
          intro active
          rw [commitKernel, commitKernel, agree owner own]
          exact active_callback_congr ((profile owner).1 rfl)
            (valid.foreignView owner own) _ _
        simp only [runFrom, PMF.map_bind]
        by_cases inactive : owner ∈ right.defaulted
        · have leftInactive : owner ∈ left.defaulted := valid.defaulted ▸ inactive
          simp only [inactive, leftInactive, dite_true, PMF.pure_bind]
          exact ih _ _ policy.2 (afterCommit profile)
            (afterCommit translated) tailsAgree originalTail normalizedTail _ _
            (valid.commit_foreign name owner payload guard own none)
        · have leftActive : owner ∉ left.defaulted := valid.defaulted ▸ inactive
          simp only [inactive, leftActive, dite_false]
          rw [kernels inactive]
          apply bind_congr_on_support _
          intro choice _
          exact ih _ _ policy.2 (afterCommit profile)
            (afterCommit translated) tailsAgree originalTail normalizedTail _ _
            (valid.commit_foreign name owner payload guard own choice)
  | @reveal Γ O published owner name payload fresh selected unresolved next ih =>
      intro unpatch patched policy profile translated agree original normalized left right valid
      have tailsAgree : ∀ other, other ≠ who →
          afterReveal translated other = afterReveal profile other :=
        fun other different => congrArg Prod.snd (agree other different)
      have originalTail : afterReveal profile who = policy.2.toBehavioral next :=
        congrArg Prod.snd original
      by_cases own : owner = who
      · subst owner
        have normalizedTail : afterReveal translated who =
            (policy.2.bindValuesFrom next
              (unpatch.afterReveal true published name who payload
                (PurePolicy.revealChoice unpatch who policy.1))
              (PatchMap.afterReveal patched true published payload)).toBehavioral next := by
          simpa only [afterCommit, afterReveal, PurePolicy.toBehavioral,
            PurePolicy.bindValuesFrom, decide_true] using
            congrArg Prod.snd normalized
        by_cases inactive : who ∈ right.defaulted
        · have leftInactive : who ∈ left.defaulted := valid.defaulted ▸ inactive
          simp only [runFrom, inactive, leftInactive, dite_true, PMF.pure_bind]
          apply ih _ _ policy.2 (afterReveal profile)
            (afterReveal translated) tailsAgree originalTail normalizedTail
          have resultEq := valid.reveal_result published selected false false (by
            simp only [ite_self, Bool.false_eq_true, ite_false])
          simpa only [decide_true] using valid.reveal published name who payload selected false
            false (fun different => (different rfl).elim) resultEq
            (PurePolicy.revealChoice unpatch who policy.1) (by
              simp [PurePolicy.revealChoice, inactive])
        · have leftActive : who ∉ left.defaulted := valid.defaulted ▸ inactive
          let disclose := policy.1 rfl (left.view who) leftActive
          let repaired := if patched selected (right.view who) then false else disclose
          have translatedKernel : revealKernel translated (right.view who) inactive =
              PMF.pure repaired := by
            rw [revealKernel, normalized]
            simp only [PurePolicy.toBehavioral, PurePolicy.bindValuesFrom]
            rw [active_callback_congr (policy.1 rfl) valid.unpatchEq inactive leftActive]
          have originalKernel : revealKernel profile (left.view who) leftActive =
              PMF.pure disclose := by
            rw [revealKernel, original]
            rfl
          simp only [runFrom, inactive, leftActive, dite_false,
            translatedKernel, originalKernel, PMF.pure_bind]
          apply ih _ _ policy.2 (afterReveal profile)
            (afterReveal translated) tailsAgree originalTail normalizedTail
          have resultEq := valid.reveal_result published selected disclose repaired
            (valid.own_proposal selected disclose)
          simpa only [decide_true] using valid.reveal published name who payload selected disclose
            repaired (fun different => (different rfl).elim) resultEq
            (PurePolicy.revealChoice unpatch who policy.1) (by
              have restored := active_callback_congr (policy.1 rfl) valid.unpatchEq
                inactive leftActive
              simpa [PurePolicy.revealChoice, inactive, disclose] using congrArg some restored)
      · have choices : PurePolicy.revealChoice unpatch owner policy.1 = fun _ => none := by
          funext view
          simp only [PurePolicy.revealChoice, own, dite_false]
        have normalizedTail : afterReveal translated who =
            (policy.2.bindValuesFrom next
              (unpatch.afterReveal false published name owner payload (fun _ => none))
              (PatchMap.afterReveal patched false published payload)).toBehavioral next := by
          simpa only [afterCommit, afterReveal, PurePolicy.toBehavioral, PurePolicy.bindValuesFrom,
            own, decide_false, choices] using congrArg Prod.snd normalized
        have kernels : ∀ active : owner ∉ right.defaulted,
            revealKernel translated (right.view owner) active =
              revealKernel profile (left.view owner) (by
                change owner ∉ left.defaulted
                exact valid.defaulted ▸ active) := by
          intro active
          rw [revealKernel, revealKernel, agree owner own]
          exact active_callback_congr ((profile owner).1 rfl)
            (valid.foreignView owner own) _ _
        have nextValid : ∀ disclose,
            Patched (unpatch.afterReveal false published name owner payload (fun _ => none))
              (PatchMap.afterReveal patched false published payload)
              (revealSuccessor published selected left disclose)
              (revealSuccessor published selected right disclose) := by
          intro disclose
          have resultEq := valid.reveal_result published selected disclose disclose (by
            rw [valid.defaulted, valid.foreignEq selected own])
          simpa only [own, decide_false] using valid.reveal published name owner payload selected
            disclose disclose (fun _ => rfl) resultEq (fun _ => none) (by simp only [own,
              false_and, ite_false])
        simp only [runFrom, PMF.map_bind]
        by_cases inactive : owner ∈ right.defaulted
        · have leftInactive : owner ∈ left.defaulted := valid.defaulted ▸ inactive
          simp only [inactive, leftInactive, dite_true, PMF.pure_bind]
          exact ih _ _ policy.2 (afterReveal profile)
            (afterReveal translated) tailsAgree originalTail normalizedTail _ _ (nextValid false)
        · have leftActive : owner ∉ left.defaulted := valid.defaulted ▸ inactive
          simp only [inactive, leftActive, dite_false]
          rw [kernels inactive]
          apply bind_congr_on_support _
          intro disclose _
          exact ih _ _ policy.2 (afterReveal profile)
            (afterReveal translated) tailsAgree originalTail normalizedTail _ _ (nextValid disclose)

/-- Replacing only the chosen player's pure policy preserves the public terminal
law, including the entire public default record, against arbitrary opponents. -/
theorem bindValues_run_publicOutcome_eq {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (policy : PurePolicy who program) (state : State L Γ) :
    (run program (Function.update profile who
      ((policy.bindValues program).toBehavioral program)) state).map (publicOutcome program) =
      (run program (Function.update profile who (policy.toBehavioral program)) state).map
        (publicOutcome program) :=
by
  have same := bindValues_publicProjection_eq program _ _ policy
    (Function.update profile who (policy.toBehavioral program))
    (Function.update profile who ((policy.bindValues program).toBehavioral program))
    (fun other different => by simp only [Function.update_of_ne different])
    (Function.update_self ..) (Function.update_self ..) _ _ (Patched.refl (Config.initial state))
  have mapped := congrArg (PMF.map fun valuesDefaults =>
    (⟨valuesDefaults.1, valuesDefaults.2⟩ : PublicOutcome program)) same
  unfold run
  change PMF.map (fun final : Config Player L program.terminalCtx =>
      (⟨sourcePublicEnv final.state, final.defaults⟩ : PublicOutcome program)) _ =
    PMF.map (fun final : Config Player L program.terminalCtx =>
      (⟨sourcePublicEnv final.state, final.defaults⟩ : PublicOutcome program)) _
  simpa only [PMF.map_comp, Function.comp_def] using mapped

end Vegas.SourceProgram
