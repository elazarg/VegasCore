/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.Continuation
import Vegas.Pending.PrefixComposition
import Vegas.Pending.StepLaw

/-! # Continuation laws across graph phase transitions -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- A cached bind result makes the head continuation exactly its typed tail
continuation. Runtime histories are retained, including markers for later sites
that may already have been produced by reaction scheduling. -/
theorem continuation_bind_cached
    (runtime : GraphRuntime Player L Δ) (name : VarId) (owner : Player)
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (profile : BehavioralProfile (.bind name owner fresh next)) (site : Nat)
    (env : VEnv L Γ) (logical : History Player L)
    (histories : Player → List (Entry runtime))
    (choice : PublicationResult (L.Val payload))
    (cached : preparedChoice (histories owner) site payload = some choice) :
    continuation runtime (.bind name owner fresh next) profile site env logical histories =
      continuation runtime next (afterBind profile) (site + 1)
        (VEnv.cons ((R.valueEquiv payload).symm choice) env)
        (Function.update logical owner
          (logical owner ++ [OwnAction.bind owner name payload choice])) histories := by
  simp [continuation, cached]

/-- A cached disclosure similarly identifies the resolve head with the exact
accepted-result tail used by `advanceResolve`. -/
theorem continuation_resolve_cached
    (runtime : GraphRuntime Player L Δ) (outputName bindingName : VarId)
    (owner : Player) {payload : L.Ty} (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (profile : BehavioralProfile
      (.resolve outputName owner bindingName fresh source checks next))
    (site : Nat) (env : VEnv L Γ) (logical : History Player L)
    (histories : Player → List (Entry runtime)) (disclose : Bool)
    (cached : rememberedDisclosure (histories owner) site = some disclose) :
    continuation runtime (.resolve outputName owner bindingName fresh source checks next)
        profile site env logical histories =
      continuation runtime next (afterResolve profile) (site + 1)
        (VEnv.cons ((R.valueEquiv payload).symm
          (acceptedResult source checks env disclose)) env)
        (Function.update logical owner
          (logical owner ++ [OwnAction.resolve owner bindingName disclose])) histories := by
  simp [continuation, cached]

/-- Public sampling advances the continuation by the same exact graph kernel
used by the native sample tick. Existing runtime caches pass through unchanged. -/
theorem continuation_sample_step
    (runtime : GraphRuntime Player L Δ) (name : VarId) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (law : PublicDist (L := L) Γ payload)
    (next : Graph Player L ((name, .pub payload) :: Γ) Δ)
    (profile : BehavioralProfile (.sample name fresh law next)) (site : Nat)
    (env : VEnv L Γ) (logical : History Player L)
    (histories : Player → List (Entry runtime)) :
    continuation runtime (.sample name fresh law next) profile site env logical histories =
      (law.eval env).bind fun value =>
        continuation runtime next (afterSample profile) (site + 1)
          (VEnv.cons value env) logical histories := by
  rfl

/-- The sample continuation kernel is unchanged when the native public-value
view is used instead of the ideal environment, provided public agreement holds. -/
theorem continuation_sample_public
    (runtime : GraphRuntime Player L Δ) (name : VarId) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (law : PublicDist (L := L) Γ payload)
    (next : Graph Player L ((name, .pub payload) :: Γ) Δ)
    (profile : BehavioralProfile (.sample name fresh law next)) (site : Nat)
    (env : VEnv L Γ)
    (logical : History Player L) (histories : Player → List (Entry runtime)) :
    continuation runtime (.sample name fresh law next) profile site env logical histories =
      (law.evalPublic (PublicValues.ofVEnv env)).bind fun value =>
        continuation runtime next (afterSample profile) (site + 1)
          (VEnv.cons value env) logical histories := by
  rw [continuation_sample_step]
  rw [PublicDist.evalPublic_ofVEnv]

/-- Original-graph form of cached bind advancement. The successor continuation
uses exactly the successor prefix profile and projected logical history. -/
theorem Prefix.continuation_bind_advance
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (name : VarId) (owner : Player) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name owner fresh next) site)
    (env : VEnv L Γ) (histories : Player → List (Entry runtime))
    (choice : PublicationResult (L.Val payload))
    (cached : preparedChoice (histories owner) site payload = some choice)
    (unique : (Γ.map Prod.fst).Nodup) :
    continuation runtime (.bind name owner fresh next)
        (walk.profileTail profile) site env
        (fun who => projectLogicalHistory who (observe who env) (histories who) whole 0 site)
        histories =
      continuation runtime next
        ((walk.trans (.bind (.refl next))).profileTail profile) (site + 1)
        (VEnv.cons ((R.valueEquiv payload).symm choice) env)
        (fun who => projectLogicalHistory who
          (observe who (VEnv.cons (x := name) (τ := .sealed owner (R.result payload))
            ((R.valueEquiv payload).symm choice) env))
          (histories who) whole 0 (site + 1)) histories := by
  rw [walk.profileTail_trans (.bind (.refl next)) profile]
  rw [continuation_bind_cached runtime name owner fresh next
    (walk.profileTail profile) site env
    _ histories choice cached]
  congr 1
  funext who
  rw [walk.projectLogicalHistory_bind who env (histories who) choice unique]
  by_cases same : who = owner
  · subst who
    simp [Function.update]
  · simp [Function.update, same, Ne.symm same]

/-- Original-graph form of cached resolve advancement. -/
theorem Prefix.continuation_resolve_advance
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole
      (.resolve outputName owner bindingName fresh source checks next) site)
    (env : VEnv L Γ) (histories : Player → List (Entry runtime)) (disclose : Bool)
    (cached : rememberedDisclosure (histories owner) site = some disclose)
    (unique : (Γ.map Prod.fst).Nodup) :
    let accepted := acceptedResult source checks env disclose
    continuation runtime (.resolve outputName owner bindingName fresh source checks next)
        (walk.profileTail profile) site env
        (fun who => projectLogicalHistory who (observe who env) (histories who) whole 0 site)
        histories =
      continuation runtime next
        ((walk.trans (.resolve (.refl next))).profileTail profile) (site + 1)
        (VEnv.cons ((R.valueEquiv payload).symm accepted) env)
        (fun who => projectLogicalHistory who
          (observe who (VEnv.cons (x := outputName) (τ := .pub (R.result payload))
            ((R.valueEquiv payload).symm accepted) env))
          (histories who) whole 0 (site + 1)) histories := by
  dsimp only
  rw [walk.profileTail_trans (.resolve (.refl next)) profile]
  rw [continuation_resolve_cached runtime outputName bindingName owner fresh source checks next
    (walk.profileTail profile) site env _ histories disclose cached]
  congr 1
  funext who
  by_cases same : who = owner
  · subst who
    rw [walk.projectLogicalHistory_resolve owner env (histories owner)
      (acceptedResult source checks env disclose) disclose cached unique]
    simp [Function.update]
  · rw [walk.projectLogicalHistory_append who _ (histories who) 0 1,
      walk.projectLogicalHistory_cons who env (histories who) _ unique fresh 0]
    simp only [projectLogicalHistory]
    rw [if_neg (Ne.symm same)]
    have zero : projectLogicalHistory who
        (observe who (VEnv.cons (x := outputName) (τ := .pub (R.result payload))
          ((R.valueEquiv payload).symm (acceptedResult source checks env disclose)) env))
        (histories who) next (0 + site + 1) 0 = [] := by
      cases next <;> rfl
    rw [zero]
    simp [Function.update, same]

/-- Original-graph form of public sample advancement. -/
theorem Prefix.continuation_sample_advance
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (name : VarId) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (law : PublicDist (L := L) Γ payload)
    (next : Graph Player L ((name, .pub payload) :: Γ) Δ)
    (walk : Prefix Δ whole (.sample name fresh law next) site)
    (env : VEnv L Γ) (histories : Player → List (Entry runtime))
    (unique : (Γ.map Prod.fst).Nodup) :
    continuation runtime (.sample name fresh law next)
        (walk.profileTail profile) site env
        (fun who => projectLogicalHistory who (observe who env) (histories who) whole 0 site)
        histories =
      (law.eval env).bind fun value =>
        continuation runtime next
          ((walk.trans (.sample (.refl next))).profileTail profile) (site + 1)
          (VEnv.cons value env)
          (fun who => projectLogicalHistory who
            (observe who (VEnv.cons (x := name) (τ := .pub payload) value env))
            (histories who) whole 0 (site + 1)) histories := by
  rw [walk.profileTail_trans (.sample (.refl next)) profile]
  rw [continuation_sample_step]
  apply FinDist.bind_congr
  intro value _
  congr 1
  funext who
  exact (walk.projectLogicalHistory_sample who env (histories who) value unique).symm

/-- Concrete native-tick package for sample phases: the actual environment
step and the projected continuation use the same retained public kernel. -/
theorem Prefix.continuation_sample_environmentStep
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (name : VarId) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (law : PublicDist (L := L) Γ payload)
    (next : Graph Player L ((name, .pub payload) :: Γ) Δ)
    (walk : Prefix Δ whole (.sample name fresh law next) site)
    (env : VEnv L Γ) (values : PublicValues Γ)
    (agreement : (values : PublicValues Γ) =
      (PublicValues.ofVEnv env : PublicValues Γ))
    (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (histories : Player → List (Entry runtime)) (unique : (Γ.map Prod.fst).Nodup) :
    (runtime.environmentStep
        (.running (.sample name fresh law next) env values bindings candidates site clock enteredAt)
        .tick =
      (law.evalPublic values).map fun value =>
        .running next (VEnv.cons value env) (PublicValues.consPublic value values)
          bindings candidates (site + 1) (clock + 1) (clock + 1)) ∧
    continuation runtime (.sample name fresh law next)
        (walk.profileTail profile) site env
        (fun who => projectLogicalHistory who (observe who env) (histories who) whole 0 site)
        histories =
      (law.evalPublic values).bind fun value =>
        continuation runtime next
          ((walk.trans (.sample (.refl next))).profileTail profile)
          (site + 1) (VEnv.cons value env)
          (fun who => projectLogicalHistory who
            (observe who (VEnv.cons (x := name) (τ := .pub payload) value env))
            (histories who) whole 0 (site + 1)) histories := by
  constructor
  · exact environmentStep_sample runtime fresh law next env values bindings candidates
      site clock enteredAt
  · rw [agreement, PublicDist.evalPublic_ofVEnv]
    exact walk.continuation_sample_advance runtime whole profile site name fresh law next env
      histories unique

end Vegas.GraphRuntime
