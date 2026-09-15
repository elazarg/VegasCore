/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageDeviationNormalization

/-! # Effective focal choices conserve the deviation continuation -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- A different player's resolution adds no own action, whether or not this
player's native history contains a disclosure marker at that site. -/
theorem Prefix.projectLogicalHistory_resolve_nonowner
    {runtime : GraphRuntime Player L Δ} {whole : Graph Player L Γ₀ Δ}
    {outputName bindingName : VarId} {owner : Player} {payload : L.Ty}
    {fresh : outputName ∉ Γ.map Prod.fst}
    {source : HasVar Γ bindingName (.sealed owner (R.result payload))}
    {checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ))}
    {tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ} {site : Nat}
    (walk : Prefix Δ whole
      (.resolve outputName owner bindingName fresh source checks tail) site)
    (who : Player) (different : who ≠ owner) (env : VEnv L Γ)
    (history : List (Entry runtime)) (result : PublicationResult (L.Val payload))
    (unique : (Γ.map Prod.fst).Nodup) :
    projectLogicalHistory who
        (observe who (VEnv.cons (x := outputName) (τ := .pub (R.result payload))
          ((R.valueEquiv payload).symm result) env)) history whole 0 (site + 1) =
      projectLogicalHistory who (observe who env) history whole 0 site := by
  rw [walk.projectLogicalHistory_append who _ history 0 1,
    walk.projectLogicalHistory_cons who env history _ unique fresh 0]
  cases tail <;> simp [projectLogicalHistory, Ne.symm different]

/-- When the focal graph kernel selects the effective binding action, native
binding advancement conserves the sanitized residual law. No focal cache
marker is interpreted as a graph choice. -/
theorem Prefix.deviationContinuation_bind_advance
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (focal : Player)
    (independent : IgnoresOwnHistory whole profile focal) (site : Nat)
    (name : VarId) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed focal (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name focal fresh next) site)
    (env : VEnv L Γ) (histories : Player → List (Entry runtime))
    (choice : PublicationResult (L.Val payload))
    (selected : bindKernel (walk.profileTail profile) (observe focal env, []) =
      FinDist.pure choice) (unique : (Γ.map Prod.fst).Nodup) :
    continuation runtime (.bind name focal fresh next)
        (walk.profileTail profile) site env
        (eraseFocalLogical focal (fun who => projectLogicalHistory who (observe who env)
          (histories who) whole 0 site)) (eraseFocalHistory focal histories) =
      continuation runtime next
        ((walk.trans (.bind (.refl next))).profileTail profile) (site + 1)
        (VEnv.cons ((R.valueEquiv payload).symm choice) env)
        (eraseFocalLogical focal (fun who => projectLogicalHistory who
          (observe who (VEnv.cons (x := name) (τ := .sealed focal (R.result payload))
            ((R.valueEquiv payload).symm choice) env))
          (histories who) whole 0 (site + 1))) (eraseFocalHistory focal histories) := by
  have cache : preparedChoice (eraseFocalHistory focal histories focal) site payload = none := by
    simp [eraseFocalHistory]
  rw [continuation, cache]
  have kernel : bindKernel (walk.profileTail profile)
      (observe focal env, (eraseFocalLogical focal (fun who => projectLogicalHistory who
        (observe who env) (histories who) whole 0 site)) focal) = FinDist.pure choice := by
    simpa [eraseFocalLogical] using selected
  rw [kernel, FinDist.pure_bind, walk.profileTail_trans (.bind (.refl next)) profile]
  apply runtime.continuation_congr_focal_logical next (afterBind (walk.profileTail profile))
    focal (walk.policyTail_ignoresOwnHistory profile focal independent).2 (site + 1) _ _ _
  · intro who different
    simp only [Function.update_of_ne different, eraseFocalLogical, if_neg different]
    rw [walk.projectLogicalHistory_bind who env (histories who) choice unique]
    simp [Ne.symm different]
  · simp [eraseFocalHistory]

/-- Resolve advancement similarly uses the graph action selected by the
extracted policy. Guard rejection and withholding both remain failure results. -/
theorem Prefix.deviationContinuation_resolve_advance
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (focal : Player)
    (independent : IgnoresOwnHistory whole profile focal) (site : Nat)
    (outputName bindingName : VarId) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed focal (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole
      (.resolve outputName focal bindingName fresh source checks next) site)
    (env : VEnv L Γ) (histories : Player → List (Entry runtime)) (disclose : Bool)
    (selected : resolveKernel (walk.profileTail profile) (observe focal env, []) =
      FinDist.pure disclose) (unique : (Γ.map Prod.fst).Nodup) :
    let result := acceptedResult source checks env disclose
    continuation runtime (.resolve outputName focal bindingName fresh source checks next)
        (walk.profileTail profile) site env
        (eraseFocalLogical focal (fun who => projectLogicalHistory who (observe who env)
          (histories who) whole 0 site)) (eraseFocalHistory focal histories) =
      continuation runtime next
        ((walk.trans (.resolve (.refl next))).profileTail profile) (site + 1)
        (VEnv.cons ((R.valueEquiv payload).symm result) env)
        (eraseFocalLogical focal (fun who => projectLogicalHistory who
          (observe who (VEnv.cons (x := outputName) (τ := .pub (R.result payload))
            ((R.valueEquiv payload).symm result) env))
          (histories who) whole 0 (site + 1))) (eraseFocalHistory focal histories) := by
  dsimp only
  have cache : rememberedDisclosure (eraseFocalHistory focal histories focal) site = none := by
    simp [eraseFocalHistory]
  rw [continuation, cache]
  have kernel : resolveKernel (walk.profileTail profile)
      (observe focal env, (eraseFocalLogical focal (fun who => projectLogicalHistory who
        (observe who env) (histories who) whole 0 site)) focal) = FinDist.pure disclose := by
    simpa [eraseFocalLogical] using selected
  rw [kernel, FinDist.pure_bind, walk.profileTail_trans (.resolve (.refl next)) profile]
  apply runtime.continuation_congr_focal_logical next (afterResolve (walk.profileTail profile))
    focal (walk.policyTail_ignoresOwnHistory profile focal independent).2 (site + 1) _ _ _
  · intro who different
    simp only [Function.update_of_ne different, eraseFocalLogical, if_neg different]
    exact (walk.projectLogicalHistory_resolve_nonowner who different env (histories who)
      (acceptedResult source checks env disclose) unique).symm
  · simp [eraseFocalHistory]

/-- info: 'Vegas.GraphRuntime.Prefix.deviationContinuation_resolve_advance' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.Prefix.deviationContinuation_resolve_advance

end Vegas.GraphRuntime
