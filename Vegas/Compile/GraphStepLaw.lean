/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphCompiler

/-! # Local semantic laws for source-to-graph compilation -/

noncomputable section
namespace Vegas.SourceProgram

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

omit [DecidableEq Player] in
theorem publicField_get_of_agrees {Γ : SourceCtx Player L} {name : VarId} {τ : L.Ty}
    (source : HasVar (SourcePublicCtx L Γ) name τ) (state : State L Γ)
    (env : VEnv L (graphCtx (R := R) Γ))
    (publicData : ∀ {field payload} (h : HasVar Γ field (.publicData payload)),
      env.get (fieldRef h) = state.get h)
    (publication : ∀ {field payload} (h : HasVar Γ field (.publication payload)),
      R.valueEquiv payload (env.get (fieldRef h)) = state.get h) :
    env.get (publicField source).ref = (sourcePublicEnv state).get source := by
  induction Γ with
  | nil => exact nomatch source
  | cons entry tail ih =>
      obtain ⟨field, cell⟩ := entry
      cases cell with
      | publicData payload =>
          cases source with
          | here =>
              change env.get (.here) = state.get .here
              exact publicData .here
          | there source =>
              exact ih source (fun _ _ h => state.get (.there h)) (VEnv.tail env)
                (fun h => publicData (.there h)) (fun h => publication (.there h))
      | privateData owner payload =>
          exact ih source (fun _ _ h => state.get (.there h)) (VEnv.tail env)
            (fun h => publicData (.there h)) (fun h => publication (.there h))
      | publication payload =>
          cases source with
          | here =>
              change env.get (.here) = (R.valueEquiv payload).symm (state.get .here)
              have equality := congrArg (R.valueEquiv payload).symm (publication .here)
              simpa only [fieldRef, Equiv.symm_apply_apply] using equality
          | there source =>
              exact ih source (fun _ _ h => state.get (.there h)) (VEnv.tail env)
                (fun h => publicData (.there h)) (fun h => publication (.there h))

omit [DecidableEq Player] in
theorem publicField_get {Γ : SourceCtx Player L} {name : VarId} {τ : L.Ty}
    (source : HasVar (SourcePublicCtx L Γ) name τ)
    (map : PublicationMap (R := R) Γ) (env : VEnv L (graphCtx (R := R) Γ)) :
    env.get (publicField source).ref =
      (sourcePublicEnv (decodeState map env)).get source := by
  apply publicField_get_of_agrees source (decodeState map env) env <;>
    intro field payload h <;> rfl

omit [DecidableEq Player] in
theorem compilePublicExpr_eval {Γ : SourceCtx Player L} {τ : L.Ty}
    (expression : L.Expr (SourcePublicCtx L Γ) τ)
    (map : PublicationMap (R := R) Γ) (env : VEnv L (graphCtx (R := R) Γ)) :
    (compilePublicExpr expression).eval env =
      L.eval expression (sourcePublicEnv (decodeState map env)) := by
  apply congrArg (L.eval expression)
  funext name payload source
  exact publicField_get source map env

omit [DecidableEq Player] in
theorem compilePublicDist_eval {Γ : SourceCtx Player L} {τ : L.Ty}
    (law : L.DistExpr (SourcePublicCtx L Γ) τ)
    (map : PublicationMap (R := R) Γ) (env : VEnv L (graphCtx (R := R) Γ)) :
    (compilePublicDist law).eval env =
      L.evalDist law (sourcePublicEnv (decodeState map env)) := by
  unfold Graph.PublicDist.eval compilePublicDist
  apply congrArg (L.evalDist law)
  funext name payload source
  exact publicField_get source map env

omit [DecidableEq Player] R in
theorem boundResult_eq_resultEquiv {Γ : SourceCtx Player L}
    {owner : Player} {payload : L.Ty} {name : VarId}
    (state : State L Γ) (source : HasVar Γ name (.privateData owner payload))
    (disclose : Bool) :
    boundResult state source disclose =
      if disclose then BoundValue.resultEquiv _ (state.get source).1 else .failure := by
  let propose : BoundValue (L.Val payload) → PublicationResult (L.Val payload) :=
    fun value => match hb : value.binding with
      | .unbound => False.elim (value.isBound hb)
      | .unopenable => .failure
      | .value data => if disclose then .success data else .failure
  change propose (state.get source).1 =
    if disclose then BoundValue.resultEquiv _ (state.get source).1 else .failure
  generalize (state.get source).1 = value
  rcases value with ⟨binding, bound⟩
  cases binding with
  | unbound => exact False.elim (bound rfl)
  | unopenable => cases disclose <;> rfl
  | value value => cases disclose <;> rfl

omit [DecidableEq Player] in
theorem boundResult_decode_eq_proposed {Γ : SourceCtx Player L}
    {owner : Player} {payload : L.Ty} {name : VarId}
    (source : HasVar Γ name (.privateData owner payload))
    (map : PublicationMap (R := R) Γ) (env : VEnv L (graphCtx (R := R) Γ))
    (disclose : Bool) :
    boundResult (decodeState map env) source disclose =
      Graph.proposedResult (fieldRef source) env disclose := by
  rw [boundResult_eq_resultEquiv]
  unfold Graph.proposedResult
  rw [decodeState_privateData]
  simp only [Equiv.apply_symm_apply]

omit [DecidableEq Player] in
theorem compile_acceptedResult {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ) (unique : (Γ.map Prod.fst).Nodup)
    (registry : Registry Γ) {owner : Player} {payload : L.Ty} {name published : VarId}
    (source : HasVar Γ name (.privateData owner payload))
    (env : VEnv L (graphCtx (R := R) Γ)) (disclose : Bool) :
    Graph.acceptedResult (outputName := published) (fieldRef source)
        (registry.weaken.map
          (compileGuard (resolveMap map unique source (published := published))))
        env disclose =
      let proposed := boundResult (decodeState map env) source disclose
      if registry.ok
          (updatePrivate (decodeState map env) source (resultPublication proposed)) then
        proposed
      else .failure := by
  let proposed := Graph.proposedResult (fieldRef source) env disclose
  let tentative : VEnv L (graphCtx ((published, .publication payload) :: Γ)) :=
    VEnv.cons (x := published) ((R.valueEquiv payload).symm proposed) env
  have checksEq := compileGuards_accept
    (resolveMap map unique source (published := published)) registry.weaken tentative
  have decodeEq := decodeState_resolve (published := published) map unique source proposed env
  unfold Graph.acceptedResult
  change (if Graph.checksAccepted _ tentative then proposed else .failure) = _
  rw [checksEq, decodeEq, Registry.ok_weaken]
  rw [show proposed = boundResult (decodeState map env) source disclose from
    (boundResult_decode_eq_proposed source map env disclose).symm]

theorem terminalPayoffs_compileGraph {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (unique : (Γ.map Prod.fst).Nodup)
    (map : PublicationMap (R := R) Γ) (registry : Registry Γ) :
    Graph.terminalPayoffs (compileGraph program unique map registry) =
      program.terminalPayoffs.map fun payoff =>
        (payoff.1, compilePublicExpr payoff.2) := by
  induction program with
  | ret => rfl
  | sample name fresh law next ih =>
      exact ih (by simp [fresh, unique]) (weakenMap map) registry.weaken
  | commit name owner fresh guard next ih =>
      exact ih (by simp [fresh, unique]) (weakenMap map) (_ :: registry.weaken)
  | reveal published owner name fresh source unresolved next ih =>
      exact ih (by simp [fresh, unique]) (resolveMap map unique source) registry.weaken

theorem compileGraph_evaluatePayoffs {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (unique : (Γ.map Prod.fst).Nodup)
    (map : PublicationMap (R := R) Γ) (registry : Registry Γ)
    (env : VEnv L (graphCtx (R := R) program.terminalCtx)) :
    Graph.evaluatePayoffs (compileGraph program unique map registry) env =
      evaluatePayoffs program (decodeState (terminalMap program unique map) env) := by
  unfold Graph.evaluatePayoffs evaluatePayoffs
  rw [terminalPayoffs_compileGraph]
  simp only [List.map_map]
  apply List.map_congr_left
  intro payoff member
  apply Prod.ext
  · rfl
  · exact congrArg L.toInt
      (compilePublicExpr_eval payoff.2 (terminalMap program unique map) env)

end Vegas.SourceProgram
