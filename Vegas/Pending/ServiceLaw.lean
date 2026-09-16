/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.Service
import Vegas.Pending.PolicyLaws
import Vegas.Pending.HistoryExtension

/-! # Local execution laws for the prescribed graph service -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph
open Interaction.MessageApplication

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}


private theorem submittedAt_append_prepare
    (runtime : GraphRuntime Player L Δ) (history : List (Entry runtime))
    (before : runtime.application.View) (site : Nat) (raw : Raw L)
    (h : submittedAt history site = false) :
    submittedAt (history ++ [⟨before, .privateCommand (.prepare site raw)⟩]) site = false := by
  induction history with
  | nil => simp [submittedAt]
  | cons entry history ih =>
      cases entry with
      | mk view command =>
          cases command <;> simp_all [submittedAt]

/-- The authenticated entry recorded by the shared runner is sufficient for
the second bind invocation to submit, with no receipt or scheduler premise. -/
theorem compile_bind_after_recorded_prepare
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (site : Nat) (name : VarId) (owner : Player)
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner (.bind name owner fresh next))
    (history : List (Entry runtime)) (before after : runtime.application.View)
    (raw : Raw L) (hpc : after.application.publicState.pc = site)
    (hunprepared : preparedRaw history site = none)
    (hunsubmitted : submittedAt history site = false) :
    compileAt runtime owner whole (.bind name owner fresh next) policy site
        (history ++ [⟨before, .privateCommand (.prepare site raw)⟩]) after =
      FinDist.pure (.submit (.commitment site (owner, .prepared site))) := by
  apply compileAt_bind_prepared runtime whole site name owner fresh next policy
    _ after raw hpc
  · exact preparedRaw_append_prepare runtime history before site raw hunprepared
  · exact submittedAt_append_prepare runtime history before site raw hunsubmitted

/-- At the first fresh bind invocation the shared runner samples exactly the
graph bind kernel. The sampled choice is retained through an arbitrary remaining
schedule, including wire delivery and reactions. Neither the environment's
history nor the subsequent execution is reset at this factorization. -/
theorem runPolicies_bind_first_kernel
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (site : Nat) (name : VarId) (owner : Player)
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner (.bind name owner fresh next))
    (players : Player → runtime.application.PlayerPolicy)
    (execution : runtime.application.PolicyExecution)
    (environment : runtime.application.EnvironmentPolicy)
    (rest : List (@Invocation Player))
    (hplayer : players owner (execution.principalHistory owner)
      (State.observe runtime.application execution.native owner) =
        compileAt runtime owner whole (.bind name owner fresh next) policy site
          (execution.principalHistory owner)
          (State.observe runtime.application execution.native owner))
    (hpc :
      (State.observe runtime.application execution.native owner).application.publicState.pc = site)
    (hwho : (State.observe runtime.application execution.native owner).application.who = owner)
    (hΓ : (State.observe runtime.application execution.native owner).application.publicState.Γ = Γ)
    (hunprepared : preparedRaw (execution.principalHistory owner) site = none)
    (hunsubmitted : submittedAt (execution.principalHistory owner) site = false) :
    let graphView := projectDecisionView owner (execution.principalHistory owner)
      whole site
      (hΓ ▸ (hwho ▸
        (State.observe runtime.application execution.native owner).application.privateObservation))
    let kernel := policy.1 rfl graphView
    runtime.application.runPolicies players environment
        (.player owner :: rest) execution =
      kernel.bind fun choice =>
        (runtime.application.playerStep owner execution
          (.privateCommand (.prepare site ⟨R.result payload,
            (R.valueEquiv payload).symm choice⟩))).bind fun prepared =>
          runtime.application.runPolicies players environment rest prepared := by
  dsimp only
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, hplayer]
  rw [compileAt_bind_fresh runtime whole site name owner fresh next policy
    (execution.principalHistory owner)
    (State.observe runtime.application execution.native owner)
    hpc hwho hΓ hunprepared hunsubmitted]
  simp only [FinDist.map_eq_bind, FinDist.pure_bind, FinDist.bind_bind]

/-- A fresh disclosure samples its Boolean graph decision once and records it
privately. The continuation remains the actual native run, with its existing
histories and any pending packets; successful and failed publications do not
alter this kernel's sampling time. -/
theorem runPolicies_resolve_first_kernel
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (site : Nat) (outputName bindingName : VarId) (owner : Player)
    {payload : L.Ty} (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner
      (.resolve outputName owner bindingName fresh source checks next))
    (players : Player → runtime.application.PlayerPolicy)
    (execution : runtime.application.PolicyExecution)
    (environment : runtime.application.EnvironmentPolicy)
    (rest : List (@Invocation Player))
    (hplayer : players owner (execution.principalHistory owner)
      (State.observe runtime.application execution.native owner) =
        compileAt runtime owner whole
          (.resolve outputName owner bindingName fresh source checks next) policy site
          (execution.principalHistory owner)
          (State.observe runtime.application execution.native owner))
    (hpc :
      (State.observe runtime.application execution.native owner).application.publicState.pc = site)
    (hwho : (State.observe runtime.application execution.native owner).application.who = owner)
    (hΓ : (State.observe runtime.application execution.native owner).application.publicState.Γ = Γ)
    (hunremembered : rememberedDisclosure (execution.principalHistory owner) site = none)
    (hunsubmitted : submittedAt (execution.principalHistory owner) site = false) :
    let graphView := projectDecisionView owner (execution.principalHistory owner)
      whole site
      (hΓ ▸ (hwho ▸
        (State.observe runtime.application execution.native owner).application.privateObservation))
    runtime.application.runPolicies players environment (.player owner :: rest) execution =
      (policy.1 rfl graphView).bind fun disclose =>
        (runtime.application.playerStep owner execution
          (.privateCommand (.rememberDisclosure disclose))).bind fun recorded =>
            runtime.application.runPolicies players environment rest recorded := by
  dsimp only
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, hplayer]
  rw [compileAt_resolve_fresh runtime whole site outputName bindingName owner fresh source
    checks next policy (execution.principalHistory owner)
    (State.observe runtime.application execution.native owner)
    hpc hwho hΓ hunremembered hunsubmitted]
  simp only [FinDist.map_eq_bind, FinDist.pure_bind, FinDist.bind_bind]

end Vegas.GraphRuntime
