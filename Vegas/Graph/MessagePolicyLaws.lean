/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessagePolicies

/-! # Local laws of prescribed graph message policies -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- At a fresh owned bind phase the compiler invokes exactly the graph bind
kernel and maps its result to preparation of the phase-indexed slot. -/
theorem compileAt_bind_fresh
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (site : Nat) (name : VarId) (owner : Player)
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner (.bind name owner fresh next))
    (history : List (Entry runtime)) (view : runtime.application.View)
    (hpc : view.application.publicState.pc = site)
    (hwho : view.application.who = owner)
    (hΓ : view.application.publicState.Γ = Γ)
    (hunprepared : preparedRaw history site = none)
    (hunsubmitted : submittedAt history site = false) :
    compileAt runtime owner whole (.bind name owner fresh next) policy site history view =
      (policy.1 rfl (projectDecisionView owner history whole site
        (hΓ ▸ (hwho ▸ view.application.privateObservation)))).map fun choice =>
          .privateCommand (.prepare site ⟨R.result payload,
            (R.valueEquiv payload).symm choice⟩) := by
  simp [compileAt, hpc, hwho, hΓ, hunprepared, hunsubmitted]

/-- Once its phase-indexed candidate is prepared, the next invocation submits
the canonical commitment without sampling the graph kernel again. -/
theorem compileAt_bind_prepared
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (site : Nat) (name : VarId) (owner : Player)
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner (.bind name owner fresh next))
    (history : List (Entry runtime)) (view : runtime.application.View) (raw : Raw L)
    (hpc : view.application.publicState.pc = site)
    (hprepared : preparedRaw history site = some raw)
    (hunsubmitted : submittedAt history site = false) :
    compileAt runtime owner whole (.bind name owner fresh next) policy site history view =
      FinDist.pure (.submit (.commitment site (owner, .prepared site))) := by
  simp [compileAt, hpc, hprepared, hunsubmitted]

/-- At a fresh owned resolve phase the compiler invokes exactly the graph
resolve kernel and records its Boolean privately before any wire submission. -/
theorem compileAt_resolve_fresh
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (site : Nat) (outputName bindingName : VarId)
    (owner : Player) {payload : L.Ty} (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner
      (.resolve outputName owner bindingName fresh source checks next))
    (history : List (Entry runtime)) (view : runtime.application.View)
    (hpc : view.application.publicState.pc = site)
    (hwho : view.application.who = owner)
    (hΓ : view.application.publicState.Γ = Γ)
    (hunremembered : rememberedDisclosure history site = none)
    (hunsubmitted : submittedAt history site = false) :
    compileAt runtime owner whole
        (.resolve outputName owner bindingName fresh source checks next)
        policy site history view =
      (policy.1 rfl (projectDecisionView owner history
        whole site
        (hΓ ▸ (hwho ▸ view.application.privateObservation)))).map fun disclose =>
          .privateCommand (.rememberDisclosure disclose) := by
  simp [compileAt, hpc, hwho, hΓ, hunremembered, hunsubmitted]

/-- A remembered positive disclosure whose public guard precheck fails is sent
as the uniform withhold packet. In particular, the opening command containing
the raw private value is absent from the resulting distribution. -/
theorem compileAt_resolve_rejected
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (site : Nat) (outputName bindingName : VarId)
    (owner : Player) {payload : L.Ty} (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner
      (.resolve outputName owner bindingName fresh source checks next))
    (history : List (Entry runtime)) (view : runtime.application.View)
    (encoded : L.Val (R.result payload))
    (hpc : view.application.publicState.pc = site)
    (hwho : view.application.who = owner)
    (hΓ : view.application.publicState.Γ = Γ)
    (hremembered : rememberedDisclosure history site = some true)
    (hunsubmitted : submittedAt history site = false)
    (hobserved :
      (hΓ ▸ (hwho ▸ view.application.privateObservation)).cells.get source = some encoded)
    (hrejected : acceptedProposal checks (hΓ ▸ view.application.publicState.values)
      (R.valueEquiv payload encoded) = .failure) :
    compileAt runtime owner whole
        (.resolve outputName owner bindingName fresh source checks next)
        policy site history view =
      FinDist.pure (.submit (.withhold site)) := by
  simp [compileAt, hpc, hwho, hΓ, hremembered,
    hunsubmitted, hobserved, hrejected]

end Vegas.GraphRuntime
