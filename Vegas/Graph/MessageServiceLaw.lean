/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageService
import Vegas.Graph.MessagePolicyLaws

/-! # Local execution laws for the prescribed graph service -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph
open Interaction.MessageApplication

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- Player instructions are absent from the environment cursor, so the first
environment call in a reaction-free phase is exactly reserved inclusion. -/
theorem serviceEnvironment_reactionFree_include
    (runtime : GraphRuntime Player L Δ) (owner : Player)
    (rest : List (ServiceInstruction Player)) (wire : runtime.application.WirePolicy) :
    runtime.serviceEnvironment
        ([.player owner, .player owner, .includeLatest owner] ++ rest) wire [] =
      runtime.application.includeLatestFrom owner [] := by
  funext view
  simp [serviceEnvironment, ServiceInstruction.environmentSlot,
    MessageApplication.includeLatestFrom]

private theorem preparedRaw_append_prepare
    (runtime : GraphRuntime Player L Δ) (history : List (Entry runtime))
    (before : runtime.application.View) (site : Nat) (raw : Raw L)
    (h : preparedRaw history site = none) :
    preparedRaw (history ++ [⟨before, .privateCommand (.prepare site raw)⟩]) site =
      some raw := by
  induction history with
  | nil => simp [preparedRaw]
  | cons entry history ih =>
      cases entry with
      | mk view command =>
          cases command <;> simp_all [preparedRaw]

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

/-- The first invocation of a reaction-free bind block retains the graph bind
kernel exactly. Each sampled choice is installed by the real shared runner as
the phase-indexed private preparation, after which the remaining player and
reserved-inclusion invocations execute normally. This is the distributional
factorization used by the bind case of whole-graph service induction. -/
theorem runPolicies_bind_first_kernel
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (site : Nat) (name : VarId) (owner : Player)
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner (.bind name owner fresh next))
    (players : Player → runtime.application.PlayerPolicy)
    (execution : runtime.application.PolicyExecution)
    (wire : runtime.application.WirePolicy)
    (rest : List (ServiceInstruction Player))
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
    let environment := runtime.serviceEnvironment
      ([.player owner, .player owner, .includeLatest owner] ++ rest) wire
    runtime.application.runPolicies players environment
        [.player owner, .player owner, .environment] execution =
      kernel.bind fun choice =>
        (runtime.application.playerStep owner execution
          (.privateCommand (.prepare site ⟨R.result payload,
            (R.valueEquiv payload).symm choice⟩))).bind fun prepared =>
          runtime.application.runPolicies players environment
            [.player owner, .environment] prepared := by
  dsimp only
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, hplayer]
  rw [compileAt_bind_fresh runtime whole site name owner fresh next policy
    (execution.principalHistory owner)
    (State.observe runtime.application execution.native owner)
    hpc hwho hΓ hunprepared hunsubmitted]
  simp only [FinDist.map_eq_bind, FinDist.pure_bind, FinDist.bind_bind]

end Vegas.GraphRuntime
