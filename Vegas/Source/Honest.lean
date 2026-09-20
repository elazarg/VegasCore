/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ValueBinding
import Vegas.Source.Disclosure

/-! # Honest play publishes what it bound

An honest policy binds a value at every commitment it owns and opens at every
reveal it owns. Those are the two classes named alongside the edges that need
them: `ValueBinding` and `Disclosing`.

Honesty alone does not make a run succeed, because a retained guard may still
reject what was opened. The premise that it does not is stated where it is
decided — at each reveal, at any configuration in which nothing has failed yet —
rather than as a property of the program alone, since whether a guard accepts
depends on the values bound.

Under both, no cell of a completed run records a failure.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A policy that binds a value everywhere and opens everywhere. -/
def Honest {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) (policy : BehavioralPolicy who p) : Prop :=
  ValueBinding p policy ∧ Disclosing p policy

/-- No cell records a failure: every binding holds a value, and every
publication carries one. -/
structure Successful {Γ : SourceCtx Player L} (state : State L Γ) : Prop where
  /-- Every private cell is bound to a value. -/
  bindings : ∀ {x o τ} (h : HasVar Γ x (.privateData o τ)),
    ∃ value, state.get h = .success value
  /-- Every publication carries a value. -/
  publications : ∀ {x τ} (h : HasVar Γ x (.publication τ)),
    ∃ value, state.get h = .success value

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem successful_empty : Successful (Player := Player) (L := L) (Env.empty _) where
  bindings := fun h => nomatch h
  publications := fun h => nomatch h

/-- Every guard retained at a reveal accepts the value opened there, in any
state in which nothing has failed yet. The obligations and publications are
threaded exactly as execution threads them, so this asks about the guards the
program actually retains rather than about an arbitrary registry. -/
def GuardsAccept : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    SourceProgram Player L Γ O → Registry Γ → Revelations Γ → Prop
  | _, _, .ret _, _, _ => True
  | _, _, .sample _ _ _ k, registry, revelations =>
      GuardsAccept k registry.weaken revelations.weaken
  | _, _, .commit name owner _ guard k, registry, revelations =>
      GuardsAccept k
        ({ owner := owner, subject := name, payload := _, source := .here,
            guard := guard.weaken } :: registry.weaken) revelations.weaken
  | _, _, .reveal published _ _ _ source _ k, registry, revelations =>
      (∀ state : State L _, Successful state → ∀ value,
        state.get source = .success value →
        (Registry.completedBy (published := published) registry revelations source).all
          (·.accepts (Revelations.reveal revelations source)
            (Env.cons (.success value) state)) = true) ∧
        GuardsAccept k registry.weaken (Revelations.reveal revelations source)

/-- Honest play from a configuration in which nothing has failed reaches only
terminal states in which nothing has failed. Every publication of a completed
honest run therefore succeeds. -/
theorem runFrom_successful :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    (profile : BehavioralProfile p) → (∀ who, Honest p (profile who)) →
    (config : Config Player L Γ) → Successful config.state →
    GuardsAccept p config.registry config.revelations →
    ∀ terminal ∈ (runFrom p profile config).support, Successful terminal
  | _, _, .ret _, _, _, _, hconfig, _, terminal, hterminal => by
      rw [runFrom, runWith, FinDist.mem_support_pure] at hterminal
      exact hterminal ▸ hconfig
  | _, _, .sample sampleName _ _ k, profile, honest, config, hconfig, guards,
      terminal, hterminal => by
      rw [runFrom_sample, FinDist.support_bind] at hterminal
      obtain ⟨value, _, hmem⟩ := Set.mem_iUnion₂.mp hterminal
      refine runFrom_successful k (afterSample profile) (fun who => honest who)
        (sampleSuccessor sampleName config value) ?_ guards terminal hmem
      exact
        { bindings := fun h => match h with
            | .there h' => hconfig.bindings h'
          publications := fun h => match h with
            | .there h' => hconfig.publications h' }
  | _, _, .commit cellName owner _ guard k, profile, honest, config, hconfig, guards,
      terminal, hterminal => by
      rw [runFrom_commit, FinDist.support_bind] at hterminal
      obtain ⟨choice, hchoice, hmem⟩ := Set.mem_iUnion₂.mp hterminal
      have hvalue : ∃ value, choice = .success value := by
        cases choice with
        | failure =>
            exact absurd hchoice ((honest owner).1.1 rfl (Config.view owner config))
        | success value => exact ⟨value, rfl⟩
      obtain ⟨value, rfl⟩ := hvalue
      refine runFrom_successful k (afterCommit profile)
        (fun who => ⟨(honest who).1.2, (honest who).2⟩)
        (commitSuccessor cellName guard config (.success value)) ?_ guards terminal hmem
      exact
        { bindings := fun h => match h with
            | .here => ⟨value, rfl⟩
            | .there h' => hconfig.bindings h'
          publications := fun h => match h with
            | .there h' => hconfig.publications h' }
  | _, _, .reveal published owner _ _ source _ k, profile, honest, config, hconfig, guards,
      terminal, hterminal => by
      rw [runFrom_reveal, FinDist.support_bind] at hterminal
      obtain ⟨disclose, hdisclose, hmem⟩ := Set.mem_iUnion₂.mp hterminal
      have hopen : disclose = true := by
        cases disclose with
        | false => exact absurd hdisclose ((honest owner).2.1 rfl (Config.view owner config))
        | true => rfl
      subst hopen
      obtain ⟨value, hbound⟩ := hconfig.bindings source
      have haccepts := guards.1 config.state hconfig value hbound
      refine runFrom_successful k (afterReveal profile)
        (fun who => ⟨(honest who).1, (honest who).2.2⟩)
        (revealSuccessor published source config true) ?_ guards.2 terminal hmem
      have hhead : (revealSuccessor published source config true).state.get
          (HasVar.here (x := published)) = .success value := by
        simp only [revealSuccessor, Env.cons_get_here, if_true, hbound, haccepts]
      exact
        { bindings := fun h => match h with
            | .there h' => hconfig.bindings h'
          publications := fun h => match h with
            | .here => ⟨value, hhead⟩
            | .there h' => hconfig.publications h' }

/-- The same from a fresh start: an honest run of a checked program publishes a
value in every publication cell. -/
theorem run_successful {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) (profile : BehavioralProfile p)
    (honest : ∀ who, Honest p (profile who))
    (guards : GuardsAccept p [] (Revelations.initial Γ))
    (state : State L Γ) (hstate : Successful state) :
    ∀ terminal ∈ (run p profile state).support, Successful terminal :=
  runFrom_successful p profile honest ⟨state, [], Revelations.initial Γ, fun _ => []⟩
    hstate guards

end Vegas.SourceProgram
