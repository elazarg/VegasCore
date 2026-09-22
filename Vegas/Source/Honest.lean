/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ValueBinding
import Vegas.Source.Disclosure

/-! # Honest play publishes what it bound

An honest policy binds a value at every commitment it owns and opens at every
reveal it owns. Those are the two classes named alongside the edges that need
them: `ValueBinding` and `Disclosing`.

Honesty alone does not make a run succeed, because a retained guard may still
reject what was opened. The premise that it does not follows the run: at each
reveal, at the configurations this profile can actually be in when it gets
there. It cannot be a property of the program alone, and it cannot quantify over
every failure-free state either — a state binding a value the guard rejects is
failure-free, and no profile need ever produce it, so that reading would be
false for every guard that rejects anything.

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
  bindings : ∀ {x o τ} (h : HasVar Γ x (.commitment o τ)),
    ∃ value, state.get h = .success value
  /-- Every publication carries a value. -/
  publications : ∀ {x τ} (h : HasVar Γ x (.publication τ)),
    ∃ value, state.get h = .success value

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem successful_empty : Successful (Player := Player) (L := L) (Env.empty _) where
  bindings := fun h => nomatch h
  publications := fun h => nomatch h

/-- Every guard retained at a reveal accepts what this profile opens there, at
every configuration the run can reach when it gets there.

The premise follows the run. Quantifying instead over every failure-free state
would be false for any guard that rejects something: a state binding the
rejected value is failure-free, and no profile need ever produce it. What a
guard has to accept is what is actually bound. -/
def GuardsAcceptFrom : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralProfile p → Config Player L Γ → Prop
  | _, _, .ret _, _, _ => True
  | _, _, .sample sampleName _ law k, profile, config =>
      ∀ value ∈ (L.evalDist law (sourcePublicEnv config.state)).support,
        GuardsAcceptFrom k (afterSample profile) (sampleSuccessor sampleName config value)
  | _, _, .commit cellName owner _ guard k, profile, config =>
      ∀ choice ∈ (commitKernel profile (Config.view owner config)).support,
        GuardsAcceptFrom k (afterCommit profile) (commitSuccessor cellName guard config choice)
  | _, _, .reveal published owner _ _ source _ k, profile, config =>
      (∀ value, config.state.get source = .success value →
        (Registry.completedBy (published := published) config.registry config.revelations
          source).all (·.accepts (Revelations.reveal config.revelations source)
            (Env.cons (.success value) config.state)) = true) ∧
      ∀ disclose ∈ (revealKernel profile (Config.view owner config)).support,
        GuardsAcceptFrom k (afterReveal profile)
          (revealSuccessor published source config disclose)

/-- Honest play from a configuration in which nothing has failed reaches only
terminal states in which nothing has failed. Every publication of a completed
honest run therefore succeeds. -/
theorem runFrom_successful :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    (profile : BehavioralProfile p) → (∀ who, Honest p (profile who)) →
    (config : Config Player L Γ) → Successful config.state →
    GuardsAcceptFrom p profile config →
    ∀ terminal ∈ (runFrom p profile config).support, Successful terminal
  | _, _, .ret _, _, _, _, hconfig, _, terminal, hterminal => by
      rw [runFrom, runWith, FinDist.mem_support_pure] at hterminal
      exact hterminal ▸ hconfig
  | _, _, .sample sampleName _ _ k, profile, honest, config, hconfig, guards,
      terminal, hterminal => by
      rw [runFrom_sample, FinDist.support_bind] at hterminal
      obtain ⟨value, hvalue, hmem⟩ := Set.mem_iUnion₂.mp hterminal
      refine runFrom_successful k (afterSample profile) (fun who => honest who)
        (sampleSuccessor sampleName config value) ?_ (guards value hvalue) terminal hmem
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
        (commitSuccessor cellName guard config (.success value)) ?_
        (guards (.success value) hchoice) terminal hmem
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
      have haccepts := guards.1 value hbound
      refine runFrom_successful k (afterReveal profile)
        (fun who => ⟨(honest who).1, (honest who).2.2⟩)
        (revealSuccessor published source config true) ?_ (guards.2 true hdisclose)
        terminal hmem
      have hhead : (revealSuccessor published source config true).state.get
          (HasVar.here (x := published)) = .success value := by
        simp only [revealSuccessor, Env.cons_get_here, ite_true, hbound, haccepts]
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
    (state : State L Γ) (hstate : Successful state)
    (guards : GuardsAcceptFrom p profile ⟨state, [], Revelations.initial Γ, fun _ => []⟩) :
    ∀ terminal ∈ (run p profile state).support, Successful terminal :=
  runFrom_successful p profile honest ⟨state, [], Revelations.initial Γ, fun _ => []⟩
    hstate guards

end Vegas.SourceProgram
