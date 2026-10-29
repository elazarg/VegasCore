/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Disclosure

/-! # Honest play publishes what it bound

An honest policy binds a value at every commitment it owns and opens at every
reveal it owns. Public omission and accepted unusable bindings are both excluded
from an honest active commitment.

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

/-- Every active own commitment submits a value, and every active own reveal opens. -/
def Honest {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → BehavioralPolicy who program → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ next, policy => Honest next policy
  | _, _, .commit _ owner _ _ next, policy =>
      (∀ (own : owner = who) view active choice, choice ∈ (policy.1 own view active).support →
        ∃ value, choice = some (.success value)) ∧ Honest next policy.2
  | _, _, .reveal _ _ _ _ _ _ next, policy =>
      (∀ own view active, false ∉ (policy.1 own view active).support) ∧ Honest next policy.2

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
      ∀ choice ∈ (if inactive : owner ∈ config.defaulted then PMF.pure none
          else commitKernel profile (config.view owner) inactive).support,
        GuardsAcceptFrom k (afterCommit profile) (commitSuccessor cellName guard config choice)
  | _, _, .reveal published owner _ _ source _ k, profile, config =>
      (∀ value, config.state.get source = .success value →
        (Registry.completedBy (published := published) config.registry config.revelations
          source).all (·.accepts (Revelations.reveal config.revelations source)
            (Env.cons (.success value) config.state)) = true) ∧
      ∀ disclose ∈ (if inactive : owner ∈ config.defaulted then PMF.pure false
          else revealKernel profile (config.view owner) inactive).support,
        GuardsAcceptFrom k (afterReveal profile)
          (revealSuccessor published source config disclose)

private theorem runFrom_successful :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (profile : BehavioralProfile program) → (∀ who, Honest program (profile who)) →
    (config : Config Player L Γ) → Successful config.state → config.defaulted = ∅ →
    GuardsAcceptFrom program profile config →
    ∀ terminal ∈ (runFrom program profile config).support,
      Successful terminal.state ∧ terminal.defaulted = ∅
  | _, _, .ret _, _, _, _, successful, clear, _, terminal, reached => by
      rw [runFrom, PMF.mem_support_pure_iff] at reached
      subst terminal
      exact ⟨successful, clear⟩
  | _, _, .sample name _ _ next, profile, honest, config, successful, clear, guards,
      terminal, reached => by
      rw [runFrom_sample, PMF.support_bind] at reached
      obtain ⟨value, supported, continued⟩ := Set.mem_iUnion₂.mp reached
      exact runFrom_successful next (afterSample profile) honest
        (sampleSuccessor name config value)
        { bindings := fun member => match member with
            | .there prior => successful.bindings prior
          publications := fun member => match member with
            | .there prior => successful.publications prior }
        clear (guards value supported) terminal continued
  | _, _, .commit name owner _ guard next, profile, honest, config, successful, clear,
      guards, terminal, reached => by
      have active : owner ∉ config.defaulted := by simp [clear]
      rw [runFrom_commit, dite_eq_right active, PMF.support_bind] at reached
      obtain ⟨choice, supported, continued⟩ := Set.mem_iUnion₂.mp reached
      obtain ⟨value, rfl⟩ := (honest owner).1 rfl (config.view owner) active choice supported
      apply runFrom_successful next (afterCommit profile) (fun player => (honest player).2)
        (commitSuccessor name guard config (some (.success value)))
        ?_ ?_ (guards _ (by simpa only [dite_eq_right active] using supported)) terminal continued
      · exact
          { bindings := fun member => by
              cases member with
              | here => exact ⟨value, by simp [commitSuccessor, active]⟩
              | there prior => exact successful.bindings prior
            publications := fun member => match member with
              | .there prior => successful.publications prior }
      · rw [commitSuccessor_defaulted_of_accepted, clear]
  | _, _, .reveal published owner _ _ selected _ next, profile, honest, config,
      successful, clear, guards, terminal, reached => by
      have active : owner ∉ config.defaulted := by simp [clear]
      rw [runFrom_reveal, dite_eq_right active, PMF.support_bind] at reached
      obtain ⟨disclose, supported, continued⟩ := Set.mem_iUnion₂.mp reached
      have opens : disclose = true := by
        cases disclose with
        | false => exact ((honest owner).1 rfl (config.view owner) active supported).elim
        | true => rfl
      subst disclose
      obtain ⟨value, bound⟩ := successful.bindings selected
      have accepted := guards.1 value bound
      have head : (revealSuccessor published selected config true).state.get .here =
          .success value := by
        simp only [revealSuccessor, active, ite_false, ite_true, bound, accepted,
          Env.cons_get_here]
      apply runFrom_successful next (afterReveal profile) (fun player => (honest player).2)
        (revealSuccessor published selected config true) ?_ ?_
        (guards.2 true (by simpa only [dite_eq_right active] using supported)) terminal continued
      · exact
          { bindings := fun member => match member with
              | .there prior => successful.bindings prior
            publications := fun member => match member with
              | .here => ⟨value, head⟩
              | .there prior => successful.publications prior }
      · unfold Config.defaulted
        rw [revealSuccessor_defaults, head]
        simpa only [PublicationResult.isFailure, Bool.false_eq_true, ite_false, ite_self,
          DefaultHistory.defaulted_record_none, Config.defaulted] using clear

/-- Honest play with accepting guards preserves every successful typed cell
and keeps every player active throughout initialized execution. -/
theorem run_successful {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (honest : ∀ who, Honest program (profile who))
    (state : State L Γ) (successful : Successful state)
    (guards : GuardsAcceptFrom program profile (Config.initial state)) :
    ∀ terminal ∈ (run program profile state).support,
      Successful terminal.state ∧ terminal.defaulted = ∅ :=
  runFrom_successful program profile honest (Config.initial state) successful rfl guards

end Vegas.SourceProgram
