/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.SetupProtocol

/-! # Public absorbing defaults along source protocol steps -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

/-- The complete public default record visible at the current program point. -/
def defaults (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program → DefaultHistory Player
  | _, _, .ret _ => DecisionView.defaults
  | _, _, .sample _ _ _ next => Sum.elim DecisionView.defaults (defaults who next)
  | _, _, .commit _ _ _ _ next => Sum.elim DecisionView.defaults (defaults who next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim DecisionView.defaults (defaults who next)

/-- The same public default status at every source program point. -/
def defaulted (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program → Finset Player
  | _, _, .ret _ => fun view => DecisionView.defaulted view
  | _, _, .sample _ _ _ next => Sum.elim DecisionView.defaulted (defaulted who next)
  | _, _, .commit _ _ _ _ next => Sum.elim DecisionView.defaulted (defaulted who next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim DecisionView.defaulted (defaulted who next)

end ProtocolView

namespace ProtocolState

/-- The complete public default record retained by the current configuration. -/
def defaults : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → DefaultHistory Player
  | _, _, .ret _ => Config.defaults
  | _, _, .sample _ _ _ next => Sum.elim Config.defaults (defaults next)
  | _, _, .commit _ _ _ _ next => Sum.elim Config.defaults (defaults next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim Config.defaults (defaults next)

@[simp] theorem defaults_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    defaults program (entry program config) = config.defaults := by cases program <;> rfl

/-- Every player observes the same complete public default record. -/
theorem defaults_observe (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    ProtocolView.defaults who program (observe who program state) = defaults program state
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl _ => rfl
      | inr rest => exact defaults_observe who next rest
  | _, _, .commit _ _ _ _ next, state => by
      cases state with
      | inl _ => rfl
      | inr rest => exact defaults_observe who next rest
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl _ => rfl
      | inr rest => exact defaults_observe who next rest

/-- Removing the newest public entry recovers the record before a nonterminal step. -/
theorem defaults_back_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (before after : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → ¬ terminal program before →
    after ∈ (step program before joint).support →
    (defaults program after).back = defaults program before
  | _, _, .ret _, _, _, _, running, _ => (running trivial).elim
  | _, _, .sample _ _ _ next, before, after, joint, running, reached => by
      cases before with
      | inl config =>
          obtain ⟨value, _, rfl⟩ := PMF.support_map .. ▸ reached
          simp only [defaults, Sum.elim_inl, Sum.elim_inr, defaults_entry,
            sampleSuccessor, DefaultHistory.back_record]
      | inr rest =>
          obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
          exact defaults_back_step next rest target joint running supported
  | _, _, .commit _ _ _ _ next, before, after, joint, running, reached => by
      cases before with
      | inl config =>
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst after
          simp only [defaults, Sum.elim_inl, Sum.elim_inr, defaults_entry,
            commitSuccessor, DefaultHistory.back_record]
      | inr rest =>
          obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
          exact defaults_back_step next rest target joint running supported
  | _, _, .reveal _ _ _ _ _ _ next, before, after, joint, running, reached => by
      cases before with
      | inl config =>
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst after
          simp only [defaults, Sum.elim_inl, Sum.elim_inr, defaults_entry,
            revealSuccessor, DefaultHistory.back_record]
      | inr rest =>
          obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
          exact defaults_back_step next rest target joint running supported

/-- Public absorbing defaults at the current source program point. -/
def defaulted : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Finset Player
  | _, _, .ret _ => fun config => Config.defaulted config
  | _, _, .sample _ _ _ next => Sum.elim Config.defaulted (defaulted next)
  | _, _, .commit _ _ _ _ next => Sum.elim Config.defaulted (defaulted next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim Config.defaulted (defaulted next)

@[simp] theorem defaulted_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    defaulted program (entry program config) = config.defaulted := by
  cases program <;> rfl

/-- Every player observes the complete public default status. -/
theorem defaulted_observe (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    ProtocolView.defaulted who program (observe who program state) = defaulted program state
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl config => rfl
      | inr rest => exact defaulted_observe who next rest
  | _, _, .commit _ _ _ _ next, state => by
      cases state with
      | inl config => rfl
      | inr rest => exact defaulted_observe who next rest
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl config => rfl
      | inr rest => exact defaulted_observe who next rest

/-- Even arbitrary joint actions cannot restore a publicly defaulted player. -/
theorem defaulted_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (before after : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) →
    after ∈ (step program before joint).support →
      defaulted program before ⊆ defaulted program after
  | _, _, .ret _, before, after, joint, reached => by
      have same := (PMF.mem_support_pure_iff _ _).mp reached
      subst after
      exact Finset.Subset.refl _
  | _, _, .sample _ _ _ next, before, after, joint, reached => by
      cases before with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          simpa only [defaulted, Sum.elim_inl, Sum.elim_inr, defaulted_entry,
            sampleSuccessor_defaulted] using Finset.Subset.refl config.defaulted
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨target, supported, rfl⟩ := reached
          exact defaulted_step next rest target joint supported
  | _, _, .commit name owner _ guard next, before, after, joint, reached => by
      cases before with
      | inl config =>
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst after
          simpa only [defaulted, Sum.elim_inl, Sum.elim_inr, defaulted_entry] using
            commitSuccessor_defaulted_mono name guard config
              (OwnAction.binding owner name _ (joint owner))
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨target, supported, rfl⟩ := reached
          exact defaulted_step next rest target joint supported
  | _, _, .reveal published owner name _ source _ next, before, after, joint, reached => by
      cases before with
      | inl config =>
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst after
          simpa only [defaulted, Sum.elim_inl, Sum.elim_inr, defaulted_entry] using
            revealSuccessor_defaulted_mono published source config
              (OwnAction.disclosure (joint owner))
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨target, supported, rfl⟩ := reached
          exact defaulted_step next rest target joint supported

end ProtocolState

namespace Setup

/-- The public default record, empty before the initial source draw. -/
def protocolDefaults (setup : Setup (Player := Player) (L := L)) :
    setup.ProtocolState → DefaultHistory Player
  | none => ⟨[]⟩
  | some state => ProtocolState.defaults setup.program state

/-- One completed source instruction adds one public entry; setup starts with none. -/
theorem protocolDefaults_back_step (setup : Setup (Player := Player) (L := L))
    (before after : setup.ProtocolState) (joint : Player → Option (OwnAction Player L))
    (running : ¬ before.elim False (ProtocolState.terminal setup.program))
    (reached : after ∈ (setup.protocolStep before joint).support) :
    (setup.protocolDefaults after).back = setup.protocolDefaults before := by
  cases before with
  | none =>
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ reached
      simp only [protocolDefaults, ProtocolState.defaults_entry, Config.initial,
        DefaultHistory.back, List.tail_nil]
  | some state =>
      obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact ProtocolState.defaults_back_step setup.program state target joint running supported


end Setup

end Vegas.SourceProgram
