module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Source.FailedBinding

@[expose] public section

/-! # Departures from intended play under arbitrary commitment admission

Irrevocable failed bindings, rejected values and withheld publications each
force a failed reveal of the deviating owner. This property uses the existing
source transitions and allows any choice of commitment admission at each site.
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def OwesFailure (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program) : Prop :=
  Indebted who program state ∨ FailedBinding who program state

theorem owesFailure_step (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (joint : Player → Option (OwnAction Player L)) (target : ProtocolState program)
    (owed : OwesFailure who program state) (reached : target ∈ (step program state joint).support) :
    OwesFailure who program target :=
  owed.elim (fun indebted => Or.inl (indebted_step who program state joint target indebted reached))
    (fun failed => Or.inr (failedBinding_step who program state joint target failed reached))

theorem failedReveals_pos_of_owesFailure (who : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (owed : OwesFailure who program state) {terminal : Config Player L program.terminalCtx}
    (read : readout program state = some terminal) :
    1 ≤ failedReveals program who (publicOutcome program terminal) :=
  owed.elim (fun indebted => failedReveals_pos_of_indebted who program state indebted read)
    (fun failed => failedReveals_pos_of_failedBinding who program state failed read)

/-- Every legal action outside the intended menu leaves an owner with an
unresolved failed binding or guard debt, including public omission. -/
theorem owesFailure_of_deviation (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (state : ProtocolState program) → Intended program state →
    (joint : Player → Option (OwnAction Player L)) → (action : OwnAction Player L) →
    joint who = some action →
    ProtocolView.actor who program (observe who program state) = some who →
    action ∈ ProtocolView.available who program admission (observe who program state) →
    action ∉ ProtocolView.intendedAvailable who program (observe who program state) →
    ∀ target ∈ (step program state joint).support, OwesFailure who program target
  | _, _, .ret _, _, _, _, _, _, _, acts, _, _, _, _ => by
      simp [ProtocolView.actor] at acts
  | _, _, .sample _ _ _ next, admission, state, intended, joint, action, chosen, acts,
      available, new, target, reached => by
      cases state with
      | inl _ => simp [ProtocolView.actor, observe] at acts
      | inr rest =>
          obtain ⟨after, supported, rfl⟩ := PMF.support_map .. ▸ reached
          exact owesFailure_of_deviation who next admission rest intended joint action
            chosen acts available new after supported
  | _, _, .commit (payload := payload) name owner fresh guard next, admission, state,
      intended, joint, action, chosen, acts, available, new, target, reached => by
      cases state with
      | inl config =>
          have same : owner = who := by
            simpa [ProtocolView.actor, observe, intended.1.not_defaulted owner] using acts
          subst who
          obtain ⟨choice, _admits, rfl⟩ := available
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst target
          rw [chosen, OwnAction.binding_commit]
          cases choice with
          | none => exact Or.inr (failedBinding_entry next _
              (Config.failedBinding_omission config intended.1.unique fresh guard _))
          | some result =>
              cases result with
              | failure => exact Or.inr (failedBinding_entry next _
                  (Config.failedBinding_commit config intended.1.unique fresh guard _))
              | success value =>
                  have rejected : guard.predicts (sourceObserve owner config.state) value =
                      false := by
                    have notIntended :
                        value ∉ intendedValues owner guard (sourceObserve owner config.state) :=
                      fun offered => new ⟨value, offered, rfl⟩
                    rw [mem_intendedValues_self guard _ intended.2.1] at notIntended
                    simpa using notIntended
                  exact Or.inl (indebted_entry next _
                    (intended.1.indebted_commit fresh guard value rejected))
      | inr rest =>
          obtain ⟨after, supported, rfl⟩ := PMF.support_map .. ▸ reached
          exact owesFailure_of_deviation who next (fun site => admission (some site))
            rest intended joint action chosen acts available new after supported
  | _, _, .reveal published owner name fresh source _ next, admission, state, intended,
      joint, action, chosen, acts, available, new, target, reached => by
      cases state with
      | inl config =>
          have same : owner = who := by
            simpa [ProtocolView.actor, observe, intended.1.not_defaulted owner] using acts
          subst who
          obtain ⟨disclose, rfl⟩ := available
          cases disclose with
          | true => exact (new rfl).elim
          | false =>
              have same := (PMF.mem_support_pure_iff _ _).mp reached
              subst target
              rw [chosen]
              refine Or.inl (Or.inl ⟨rfl, ?_⟩)
              rw [base_entry]
              exact revealSuccessor_result_of_withholding published source config
      | inr rest =>
          obtain ⟨after, supported, rfl⟩ := PMF.support_map .. ▸ reached
          rcases owesFailure_of_deviation who next admission rest intended.2 joint action
            chosen acts available new after supported with indebted | failed
          · exact Or.inl (Or.inr indebted)
          · exact Or.inr (Or.inr failed)

end Vegas.SourceProgram.ProtocolState

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

variable {Γ : SourceCtx Player L} {unresolved : Finset VarId} {config : Config Player L Γ}

omit [IExpr.ResultTypes L] in
/-- An intended configuration owes no failed reveal. -/
theorem Intended.not_indebted (intended : config.Intended unresolved) (who : Player) :
    ¬ config.Indebted who unresolved := by
  intro indebted
  obtain ⟨obligation, member, _, _, value, bound, rejects⟩ := indebted.pending
  rw [intended.predicted obligation member value bound] at rejects
  cases rejects

omit [IExpr.ResultTypes L] in
/-- An intended configuration has no failed binding. -/
theorem Intended.not_failedBinding (intended : config.Intended unresolved) (who : Player) :
    ¬ config.FailedBinding who unresolved := by
  intro failed
  obtain ⟨_, _, source, _, failure⟩ := failed.pending
  obtain ⟨value, success⟩ := intended.bound source
  rw [success] at failure
  cases failure

end Config

namespace ProtocolState

/-- A point of the intended game has no failed reveal or debt. -/
theorem Intended.not_indebted (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    Intended program state → ¬ Indebted who program state
  | _, _, .ret _, _, intended =>
      Config.Intended.not_indebted (unresolved := ∅) intended who
  | _, _, .sample _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_indebted intended.1 who
      | inr rest => exact Intended.not_indebted who next rest intended
  | _, _, .commit _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_indebted intended.1 who
      | inr rest => exact Intended.not_indebted who next rest intended
  | _, _, .reveal _ _ _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_indebted intended.1 who
      | inr rest =>
          rintro (⟨_, failure⟩ | indebted)
          · obtain ⟨value, success⟩ := intended.1
            rw [success] at failure
            cases failure
          · exact Intended.not_indebted who next rest intended.2 indebted

/-- A point of the intended game has no failed binding. -/
theorem Intended.not_failedBinding (who : Player) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (state : ProtocolState program) → Intended program state → ¬ FailedBinding who program state
  | _, _, .ret _, _, intended =>
      Config.Intended.not_failedBinding (unresolved := ∅) intended who
  | _, _, .sample _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_failedBinding intended.1 who
      | inr rest => exact Intended.not_failedBinding who next rest intended
  | _, _, .commit _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_failedBinding intended.1 who
      | inr rest => exact Intended.not_failedBinding who next rest intended
  | _, _, .reveal _ _ _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_failedBinding intended.1 who
      | inr rest =>
          rintro (⟨_, failure⟩ | failed)
          · obtain ⟨value, success⟩ := intended.1
            rw [success] at failure
            cases failure
          · exact Intended.not_failedBinding who next rest intended.2 failed

/-- **Intended points owe nothing.** No player owes a failure at a point of the
intended game. -/
theorem Intended.not_owesFailure (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (intended : Intended program state) : ¬ OwesFailure who program state := by
  rintro (indebted | failed)
  · exact Intended.not_indebted who program state intended indebted
  · exact Intended.not_failedBinding who program state intended failed

end ProtocolState

end Vegas.SourceProgram
