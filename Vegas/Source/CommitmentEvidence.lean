/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Protocol

/-! # Source-level evidence of a committed value

An opening certifies the immutable binding, independently of the guard's
publication verdict. Private initial inputs supply no such certificate.
Evidence uses source names and typed values; it contains no runtime handle.
-/

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

structure CommitmentEvidence (Player : Type) (L : IExpr) where
  owner : Player
  name : VarId
  payload : L.Ty
  value : L.Val payload

namespace CommitmentEvidence

def Holds (fact : CommitmentEvidence Player L) {Γ : SourceCtx Player L} (state : State L Γ) :
    Prop :=
  ∃ ref : HasVar Γ fact.name (.commitment fact.owner fact.payload),
    state.get ref = .success fact.value

def Possessed (fact : CommitmentEvidence Player L) (who : Player) {Γ : SourceCtx Player L}
    (view : SourceObservation L who Γ) : Prop :=
  fact.owner = who ∧ ∃ ref : HasVar Γ fact.name (.commitment fact.owner fact.payload),
    view.cells.get ref = some (.success fact.value)

omit [IExpr.ResultTypes L] in
theorem possessed_sound (fact : CommitmentEvidence Player L) (who : Player)
    {Γ : SourceCtx Player L} (state : State L Γ)
    (known : fact.Possessed who (sourceObserve who state)) : fact.Holds state := by
  obtain ⟨owner, ref, stored⟩ := known
  refine ⟨ref, ?_⟩
  change (if fact.owner = who then some (state.get ref) else none) =
    some (.success fact.value) at stored
  simpa only [owner, ↓reduceIte, Option.some.injEq] using stored

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem holds_cons (fact : CommitmentEvidence Player L) {Γ : SourceCtx Player L}
    (state : State L Γ) (known : fact.Holds state) (name : VarId) (cell : CellTy Player L)
    (value : CellVal L cell) : fact.Holds (Γ := (name, cell) :: Γ) (Env.cons value state) := by
  obtain ⟨ref, stored⟩ := known
  exact ⟨.there ref, stored⟩

end CommitmentEvidence

namespace ProtocolState

def evidenceHolds : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program →
    CommitmentEvidence Player L → Prop
  | _, _, .ret _, config, fact => fact.Holds config.state
  | _, _, .sample _ _ _ next, state, fact =>
      state.elim (fun config => fact.Holds config.state) (fun rest => evidenceHolds next rest fact)
  | _, _, .commit _ _ _ _ next, state, fact =>
      state.elim (fun config => fact.Holds config.state) (fun rest => evidenceHolds next rest fact)
  | _, _, .reveal _ _ _ _ _ _ next, state, fact =>
      state.elim (fun config => fact.Holds config.state) (fun rest => evidenceHolds next rest fact)

@[simp] theorem evidenceHolds_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ)
    (fact : CommitmentEvidence Player L) :
    evidenceHolds program (entry program config) fact ↔ fact.Holds config.state := by
  cases program <;> rfl

end ProtocolState

namespace ProtocolView

def possessesEvidence (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program →
    CommitmentEvidence Player L → Prop
  | _, _, .ret _, view, fact => fact.Possessed who view.1
  | _, _, .sample _ _ _ next, view, fact =>
      view.elim (fun current => fact.Possessed who current.1)
        (fun rest => possessesEvidence who next rest fact)
  | _, _, .commit _ _ _ _ next, view, fact =>
      view.elim (fun current => fact.Possessed who current.1)
        (fun rest => possessesEvidence who next rest fact)
  | _, _, .reveal _ _ _ _ _ _ next, view, fact =>
      view.elim (fun current => fact.Possessed who current.1)
        (fun rest => possessesEvidence who next rest fact)

theorem possessesEvidence_sound (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (fact : CommitmentEvidence Player L) →
    possessesEvidence who program (ProtocolState.observe who program state) fact →
      ProtocolState.evidenceHolds program state fact
  | _, _, .ret _, config, fact, known => fact.possessed_sound who config.state known
  | _, _, .sample _ _ _ next, state, fact, known => by
      cases state with
      | inl config => exact fact.possessed_sound who config.state known
      | inr rest => exact possessesEvidence_sound who next rest fact known
  | _, _, .commit _ _ _ _ next, state, fact, known => by
      cases state with
      | inl config => exact fact.possessed_sound who config.state known
      | inr rest => exact possessesEvidence_sound who next rest fact known
  | _, _, .reveal _ _ _ _ _ _ next, state, fact, known => by
      cases state with
      | inl config => exact fact.possessed_sound who config.state known
      | inr rest => exact possessesEvidence_sound who next rest fact known

end ProtocolView

namespace ProtocolState

open GameTheory.Math.Probability

theorem evidenceHolds_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state target : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) →
    target ∈ (step program state joint).support → (fact : CommitmentEvidence Player L) →
    evidenceHolds program state fact → evidenceHolds program target fact
  | _, _, .ret _, state, target, joint, reached, fact, known => by
      cases FinDist.mem_support_pure.mp reached
      exact known
  | _, _, .sample name _ law next, state, target, joint, reached, fact, known => by
      cases state with
      | inl config =>
          obtain ⟨value, _, rfl⟩ := FinDist.support_map .. ▸ reached
          apply (evidenceHolds_entry next _ fact).mpr
          exact fact.holds_cons config.state known name (.publicData _) value
      | inr rest =>
          obtain ⟨after, selected, rfl⟩ := FinDist.support_map .. ▸ reached
          exact evidenceHolds_step next rest after joint selected fact known
  | _, _, .commit name owner _ guard next, state, target, joint, reached, fact, known => by
      cases state with
      | inl config =>
          cases FinDist.mem_support_pure.mp reached
          apply (evidenceHolds_entry next _ fact).mpr
          exact fact.holds_cons config.state known name _ _
      | inr rest =>
          obtain ⟨after, selected, rfl⟩ := FinDist.support_map .. ▸ reached
          exact evidenceHolds_step next rest after joint selected fact known
  | _, _, .reveal published owner name _ source _ next,
      state, target, joint, reached, fact, known => by
      cases state with
      | inl config =>
          cases FinDist.mem_support_pure.mp reached
          apply (evidenceHolds_entry next _ fact).mpr
          exact fact.holds_cons config.state known published _ _
      | inr rest =>
          obtain ⟨after, selected, rfl⟩ := FinDist.support_map .. ▸ reached
          exact evidenceHolds_step next rest after joint selected fact known

/-- Disclosing an openable binding emits its value even when guard validation
fails. Withholding and unopenable bindings emit no certificate. -/
def disclosedEvidence : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program →
    (Player → Option (OwnAction Player L)) → List (CommitmentEvidence Player L)
  | _, _, .ret _, _, _ => []
  | _, _, .sample _ _ _ next, state, joint =>
      state.elim (fun _ => []) (fun rest => disclosedEvidence next rest joint)
  | _, _, .commit _ _ _ _ next, state, joint =>
      state.elim (fun _ => []) (fun rest => disclosedEvidence next rest joint)
  | _, _, .reveal _ owner name _ source _ next, state, joint =>
      state.elim (fun config => if OwnAction.disclosure (joint owner) then
        match config.state.get source with
        | .failure => []
        | .success value => [⟨owner, name, _, value⟩]
        else []) (fun rest => disclosedEvidence next rest joint)

theorem disclosedEvidence_sound : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state target : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) →
    target ∈ (step program state joint).support → (fact : CommitmentEvidence Player L) →
    fact ∈ disclosedEvidence program state joint → evidenceHolds program target fact
  | _, _, .ret _, _, _, _, _, _, member => False.elim (List.not_mem_nil member)
  | _, _, .sample _ _ _ next, state, target, joint, reached, fact, member => by
      cases state with
      | inl config => exact False.elim (List.not_mem_nil member)
      | inr rest =>
          obtain ⟨after, selected, rfl⟩ := FinDist.support_map .. ▸ reached
          exact disclosedEvidence_sound next rest after joint selected fact member
  | _, _, .commit _ _ _ _ next, state, target, joint, reached, fact, member => by
      cases state with
      | inl config => exact False.elim (List.not_mem_nil member)
      | inr rest =>
          obtain ⟨after, selected, rfl⟩ := FinDist.support_map .. ▸ reached
          exact disclosedEvidence_sound next rest after joint selected fact member
  | _, _, .reveal published owner name _ source _ next,
      state, target, joint, reached, fact, member => by
      cases state with
      | inl config =>
          cases FinDist.mem_support_pure.mp reached
          change fact ∈ (if OwnAction.disclosure (joint owner) then _ else []) at member
          split at member
          · cases stored : config.state.get source with
            | failure => simp [stored] at member
            | success value =>
                simp only [stored, List.mem_singleton] at member
                subst fact
                apply (evidenceHolds_entry next _ _).mpr
                exact ⟨.there source, stored⟩
          · exact False.elim (List.not_mem_nil member)
      | inr rest =>
          obtain ⟨after, selected, rfl⟩ := FinDist.support_map .. ▸ reached
          exact disclosedEvidence_sound next rest after joint selected fact member

end ProtocolState
end Vegas.SourceProgram
