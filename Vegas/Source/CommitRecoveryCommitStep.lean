/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBlockEmbedding

/-! # Legal commitment instructions lifted into the actual recovery protocol -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {whole : SourceProgram Player L Γ O}

/-- The original one-owner recovery instruction, retaining its actual omission
marker. An already excluded owner supplies no original action. -/
def commitJoint (state : CommitRecoveryState whole) (owner : Player) (name : VarId)
    (payload : L.Ty) (choice : PublicationResult (L.Val payload)) (missed : Bool) :
    Player → Option (CommitRecoveryMove Player L) :=
  fun who => if who = owner ∧ owner ∉ state.excluded then
    some ⟨.commit owner name payload choice, missed⟩ else none

/-- A supported raw instruction gives the exact automatically closed successor. -/
theorem step_contains_close (state : CommitRecoveryState whole)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState whole × Finset Player) (monotone : state.excluded ⊆ result.2)
    (reached : result ∈
      (ProtocolState.recoveryStep whole state.point state.excluded joint).support) :
    (state.install result monotone).close ∈ (state.step joint).support := by
  let raw := ProtocolState.recoveryStep whole state.point state.excluded joint
  let keep := fun result (supported : result ∈ raw.support) =>
    ProtocolState.recoveryStep_excluded_monotone whole state.point state.excluded joint
      result supported
  change result ∈ raw.support at reached
  rw [← map_val_pmfToSubtype raw keep] at reached
  obtain ⟨tagged, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  change _ ∈ ((pmfToSubtype raw keep).map _).support
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨tagged, member, by cases same; rfl⟩

end CommitRecoveryState

/-- The lift hypotheses are local structural adapters: current rank, actor,
available typed moves and the original raw kernel. No path is assumed. -/
theorem lifted_commit_successor
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) (initial : Config Player L wholeΓ)
    {name : VarId} {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState whole)
    (ranks : ∀ point, ProtocolState.remaining whole (lift point) =
      ProtocolState.remaining (.commit name owner fresh guard tail) point)
    (actors : ∀ point, ProtocolState.actor whole (lift point) =
      ProtocolState.actor (.commit name owner fresh guard tail) point)
    (menus : ∀ point who, ProtocolView.recoveryAvailable who whole
      (ProtocolState.observe who whole (lift point)) =
      ProtocolView.recoveryAvailable who (.commit name owner fresh guard tail)
        (ProtocolState.observe who (.commit name owner fresh guard tail) point))
    (steps : ∀ point excluded joint, ProtocolState.recoveryStep whole (lift point) excluded joint =
      (ProtocolState.recoveryStep (.commit name owner fresh guard tail) point excluded joint).map
        (fun result => (lift result.1, result.2)))
    (config : Config Player L Γ) (state : CommitRecoveryState whole)
    (atEntry : state.point = lift (Sum.inl config))
    (choice : PublicationResult (L.Val payload)) (missed : Bool)
    (missingFailure : missed = true → choice = .failure) :
    let inactive := owner ∈ state.excluded
    let nextConfig := if inactive then automaticCommit name owner payload config
      else commitSuccessor name guard config choice
    let excluded := if inactive then state.excluded else excludeCommit state.excluded owner missed
    let joint := state.commitJoint owner name payload choice missed
    ∃ monotone : state.excluded ⊆ excluded,
      ∃ legal : (commitRecoveryProtocol whole initial).Legal state joint,
        (state.install (lift (Sum.inr (ProtocolState.entry tail nextConfig)), excluded)
          monotone).close ∈
          ((commitRecoveryProtocol whole initial).step state ⟨joint, legal⟩).support := by
  classical
  dsimp only
  let move : CommitRecoveryMove Player L := ⟨.commit owner name payload choice, missed⟩
  let joint := state.commitJoint owner name payload choice missed
  have acting : ProtocolState.actor whole state.point = some owner := by
    rw [atEntry, actors]
    rfl
  have legal : (commitRecoveryProtocol whole initial).Legal state joint := by
    constructor
    · intro stopped
      have zero := (ProtocolState.remaining_zero_iff_terminal whole state.point).mpr stopped
      rw [atEntry, ranks] at zero
      change instructionCount tail + 1 = 0 at zero
      omega
    · intro who
      by_cases chosen : who = owner ∧ owner ∉ state.excluded
      · rw [show joint who = some move from ite_eq_left chosen]
        obtain ⟨same, active⟩ := chosen
        subst who
        refine ⟨⟨acting, active⟩, ?_⟩
        change move ∈ ProtocolView.recoveryAvailable owner whole
          (ProtocolState.observe owner whole state.point)
        rw [atEntry, menus]
        refine ⟨⟨choice, ?_, rfl⟩, ?_⟩
        · cases choice <;> trivial
        · intro missing
          change choice = .failure
          exact missingFailure missing
      · rw [show joint who = none from ite_eq_right chosen]
        intro active
        apply chosen
        exact ⟨Option.some.inj (active.1.symm.trans acting), by
          have same := Option.some.inj (active.1.symm.trans acting)
          exact same ▸ active.2⟩
  have monotone : state.excluded ⊆
      (if owner ∈ state.excluded then state.excluded
        else excludeCommit state.excluded owner missed) := by
    split
    · exact Finset.Subset.refl _
    · unfold excludeCommit
      split
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
  refine ⟨monotone, legal, state.step_contains_close joint _ monotone ?_⟩
  rw [atEntry, steps]
  by_cases inactive : owner ∈ state.excluded
  · simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte, PMF.pure_map,
      PMF.mem_support_pure_iff]
  · have chosen : joint owner = some move := ite_eq_left ⟨rfl, inactive⟩
    simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte, chosen,
      Option.map_some, move, OwnAction.binding_commit, CommitRecoveryMove.missed, Option.elim_some,
      PMF.pure_map, PMF.mem_support_pure_iff, excludeCommit]

end Vegas.SourceProgram
