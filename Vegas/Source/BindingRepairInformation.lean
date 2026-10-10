/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ValueBindingContinuation
import Vegas.Source.Protocol

/-! # Full foreign information across repaired source commitments

A failed commitment has a value-interface successor with the same information
for every other player, including that player's entire original action recall.
The claim is local to a focal owner's repair: another player's own failed
commitment is observable to that player and cannot be silently represented.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
theorem Patched.foreign_view_eq {Γ : SourceCtx Player L} {who observer : Player}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ}
    {original repaired : Config Player L Γ}
    (related : Patched unpatch patched original.state repaired.state
      original.history repaired.history)
    (foreign : observer ≠ who) : repaired.view observer = original.view observer := by
  exact Prod.ext
    (sourceObserve_congr observer repaired.state original.state related.publicEq
      related.publicationEq related.inputEq (fun cell => related.foreignEq cell foreign))
    (related.historyEq observer foreign)

omit [IExpr.ResultTypes L] in
theorem commitSuccessor_foreign_view_eq {Γ : SourceCtx Player L} {owner observer : Player}
    {payload : L.Ty} (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (config : Config Player L Γ) (first second : PublicationResult (L.Val payload))
    (foreign : observer ≠ owner) :
    (commitSuccessor name guard config first).view observer =
      (commitSuccessor name guard config second).view observer := by
  apply Prod.ext
  · apply congrArg SourceObservation.mk
    funext cellName cell selected
    cases selected with
    | here =>
        change (if owner = observer then some _ else none) =
          (if owner = observer then some _ else none)
        simp [Ne.symm foreign]
    | there prior => cases cell <;> simp [commitSuccessor]
  · simp only [Config.view, commitSuccessor, Function.update_of_ne foreign]

/-- Both successors are actual legal protocol histories. Only the focal
owner's newly bound value and own commitment action differ. -/
theorem exists_values_history_after_failed_commit {Γ : SourceCtx Player L}
    {O : Finset VarId} {owner : Player} {payload : L.Ty}
    (name : VarId) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (admission : CommitmentInterface (.commit name owner fresh guard next))
    (forfeiture : admission none = .forfeiture) (config : Config Player L Γ) :
    let program := SourceProgram.commit name owner fresh guard next
    ∃ original : (executionProtocol program admission config).History,
      original.state = Sum.inr (ProtocolState.entry next
        (commitSuccessor name guard config .failure)) ∧
      ∃ repaired : (executionProtocol program (CommitmentInterface.values program) config).History,
        repaired.state = Sum.inr (ProtocolState.entry next
          (commitSuccessor name guard config (.success (L.someValue payload)))) ∧
        repaired.trace.length = original.trace.length ∧
        ∀ observer, observer ≠ owner →
          (informationModel program (CommitmentInterface.values program) config).infoOf
            observer repaired.trace =
          (informationModel program admission config).infoOf observer original.trace := by
  dsimp only
  let program := SourceProgram.commit name owner fresh guard next
  let joint (result : PublicationResult (L.Val payload)) : Player → Option (OwnAction Player L) :=
    fun who => if who = owner then some (.commit owner name payload result) else none
  have legal (interface : CommitmentInterface program) (result : PublicationResult (L.Val payload))
      (admitted : (interface none).Admits result) :
      (executionProtocol program interface config).Legal
        (ProtocolState.entry program config) (joint result) := by
    refine ⟨by simp [program, executionProtocol, ProtocolState.entry, ProtocolState.terminal], ?_⟩
    intro who
    by_cases same : who = owner
    · subst who
      simp only [joint, ↓reduceIte, executionProtocol, program, ProtocolState.entry,
        ProtocolState.observe, Sum.elim_inl, ProtocolView.actor, ProtocolView.available]
      exact ⟨trivial, result, admitted, rfl⟩
    · simp [joint, same, executionProtocol, program, ProtocolState.entry,
        ProtocolState.observe, ProtocolView.actor, Ne.symm same]
  have reached (interface : CommitmentInterface program) (result : PublicationResult (L.Val
    payload))
      (admitted : (interface none).Admits result) :
      Sum.inr (ProtocolState.entry next (commitSuccessor name guard config result)) ∈
        ((executionProtocol program interface config).step
          (ProtocolState.entry program config) ⟨joint result, legal interface result
            admitted⟩).support := by
    simp only [executionProtocol, program, ProtocolState.entry, ProtocolState.step,
      Sum.elim_inl, joint, ↓reduceIte, OwnAction.binding_commit]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  let original := (executionProtocol program admission config).initHistory.extend
    (legal admission .failure forfeiture) (reached admission .failure forfeiture)
  let repaired := (executionProtocol program
    (CommitmentInterface.values program) config).initHistory.extend
      (legal _ (.success (L.someValue payload)) trivial)
      (reached _ (.success (L.someValue payload)) trivial)
  refine ⟨original, rfl, repaired, rfl, rfl, ?_⟩
  intro observer foreign
  change ProtocolState.observe observer program repaired.state =
    ProtocolState.observe observer program original.state
  change Sum.inr (ProtocolState.observe observer next
    (ProtocolState.entry next (commitSuccessor name guard config
      (.success (L.someValue payload))))) =
    Sum.inr (ProtocolState.observe observer next
      (ProtocolState.entry next (commitSuccessor name guard config .failure)))
  have observation := commitSuccessor_foreign_view_eq name guard config
    (.success (L.someValue payload)) .failure foreign
  have entry_observation {Δ : SourceCtx Player L} {U : Finset VarId}
      (suffix : SourceProgram Player L Δ U) (first second : Config Player L Δ)
      (equal : first.view observer = second.view observer) :
      ProtocolState.observe observer suffix (ProtocolState.entry suffix first) =
        ProtocolState.observe observer suffix (ProtocolState.entry suffix second) := by
    cases suffix <;> simp only [ProtocolState.entry, ProtocolState.observe, Sum.elim_inl]
      <;> rw [equal]
  exact congrArg Sum.inr (entry_observation next _ _ observation)

end Vegas.SourceProgram
