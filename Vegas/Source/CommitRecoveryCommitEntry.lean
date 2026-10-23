/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProtocolSuffix

/-! # The actual residual constructor at a committing source point -/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A committing point is an entry configuration of an actual syntactic
commitment suffix, with fresh context names inherited from the whole program. -/
theorem exists_committing_entry :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program),
      (Γ.map Prod.fst).Nodup → atCommit program point = true →
      ∃ (Δ : SourceCtx Player L) (P : Finset VarId) (name : VarId) (owner : Player)
        (payload : L.Ty) (fresh : name ∉ Δ.map Prod.fst)
        (guard : SourceGuard L Δ owner name payload)
        (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ)
          (insert name P))
        (lift : ProtocolState (.commit name owner fresh guard next) → ProtocolState program)
        (entry : Config Player L Δ),
        ProtocolSuffix program (.commit name owner fresh guard next) lift ∧
        point = lift (ProtocolState.entry (.commit name owner fresh guard next) entry) ∧
        (Δ.map Prod.fst).Nodup
  | _, _, .ret _, _, _, committing => by cases committing
  | _, _, .sample name fresh law next, point, unique, committing => by
      cases point with
      | inl config => cases committing
      | inr point =>
          obtain ⟨Δ, P, selected, owner, payload, selectedFresh, guard, tail, lift, entry,
            origin, atEntry, names⟩ := exists_committing_entry next point
              (List.nodup_cons.mpr ⟨fresh, unique⟩) committing
          refine ⟨Δ, P, selected, owner, payload, selectedFresh, guard, tail,
            (fun result => Sum.inr (lift result)), entry, ?_, congrArg Sum.inr atEntry, names⟩
          exact (ProtocolSuffix.sampleTail fresh law next .initial).compose origin
  | _, _, .commit name owner fresh guard next, point, unique, committing => by
      cases point with
      | inl config =>
          exact ⟨_, _, name, owner, _, fresh, guard, next, id, config, .initial, rfl, unique⟩
      | inr point =>
          obtain ⟨Δ, P, selected, actor, payload, selectedFresh, selectedGuard, tail, lift,
            entry, origin, atEntry, names⟩ := exists_committing_entry next point
              (List.nodup_cons.mpr ⟨fresh, unique⟩) committing
          refine ⟨Δ, P, selected, actor, payload, selectedFresh, selectedGuard, tail,
            (fun result => Sum.inr (lift result)), entry, ?_, congrArg Sum.inr atEntry, names⟩
          exact (ProtocolSuffix.commitTail fresh guard next .initial).compose origin
  | _, _, .reveal published owner name fresh selected unresolved next, point, unique,
      committing => by
      cases point with
      | inl config => cases committing
      | inr point =>
          obtain ⟨Δ, P, chosen, actor, payload, chosenFresh, guard, tail, lift, entry,
            origin, atEntry, names⟩ := exists_committing_entry next point
              (List.nodup_cons.mpr ⟨fresh, unique⟩) committing
          refine ⟨Δ, P, chosen, actor, payload, chosenFresh, guard, tail,
            (fun result => Sum.inr (lift result)), entry, ?_, congrArg Sum.inr atEntry, names⟩
          exact (ProtocolSuffix.revealTail fresh selected unresolved next .initial).compose origin

end Vegas.SourceProgram.ProtocolState
