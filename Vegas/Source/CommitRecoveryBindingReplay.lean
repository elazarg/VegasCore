/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryVirtualView
import Vegas.Source.CommitRecoveryValueMenu
import GameTheoryExtensions.Protocol.MenuRestriction

/-! # Supported virtual replacements at actual recovery callbacks -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryMove

/-- The canonical virtual domain value is assigned to an accepted unusable
binding. Actual missing bindings are kept distinct. -/
def repairAtom (owner who : Player) (payload : L.Ty)
    (atom : L.Val payload ⊕ Bool) : L.Val payload ⊕ Bool :=
  if owner = who then match atom with
    | .inl value => .inl value
    | .inr _ => .inl (L.someValue payload)
  else atom

omit [IExpr.ResultTypes L] in
/-- Replacing the hidden focal content retains the actual accepted/missing
classification whenever the original owner survives this instruction. -/
theorem repairAtom_missing (owner who : Player) (payload : L.Ty)
    (atom : L.Val payload ⊕ Bool)
    (survives : owner = who → atom ≠ .inr true) (name : VarId) :
    (bindingAtom owner name payload (repairAtom owner who payload atom)).missing =
      (bindingAtom owner name payload atom).missing := by
  by_cases own : owner = who
  · cases atom with
    | inl => simp only [repairAtom, own, ↓reduceIte, bindingAtom]
    | inr bit =>
        cases bit with
        | false => simp only [repairAtom, own, ↓reduceIte, bindingAtom]
        | true => exact (survives own rfl).elim
  · simp only [repairAtom, own, ↓reduceIte]

omit [IExpr.ResultTypes L] in
/-- The virtual atom carries exactly the existing focal binding repair. -/
theorem repairAtom_binding (owner who : Player) (payload : L.Ty)
    (atom : L.Val payload ⊕ Bool) (name : VarId) :
    OwnAction.binding owner name payload
        (some (bindingAtom owner name payload (repairAtom owner who payload atom)).action) =
      repairBinding owner who
        (OwnAction.binding owner name payload
          (some (bindingAtom owner name payload atom).action)) :=
  by
  by_cases own : owner = who
  · cases atom <;> simp only [repairAtom, own, ↓reduceIte, bindingAtom,
      OwnAction.binding_commit, repairBinding]
  · simp only [repairAtom, own, ↓reduceIte, repairBinding]

end CommitRecoveryMove

namespace ProtocolState

/-- Replacing a surviving actor's unusable bindings produces a supported
legal recovery instruction with the same exclusions. Every foreign atom,
including accepted failure and omission, remains the original one. -/
theorem VirtualRepair.recoveryStep (preserved : Finset VarId) (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program),
      VirtualRepair preserved who program original repaired →
      preserved ⊆ (Γ.map Prod.fst).toFinset →
      ∀ (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L)),
      IsLegalJoint (CommitRecoveryState.atPoint original excluded 0).Active
        (CommitRecoveryState.atPoint original excluded 0).available joint →
      ∀ target ∈ (ProtocolState.recoveryStep program original excluded joint).support,
      who ∉ target.2 →
      ∃ translated : Player → Option (CommitRecoveryMove Player L),
        (∀ observer, observer ≠ who → translated observer = joint observer) ∧
        IsLegalJoint (CommitRecoveryState.atPoint repaired excluded 0).Active
          (CommitRecoveryState.atPoint repaired excluded 0).available translated ∧
        ∃ paired ∈ (ProtocolState.recoveryStep program repaired excluded translated).support,
          paired.2 = target.2 ∧ VirtualRepair preserved who program target.1 paired.1 := by
  intro Γ O program
  induction program with
  | ret payoff =>
      intro original repaired related known excluded joint legal target reached _active
      have same := (PMF.mem_support_pure_iff _ _).mp reached
      subst target
      exact ⟨joint, fun _ _ => rfl, legal, (repaired, excluded),
        (PMF.mem_support_pure_iff _ _).mpr rfl, rfl, related⟩
  | sample name fresh law next ih =>
      intro original repaired related known excluded joint legal target reached active
      cases original with
      | inl original =>
          cases repaired with
          | inr => exact related.elim
          | inl repaired =>
              obtain ⟨value, drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
              have lawEq : L.evalDist law (sourcePublicEnv repaired.state) =
                  L.evalDist law (sourcePublicEnv original.state) := by
                obtain ⟨_, _, patched, _, _⟩ := related.related
                rw [sourcePublicEnv_congr repaired.state original.state
                  patched.publicEq patched.publicationEq]
              refine ⟨joint, fun _ _ => rfl, legal,
                (Sum.inr (entry next (sampleSuccessor name repaired value)), excluded), ?_, rfl,
                virtualRepair_entry preserved who next (related.sample name value)⟩
              exact (PMF.mem_support_map_iff _ _ _).mpr ⟨value, lawEq ▸ drawn, rfl⟩
      | inr original =>
          cases repaired with
          | inl => exact related.elim
          | inr repaired =>
              simp only [ProtocolState.recoveryStep, Sum.elim_inr, PMF.support_map,
                Set.mem_image] at reached
              obtain ⟨target, reached, rfl⟩ := reached
              obtain ⟨translated, same, permitted, paired, realized, exclusions, relation⟩ :=
                ih original repaired related
                  (fun _ member => by
                    simp only [List.map_cons, List.toFinset_cons]
                    exact Finset.mem_insert_of_mem (known member)) excluded joint legal
                  target reached active
              exact ⟨translated, same, permitted, (Sum.inr paired.1, paired.2),
                (PMF.mem_support_map_iff _ _ _).mpr ⟨paired, realized, rfl⟩,
                exclusions, relation⟩
  | @commit Γ O name owner payload fresh guard next ih =>
      intro original repaired related known excluded joint legal target reached active
      cases original with
      | inl original =>
          cases repaired with
          | inr => exact related.elim
          | inl repaired =>
              by_cases inactive : owner ∈ excluded
              · have same := (PMF.mem_support_pure_iff _ _).mp
                  (by simpa only [ProtocolState.recoveryStep, Sum.elim_inl, inactive,
                    ↓reduceIte] using reached)
                subst target
                have foreign : owner ≠ who := fun same => active
                  (same ▸ recoveryStep_excluded_monotone _ _ _ _ _ reached inactive)
                refine ⟨joint, fun _ _ => rfl, legal,
                  (Sum.inr (entry next (automaticCommit name owner payload repaired)), excluded),
                  ?_, rfl, virtualRepair_entry preserved who next
                    (related.automaticCommit name owner payload foreign)⟩
                simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
                  PMF.mem_support_pure_iff]
              · have ownLegal := legal owner
                cases chosen : joint owner with
                | none =>
                    rw [chosen] at ownLegal
                    exact (ownLegal ⟨rfl, inactive⟩).elim
                | some move =>
                    rw [chosen] at ownLegal
                    obtain ⟨atom, atomEq⟩ := CommitRecoveryMove.exists_bindingAtom_of_available
                      owner name payload fresh guard next (original.view owner) move ownLegal.2
                    subst move
                    let replacement := CommitRecoveryMove.bindingAtom owner name payload
                      (CommitRecoveryMove.repairAtom owner who payload atom)
                    let translated := Function.update joint owner (some replacement)
                    have notMiss : owner = who → atom ≠ .inr true := by
                      intro same bad
                      subst atom
                      simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive,
                        ↓reduceIte, chosen,
                        Option.map_some, CommitRecoveryMove.bindingAtom, OwnAction.binding_commit,
                        CommitRecoveryMove.missed, Option.elim_some,
                        PMF.mem_support_pure_iff] at reached
                      subst target
                      exact active (same ▸ Finset.mem_insert_self owner excluded)
                    have missing := CommitRecoveryMove.repairAtom_missing owner who payload atom
                      notMiss name
                    have same : ∀ observer, observer ≠ who → translated observer = joint observer :=
                      by
                      intro observer outside
                      by_cases acts : observer = owner
                      · subst observer
                        simp only [translated, Function.update_self, replacement,
                          CommitRecoveryMove.repairAtom, outside, ↓reduceIte, chosen]
                      · exact Function.update_of_ne acts _ _
                    have permitted : IsLegalJoint
                        (CommitRecoveryState.atPoint (program := .commit name owner fresh
                          guard next)
                          (.inl repaired) excluded 0).Active
                        (CommitRecoveryState.atPoint (program := .commit name owner fresh
                          guard next)
                          (.inl repaired) excluded 0).available
                        translated :=
                      by
                      intro observer
                      by_cases acts : observer = owner
                      · subst observer
                        dsimp only [translated]
                        rw [Function.update_self]
                        exact ⟨⟨rfl, inactive⟩,
                          CommitRecoveryMove.bindingAtom_available owner name payload fresh guard
                            next
                            (repaired.view owner) _⟩
                      · rw [show translated observer = joint observer from
                          Function.update_of_ne acts _ _]
                        exact legal observer
                    have originalEq := reached
                    simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
                      chosen,
                      Option.map_some, PMF.mem_support_pure_iff] at originalEq
                    subst target
                    let paired : ProtocolState (.commit name owner fresh guard next) ×
                        Finset Player :=
                      (Sum.inr (entry next (commitSuccessor name guard repaired
                      (OwnAction.binding owner name payload (some replacement.action)))),
                      if CommitRecoveryMove.missed (joint owner) then insert owner excluded
                        else excluded)
                    refine ⟨translated, same, permitted, paired, ?_,
                      by simp only [paired, chosen], ?_⟩
                    · simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive,
                      ↓reduceIte, translated,
                        Function.update_self, Option.map_some, PMF.mem_support_pure_iff]
                      simp only [paired, CommitRecoveryMove.missed, Option.elim_some, chosen,
                        replacement, missing]
                    · have binding :=
                        CommitRecoveryMove.repairAtom_binding owner who payload atom name
                      change VirtualRepair preserved who next
                        (entry next (commitSuccessor name guard original
                          (OwnAction.binding owner name payload
                            (some
                              (CommitRecoveryMove.bindingAtom owner name payload atom).action))))
                        (entry next (commitSuccessor name guard repaired
                          (OwnAction.binding owner name payload (some replacement.action))))
                      rw [show OwnAction.binding owner name payload (some replacement.action) =
                          repairBinding owner who (OwnAction.binding owner name payload
                            (some (CommitRecoveryMove.bindingAtom owner name payload atom).action))
                        from binding]
                      exact virtualRepair_entry preserved who next (related.commit name guard
                        (fun member => fresh (List.mem_toFinset.mp (known member))) _)
      | inr original =>
          cases repaired with
          | inl => exact related.elim
          | inr repaired =>
              simp only [ProtocolState.recoveryStep, Sum.elim_inr, PMF.support_map,
                Set.mem_image] at reached
              obtain ⟨target, reached, rfl⟩ := reached
              obtain ⟨translated, same, permitted, paired, realized, exclusions, relation⟩ :=
                ih original repaired related
                  (fun _ member => by
                    simp only [List.map_cons, List.toFinset_cons]
                    exact Finset.mem_insert_of_mem (known member)) excluded joint legal
                  target reached active
              exact ⟨translated, same, permitted, (Sum.inr paired.1, paired.2),
                (PMF.mem_support_map_iff _ _ _).mpr ⟨paired, realized, rfl⟩,
                exclusions, relation⟩
  | reveal published owner name fresh selected unresolved next ih =>
      intro original repaired related known excluded joint legal target reached active
      cases original with
      | inl original =>
          cases repaired with
          | inr => exact related.elim
          | inl repaired =>
              let disclose := if owner ∈ excluded then false else
                OwnAction.disclosure ((joint owner).map (·.action))
              obtain ⟨changed, relation, foreign⟩ := related.reveal published selected disclose
              let translated := if owner ∈ excluded then joint else
                Function.update joint owner (some ⟨.reveal owner name changed, false⟩)
              have activeBefore : who ∉ excluded := fun member =>
                active (recoveryStep_excluded_monotone _ _ _ _ _ reached member)
              have same : ∀ observer, observer ≠ who → translated observer = joint observer := by
                intro observer outside
                by_cases inactive : owner ∈ excluded
                · simp only [translated, inactive, ↓reduceIte]
                · simp only [translated, inactive, ↓reduceIte]
                  by_cases acts : observer = owner
                  · subst observer
                    have offered := legal owner
                    cases chosen : joint owner with
                    | none =>
                        rw [chosen] at offered
                        exact (offered ⟨rfl, inactive⟩).elim
                    | some move =>
                        rw [chosen] at offered
                        obtain ⟨⟨bit, action⟩, missing⟩ := offered.2
                        cases move with | mk actionValue marker =>
                          dsimp only at action missing
                          cases action
                          have bitEq : changed = bit := by
                            simpa only [disclose, inactive, ↓reduceIte, chosen, Option.map_some,
                              OwnAction.disclosure] using foreign outside
                          have markerEq : marker = false := missing
                          cases markerEq
                          simp only [Function.update_self, bitEq]
                  · exact Function.update_of_ne acts _ _
              have permitted : IsLegalJoint
                  (CommitRecoveryState.atPoint
                    (program := .reveal published owner name fresh selected unresolved next)
                    (.inl repaired) excluded 0).Active
                  (CommitRecoveryState.atPoint
                    (program := .reveal published owner name fresh selected unresolved next)
                    (.inl repaired) excluded 0).available
                  translated := by
                by_cases inactive : owner ∈ excluded
                · simpa only [translated, inactive, ↓reduceIte, IsLegalJoint,
                    CommitRecoveryState.Active, CommitRecoveryState.available,
                    CommitRecoveryState.atPoint, ProtocolState.actor, ProtocolState.observe,
                    ProtocolView.recoveryAvailable, ProtocolView.atCommit, ProtocolView.available,
                    Sum.elim_inl] using legal
                · simp only [translated, inactive, ↓reduceIte]
                  exact legal.update owner ⟨.reveal owner name changed, false⟩ ⟨rfl, inactive⟩
                    ⟨⟨changed, rfl⟩, rfl⟩
              have bitEq : (if owner ∈ excluded then false else
                  OwnAction.disclosure ((translated owner).map (·.action))) = changed := by
                by_cases inactive : owner ∈ excluded
                · have outside : owner ≠ who := fun same => activeBefore (same ▸ inactive)
                  simpa only [disclose, inactive, ↓reduceIte] using (foreign outside).symm
                · simp only [translated, inactive, ↓reduceIte, Function.update_self,
                    Option.map_some, OwnAction.disclosure]
              have publicEq := relation.related.publicOnly who
              have resultEq := congrArg (fun view : SourceObservation L who
                  ((published, .publication _) :: _) => view.cells published (.publication _) .here)
                publicEq
              simp only [Config.view, SourceObservation.publicOnly, sourceObserve_publication]
                at resultEq
              let ending := match (revealSuccessor published selected original disclose).state.get
                  .here with
                | .failure => insert owner excluded
                | .success _ => excluded
              simp only [ProtocolState.recoveryStep, Sum.elim_inl,
                PMF.mem_support_pure_iff] at reached
              change target = (Sum.inr (entry next
                (if owner ∈ excluded then
                  { revealSuccessor published selected original disclose with
                    history := original.history }
                else revealSuccessor published selected original disclose)), ending) at reached
              subst target
              by_cases inactive : owner ∈ excluded
              · have foreignPast : ∀ observer, observer ≠ who →
                    repaired.history observer = original.history observer := by
                  obtain ⟨_, _, invariant, _, _⟩ := related.related
                  exact invariant.historyEq
                have kept := relation.withHistories original.history repaired.history foreignPast
                let paired : ProtocolState
                    (.reveal published owner name fresh selected unresolved next) × Finset Player :=
                  (Sum.inr (entry next
                    { revealSuccessor published selected repaired changed with
                      history := repaired.history }), ending)
                refine ⟨translated, same, permitted, paired, ?_, rfl, ?_⟩
                · simp only [ProtocolState.recoveryStep, Sum.elim_inl]
                  rw [bitEq]
                  simp only [inactive, ↓reduceIte, PMF.mem_support_pure_iff]
                  dsimp only [paired, ending]
                  rw [resultEq]
                  rfl
                · simpa only [paired, inactive, ↓reduceIte, ProtocolState.VirtualRepair] using
                    virtualRepair_entry preserved who next kept
              · let paired : ProtocolState
                    (.reveal published owner name fresh selected unresolved next) × Finset Player :=
                  (Sum.inr (entry next
                    (revealSuccessor published selected repaired changed)), ending)
                refine ⟨translated, same, permitted, paired, ?_, rfl, ?_⟩
                · simp only [ProtocolState.recoveryStep, Sum.elim_inl]
                  rw [bitEq]
                  simp only [inactive, ↓reduceIte, PMF.mem_support_pure_iff]
                  dsimp only [paired, ending]
                  rw [resultEq]
                  rfl
                · simpa only [paired, inactive, ↓reduceIte, ProtocolState.VirtualRepair] using
                    virtualRepair_entry preserved who next relation
      | inr original =>
          cases repaired with
          | inl => exact related.elim
          | inr repaired =>
              simp only [ProtocolState.recoveryStep, Sum.elim_inr, PMF.support_map,
                Set.mem_image] at reached
              obtain ⟨target, reached, rfl⟩ := reached
              obtain ⟨translated, same, permitted, paired, realized, exclusions, relation⟩ :=
                ih original repaired related
                  (fun _ member => by
                    simp only [List.map_cons, List.toFinset_cons]
                    exact Finset.mem_insert_of_mem (known member)) excluded joint legal
                  target reached active
              exact ⟨translated, same, permitted, (Sum.inr paired.1, paired.2),
                (PMF.mem_support_map_iff _ _ _).mpr ⟨paired, realized, rfl⟩,
                exclusions, relation⟩

end ProtocolState

end Vegas.SourceProgram
