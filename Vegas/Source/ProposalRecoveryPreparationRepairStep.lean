/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryPreparationRepair

/-! # Selective preparation partners for actual recovery instructions -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- An actual recovery instruction has a selective partner even when the
repaired owner is already excluded or is excluded by this instruction. -/
theorem FocalRepair.preparation_recoveryStep (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program),
      FocalRepair who program original repaired →
      ∀ (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L)),
      IsLegalJoint (CommitRecoveryState.atPoint original excluded 0).Active
        (CommitRecoveryState.atPoint original excluded 0).available joint →
      ∀ target ∈ (ProtocolState.recoveryStep program original excluded joint).support,
      ∃ translated : Player → Option (CommitRecoveryMove Player L),
        (∀ observer, observer ≠ who → translated observer = joint observer) ∧
        translated = repairPreparationRawJoint who program original joint ∧
        IsLegalJoint (CommitRecoveryState.atPoint repaired excluded 0).Active
          (CommitRecoveryState.atPoint repaired excluded 0).available translated ∧
        ∃ paired ∈ (ProtocolState.recoveryStep program repaired excluded translated).support,
          paired.2 = target.2 ∧ FocalRepair who program target.1 paired.1 := by
  intro Γ O program
  induction program with
  | ret payoff =>
      intro original repaired related excluded joint legal target reached
      have same := (PMF.mem_support_pure_iff _ _).mp reached
      subst target
      exact ⟨joint, fun _ _ => rfl, rfl, legal, (repaired, excluded),
        (PMF.mem_support_pure_iff _ _).mpr rfl, rfl, related⟩
  | sample name fresh law next ih =>
      intro original repaired related excluded joint legal target reached
      cases original with
      | inl original =>
          cases repaired with
          | inr => exact related.elim
          | inl repaired =>
              obtain ⟨value, drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
              have lawEq : L.evalDist law (sourcePublicEnv repaired.state) =
                  L.evalDist law (sourcePublicEnv original.state) := by
                obtain ⟨_, _, patched, _, _⟩ := related
                rw [sourcePublicEnv_congr repaired.state original.state
                  patched.publicEq patched.publicationEq]
              refine ⟨joint, fun _ _ => rfl, rfl, legal,
                (Sum.inr (entry next (sampleSuccessor name repaired value)), excluded), ?_, rfl,
                focalRepair_entry who next (related.sample name value)⟩
              exact (PMF.mem_support_map_iff _ _ _).mpr ⟨value, lawEq ▸ drawn, rfl⟩
      | inr original =>
          cases repaired with
          | inl => exact related.elim
          | inr repaired =>
              simp only [ProtocolState.recoveryStep, Sum.elim_inr, PMF.support_map,
                Set.mem_image] at reached
              obtain ⟨target, reached, rfl⟩ := reached
              obtain ⟨translated, same, described, permitted, paired, realized, exclusions,
                relation⟩ :=
                ih original repaired related excluded joint legal target reached
              exact ⟨translated, same, described, permitted, (Sum.inr paired.1, paired.2),
                (PMF.mem_support_map_iff _ _ _).mpr ⟨paired, realized, rfl⟩,
                exclusions, relation⟩
  | @commit Γ O name owner payload fresh guard next ih =>
      intro original repaired related excluded joint legal target reached
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
                have absent : joint owner = none := by
                  cases chosen : joint owner with
                  | none => rfl
                  | some move =>
                      have offered := legal owner
                      rw [chosen] at offered
                      exact (offered.1.2 inactive).elim
                have described : joint = repairPreparationRawJoint who
                    (.commit name owner fresh guard next) (.inl original) joint := by
                  funext observer
                  simp only [repairPreparationRawJoint, Sum.elim_inl]
                  split
                  · by_cases acts : observer = owner
                    · subst observer
                      simp only [Function.update_self, absent, Option.map_none]
                    · rw [Function.update_of_ne acts]
                  · rfl
                refine ⟨joint, fun _ _ => rfl, described, legal,
                  (Sum.inr (entry next (automaticCommit name owner payload repaired)), excluded),
                  ?_, rfl, focalRepair_entry who next
                    (related.automaticCommit name owner payload)⟩
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
                      (repairPreparationAtom owner who payload atom)
                    let translated := Function.update joint owner (some replacement)
                    have missing := repairPreparationAtom_missing owner who payload atom name
                    have same : ∀ observer, observer ≠ who → translated observer = joint observer :=
                      by
                      intro observer outside
                      by_cases acts : observer = owner
                      · subst observer
                        simp only [translated, Function.update_self, replacement,
                          repairPreparationAtom, outside, ↓reduceIte, chosen]
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
                    have described : translated = repairPreparationRawJoint who
                        (.commit name owner fresh guard next) (.inl original) joint := by
                      funext observer
                      by_cases own : owner = who
                      · subst who
                        simp only [repairPreparationRawJoint, Sum.elim_inl, ↓reduceIte]
                        by_cases acts : observer = owner
                        · subst observer
                          rw [chosen]
                          simp only [translated, Function.update_self, Option.map_some, replacement]
                          cases atom with
                          | inl value => simp [repairPreparationAtom,
                              CommitRecoveryMove.bindingAtom, OwnAction.binding_commit]
                          | inr bit => cases bit <;> simp [repairPreparationAtom,
                              CommitRecoveryMove.bindingAtom, OwnAction.binding_commit]
                        · simp only [translated, Function.update_of_ne acts]
                      · simp only [repairPreparationRawJoint, Sum.elim_inl, own, ↓reduceIte]
                        by_cases acts : observer = owner
                        · subst observer
                          simp only [translated, Function.update_self, chosen, replacement,
                            repairPreparationAtom, own, ↓reduceIte]
                        · exact Function.update_of_ne acts _ _
                    refine ⟨translated, same, described, permitted, paired, ?_,
                      by simp only [paired, chosen], ?_⟩
                    · simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive,
                      ↓reduceIte, translated,
                        Function.update_self, Option.map_some, PMF.mem_support_pure_iff]
                      simp only [paired, CommitRecoveryMove.missed, Option.elim_some, chosen,
                        replacement, missing]
                    · change FocalRepair who next
                        (entry next (commitSuccessor name guard original
                          (OwnAction.binding owner name payload
                            (some (CommitRecoveryMove.bindingAtom owner name payload
                              atom).action))))
                        (entry next (commitSuccessor name guard repaired
                          (OwnAction.binding owner name payload (some replacement.action))))
                      apply focalRepair_entry who next
                      by_cases own : owner = who
                      · subst owner
                        cases atom with
                        | inl value =>
                            simpa [replacement, repairPreparationAtom,
                              CommitRecoveryMove.bindingAtom, OwnAction.binding, repairBinding]
                                using
                              related.commit name guard (.success value)
                        | inr bit =>
                            cases bit with
                            | false =>
                                simpa [replacement, repairPreparationAtom,
                                  CommitRecoveryMove.bindingAtom, OwnAction.binding,
                                    repairBinding] using
                                  related.commit name guard .failure
                            | true =>
                                simpa [replacement, repairPreparationAtom,
                                  CommitRecoveryMove.bindingAtom, OwnAction.binding] using
                                  related.commit_kept name who payload guard .failure
                      · simpa [replacement, repairPreparationAtom, own, repairBinding] using
                          related.commit name guard
                            (OwnAction.binding owner name payload
                              (some (CommitRecoveryMove.bindingAtom owner name payload
                                atom).action))
      | inr original =>
          cases repaired with
          | inl => exact related.elim
          | inr repaired =>
              simp only [ProtocolState.recoveryStep, Sum.elim_inr, PMF.support_map,
                Set.mem_image] at reached
              obtain ⟨target, reached, rfl⟩ := reached
              obtain ⟨translated, same, described, permitted, paired, realized, exclusions,
                relation⟩ :=
                ih original repaired related excluded joint legal target reached
              exact ⟨translated, same, described, permitted, (Sum.inr paired.1, paired.2),
                (PMF.mem_support_map_iff _ _ _).mpr ⟨paired, realized, rfl⟩,
                exclusions, relation⟩
  | reveal published owner name fresh selected unresolved next ih =>
      intro original repaired related excluded joint legal target reached
      cases original with
      | inl original =>
          cases repaired with
          | inr => exact related.elim
          | inl repaired =>
              let disclose := if owner ∈ excluded then false else
                OwnAction.disclosure ((joint owner).map (·.action))
              let changed := Config.preparationDisclosure who owner original selected disclose
              have relation := related.reveal_preparation published selected disclose
              have foreign : owner ≠ who → changed = disclose := by
                intro outside
                simp only [changed, Config.preparationDisclosure, outside, ↓reduceIte]
              let translated := if owner ∈ excluded then joint else
                Function.update joint owner (some ⟨.reveal owner name changed, false⟩)
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
                intro observer
                by_cases inactive : owner ∈ excluded
                · simp only [translated, inactive, ↓reduceIte]
                  cases choice : joint observer with
                  | none =>
                      intro acting
                      exact acting.2 (Option.some.inj acting.1 ▸ inactive)
                  | some move =>
                      have offered := legal observer
                      rw [choice] at offered
                      exact (offered.1.2 (Option.some.inj offered.1.1 ▸ inactive)).elim
                · simp only [translated, inactive, ↓reduceIte]
                  by_cases acts : observer = owner
                  · subst observer
                    rw [Function.update_self]
                    exact ⟨⟨rfl, inactive⟩, ⟨changed, rfl⟩, rfl⟩
                  · rw [Function.update_of_ne acts]
                    exact legal observer
              have bitEq : (if owner ∈ excluded then false else
                  OwnAction.disclosure ((translated owner).map (·.action))) = changed := by
                by_cases inactive : owner ∈ excluded
                · simp only [changed, disclose, inactive, ↓reduceIte]
                  unfold Config.preparationDisclosure
                  split
                  · split <;> rfl
                  · rfl
                · simp only [translated, inactive, ↓reduceIte, Function.update_self,
                    Option.map_some, OwnAction.disclosure]
              have publicEq := relation.publicOnly who
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
              have described : translated = repairPreparationRawJoint who
                  (.reveal published owner name fresh selected unresolved next) (.inl original)
                    joint := by
                funext observer
                by_cases inactive : owner ∈ excluded
                · have absent : joint owner = none := by
                    cases chosen : joint owner with
                    | none => rfl
                    | some move =>
                      have offered := legal owner
                      rw [chosen] at offered
                      exact (offered.1.2 inactive).elim
                  simp only [translated, inactive, ↓reduceIte, repairPreparationRawJoint,
                    Sum.elim_inl]
                  split
                  · split
                    · by_cases acts : observer = owner
                      · subst observer
                        simp only [Function.update_self, absent, Option.map_none]
                      · rw [Function.update_of_ne acts]
                    · rfl
                  · rfl
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
                          cases missing
                          have disclosure : disclose = bit := by
                            simp only [disclose, inactive, ↓reduceIte, chosen, Option.map_some,
                              OwnAction.disclosure]
                          simp only [repairPreparationRawJoint, Sum.elim_inl]
                          by_cases own : owner = who
                          · subst who
                            cases bound : original.state.get selected
                            · simp only [Function.update_self]
                              rw [chosen]
                              simp [changed, Config.preparationDisclosure, bound]
                            · simp only [Function.update_self, ↓reduceIte]
                              rw [chosen]
                              simp [changed, Config.preparationDisclosure, bound, disclosure]
                          · simp only [own, ↓reduceIte, Function.update_self]
                            rw [chosen]
                            simp only [changed, Config.preparationDisclosure, own, ↓reduceIte,
                              disclosure]
                  · simp only [Function.update_of_ne acts, repairPreparationRawJoint, Sum.elim_inl]
                    split
                    · split
                      · exact (Function.update_of_ne acts _ _).symm
                      · rfl
                    · rfl
              by_cases inactive : owner ∈ excluded
              · have foreignPast : ∀ observer, observer ≠ who →
                    repaired.history observer = original.history observer := by
                  obtain ⟨_, _, invariant, _, _⟩ := related
                  exact invariant.historyEq
                have kept := relation.withHistories original.history repaired.history foreignPast
                let paired : ProtocolState
                    (.reveal published owner name fresh selected unresolved next) × Finset Player :=
                  (Sum.inr (entry next
                    { revealSuccessor published selected repaired changed with
                      history := repaired.history }), ending)
                refine ⟨translated, same, described, permitted, paired, ?_, rfl, ?_⟩
                · simp only [ProtocolState.recoveryStep, Sum.elim_inl]
                  rw [bitEq]
                  simp only [inactive, ↓reduceIte, PMF.mem_support_pure_iff]
                  dsimp only [paired, ending]
                  rw [resultEq]
                  rfl
                · simpa only [paired, inactive, ↓reduceIte, ProtocolState.FocalRepair] using
                    focalRepair_entry who next kept
              · let paired : ProtocolState
                    (.reveal published owner name fresh selected unresolved next) × Finset Player :=
                  (Sum.inr (entry next
                    (revealSuccessor published selected repaired changed)), ending)
                refine ⟨translated, same, described, permitted, paired, ?_, rfl, ?_⟩
                · simp only [ProtocolState.recoveryStep, Sum.elim_inl]
                  rw [bitEq]
                  simp only [inactive, ↓reduceIte, PMF.mem_support_pure_iff]
                  dsimp only [paired, ending]
                  rw [resultEq]
                  rfl
                · simpa only [paired, inactive, ↓reduceIte, ProtocolState.FocalRepair] using
                    focalRepair_entry who next relation
      | inr original =>
          cases repaired with
          | inl => exact related.elim
          | inr repaired =>
              simp only [ProtocolState.recoveryStep, Sum.elim_inr, PMF.support_map,
                Set.mem_image] at reached
              obtain ⟨target, reached, rfl⟩ := reached
              obtain ⟨translated, same, described, permitted, paired, realized, exclusions,
                relation⟩ :=
                ih original repaired related excluded joint legal target reached
              exact ⟨translated, same, described, permitted, (Sum.inr paired.1, paired.2),
                (PMF.mem_support_map_iff _ _ _).mpr ⟨paired, realized, rfl⟩,
                exclusions, relation⟩

end ProtocolState
end Vegas.SourceProgram
