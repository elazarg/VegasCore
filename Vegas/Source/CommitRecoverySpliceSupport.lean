/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryStateSplice

/-! # Actual source instruction support under owner substitution

Two genuine instruction results with the same public record can be combined
using one owner's original raw coordinate and every other original coordinate.
The result is supported by the existing recovery instruction kernel.
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Owner substitution produces an actual supported raw source successor,
retaining the second result's original public control and Nature draw. -/
theorem recoveryStep_splice_support (focal : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (mine others : ProtocolState program),
      MetadataEq program mine others →
      ProtocolView.publicOnly focal program (observe focal program mine) =
        ProtocolView.publicOnly focal program (observe focal program others) →
      ∀ (excluded : Finset Player)
        (left right : Player → Option (CommitRecoveryMove Player L)),
      ∀ l ∈ (recoveryStep program mine excluded left).support,
      ∀ r ∈ (recoveryStep program others excluded right).support,
        l.2 = r.2 →
        ProtocolView.publicOnly focal program (observe focal program l.1) =
          ProtocolView.publicOnly focal program (observe focal program r.1) →
        (splice focal program l.1 r.1, r.2) ∈
          (recoveryStep program (splice focal program mine others) excluded
            (Function.update right focal (left focal))).support
  | _, _, .ret _, _, _, _, _, _, _, _, l, lm, r, rm, _, _ => by
      simp only [recoveryStep, PMF.mem_support_pure_iff] at lm rm
      subst l; subst r
      exact (PMF.mem_support_pure_iff ..).mpr rfl
  | Γ, _, .sample (payload := payload) name _ law next, mine, others, metadata, before,
      excluded, left, right, l, lm, r, rm, exclusions, after => by
      cases mine with
      | inl mine =>
          cases others with
          | inr _ => cases metadata
          | inl others =>
              obtain ⟨lv, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
              obtain ⟨rv, rvMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
              have environment : sourcePublicEnv (Config.splice focal mine others).state =
                  sourcePublicEnv others.state := by
                apply sourcePublicEnv_congr
                · intro cellName cellType member; rfl
                · intro cellName cellType member; rfl
              simp only [recoveryStep, splice, Sum.elim_inl]
              rw [environment]
              apply (PMF.mem_support_map_iff _ _ _).mpr
              refine ⟨rv, rvMember, ?_⟩
              rw [splice_entry, Config.splice_sample]
      | inr mine =>
          cases others with
          | inl _ => cases metadata
          | inr others =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next mine excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next others excluded right) _).mp rm
              subst l; subst r
              apply (PMF.mem_support_map_iff _ _ _).mpr
              exact ⟨_, recoveryStep_splice_support focal next mine others metadata
                (Sum.inr.inj before) excluded left right lowerLeft lowerLeftMember
                lowerRight lowerRightMember exclusions (Sum.inr.inj after), rfl⟩
  | _, _, .commit name owner _ guard next, mine, others, metadata, before,
      excluded, left, right, l, lm, r, rm, exclusions, after => by
      cases mine with
      | inl mine =>
          cases others with
          | inr _ => cases metadata
          | inl others =>
              by_cases inactive : owner ∈ excluded
              · simp only [recoveryStep, Sum.elim_inl, ite_eq_left inactive,
                  PMF.mem_support_pure_iff] at lm rm
                subst l; subst r
                simp only [recoveryStep, splice, Sum.elim_inl, ite_eq_left inactive,
                  PMF.mem_support_pure_iff, splice_entry, Config.splice_automaticCommit]
              · simp only [recoveryStep, Sum.elim_inl, ite_eq_right inactive,
                  PMF.mem_support_pure_iff] at lm rm
                subst l; subst r
                simp only [recoveryStep, splice, Sum.elim_inl, ite_eq_right inactive,
                  PMF.mem_support_pure_iff, splice_entry, Config.splice_commit]
                by_cases own : owner = focal
                · subst owner
                  simp only [Function.update_self, ↓reduceIte]
                  exact Prod.ext rfl exclusions.symm
                · simp only [Function.update_of_ne own, own, ↓reduceIte]
      | inr mine =>
          cases others with
          | inl _ => cases metadata
          | inr others =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next mine excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next others excluded right) _).mp rm
              subst l; subst r
              apply (PMF.mem_support_map_iff _ _ _).mpr
              exact ⟨_, recoveryStep_splice_support focal next mine others metadata
                (Sum.inr.inj before) excluded left right lowerLeft lowerLeftMember
                lowerRight lowerRightMember exclusions (Sum.inr.inj after), rfl⟩
  | Γ, _, .reveal (payload := payload) published owner _ _ source _ next,
      mine, others, metadata, before, excluded, left, right, l, lm, r, rm,
      exclusions, after => by
      cases mine with
      | inl mine =>
          cases others with
          | inr _ => cases metadata
          | inl others =>
              by_cases inactive : owner ∈ excluded
              · have silentResult (config : Config Player L Γ) :
                    (revealSuccessor published source config false).state.get .here = .failure :=
                  disclosureResult_false published source config
                simp only [recoveryStep, Sum.elim_inl, ite_eq_left inactive,
                  silentResult, Finset.insert_eq_of_mem inactive,
                  PMF.mem_support_pure_iff] at lm rm
                subst l; subst r
                simp only [recoveryStep, splice, Sum.elim_inl, ite_eq_left inactive,
                  silentResult, Finset.insert_eq_of_mem inactive,
                  PMF.mem_support_pure_iff, splice_entry, Config.splice_automaticReveal]
              · simp only [recoveryStep, Sum.elim_inl, ite_eq_right inactive,
                  PMF.mem_support_pure_iff] at lm rm
                subst l; subst r
                have publicCells : (mine.view focal).1.publicOnly =
                    (others.view focal).1.publicOnly := congrArg Prod.fst (Sum.inl.inj before)
                have nextCells := ProtocolView.publicOnly_entry_cells focal next _ _
                  (Sum.inr.inj after)
                let dl := OwnAction.disclosure ((left owner).map (·.action))
                let dr := OwnAction.disclosure ((right owner).map (·.action))
                have publishedResult : disclosureResult published source mine dl =
                    disclosureResult published source others dr := congrArg
                  (fun view => view.cells published (.publication payload) .here) nextCells
                have result : disclosureResult published source (Config.splice focal mine others)
                      (if owner = focal then dl else dr) =
                    disclosureResult published source others dr := by
                  rw [Config.splice_disclosureResult focal published source mine others publicCells
                    metadata.1 metadata.2 dl dr]
                  split
                  · exact publishedResult
                  · rfl
                have choice : OwnAction.disclosure
                      (((Function.update right focal (left focal)) owner).map (·.action)) =
                    if owner = focal then dl else dr := by
                  by_cases own : owner = focal
                  · subst owner
                    simp only [Function.update_self, ↓reduceIte]
                    rfl
                  · simp only [Function.update_of_ne own, own, ↓reduceIte]
                    rfl
                simp only [recoveryStep, splice, Sum.elim_inl, ite_eq_right inactive,
                  PMF.mem_support_pure_iff]
                rw [choice, splice_entry, Config.splice_reveal focal published source mine others
                  publicCells metadata.1 metadata.2 dl dr publishedResult]
                apply Prod.ext
                · rfl
                · unfold disclosureResult at result
                  simp only [result, dr]
      | inr mine =>
          cases others with
          | inl _ => cases metadata
          | inr others =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next mine excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next others excluded right) _).mp rm
              subst l; subst r
              apply (PMF.mem_support_map_iff _ _ _).mpr
              exact ⟨_, recoveryStep_splice_support focal next mine others metadata
                (Sum.inr.inj before) excluded left right lowerLeft lowerLeftMember
                lowerRight lowerRightMember exclusions (Sum.inr.inj after), rfl⟩

end Vegas.SourceProgram.ProtocolState
