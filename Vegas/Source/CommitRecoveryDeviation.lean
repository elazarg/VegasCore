/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitBlockRecovery
import Vegas.Source.FailedBindingDeviation

/-! # First departures from intended source recovery choices -/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- An extra intended-site source choice either publicly excludes its author
immediately or creates latent debt inside the current commitment block. An
accepted unusable binding is in the second case, without a public omission. -/
theorem recoveryStep_deviation (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (point : ProtocolState program), Intended program point →
      (joint : Player → Option (CommitRecoveryMove Player L)) →
      (move : CommitRecoveryMove Player L) → joint who = some move →
      actor program point = some who →
      move ∈ ProtocolView.recoveryAvailable who program (observe who program point) →
      (move.missing = true ∨
        move.action ∉ ProtocolView.intendedAvailable who program (observe who program point)) →
      ∀ result ∈ (recoveryStep program point ∅ joint).support,
        who ∈ result.2 ∨
          (atCommit program point = true ∧ OwesFailure who program result.1 ∧ result.2 = ∅)
  | _, _, .ret _, _, _, _, _, _, acting, _, _, _, _ => by cases acting
  | _, _, .sample _ _ _ next, point, intended, joint, move, chosen, acting, offered,
      extra, result, reached => by
      cases point with
      | inl _ => cases acting
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact recoveryStep_deviation who next point intended joint move chosen acting
            offered extra after supported
  | _, _, .commit name owner fresh guard next, point, intended, joint, move, chosen,
      acting, offered, extra, result, reached => by
      cases point with
      | inl config =>
          have own : owner = who := Option.some.inj acting
          subst owner
          let program := SourceProgram.commit name who fresh guard next
          by_cases missing : move.missing = true
          · have missed : CommitRecoveryMove.missed (joint who) = true := by
              simpa only [chosen, CommitRecoveryMove.missed, Option.elim_some] using missing
            exact Or.inl (recoveryStep_missed_excludes who program (Sum.inl config) ∅ joint
              rfl acting missed result reached)
          · have noMiss : move.missing = false := Bool.eq_false_iff.mpr missing
            have notIntended := extra.resolve_left missing
            have acted : (joint who).map (·.action) = some move.action := by rw [chosen]; rfl
            have raw : result.2 = ∅ ∧
                result.1 ∈ (step program (Sum.inl config)
                  (fun observer => (joint observer).map (·.action))).support := by
              simp only [recoveryStep, Sum.elim_inl, Finset.notMem_empty, ↓reduceIte,
                chosen, CommitRecoveryMove.missed, Option.elim_some, noMiss,
                PMF.mem_support_pure_iff] at reached
              subst result
              refine ⟨rfl, ?_⟩
              apply (PMF.mem_support_pure_iff _ _).mpr
              dsimp only
              rw [chosen]
            exact Or.inr ⟨rfl,
              owesFailure_of_deviation who program (CommitmentInterface.forfeiture program)
                (Sum.inl config) intended (fun observer => (joint observer).map (·.action))
                move.action acted ((actor_observe_eq _ _ _).trans acting) offered.1
                notIntended result.1 raw.2, raw.1⟩
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact recoveryStep_deviation who next point intended joint move chosen acting
            offered extra after supported
  | _, _, .reveal published owner name _ source _ next, point, intended, joint,
      move, chosen, acting, offered, extra, result, reached => by
      cases point with
      | inl config =>
          have own : owner = who := Option.some.inj acting
          subst owner
          have noMiss : move.missing = false := offered.2
          have notIntended := extra.resolve_left (by rw [noMiss]; decide)
          obtain ⟨disclose, selected⟩ := offered.1
          have withholds : disclose = false := by
            cases disclose with
            | false => rfl
            | true => exact (notIntended selected).elim
          have packet : (joint who).map (·.action) =
              some (.reveal who name false) := by
            rw [chosen]
            simp only [Option.map_some]
            rw [selected, withholds]
          have failed : (revealSuccessor published source config false).state.get .here =
              .failure := by simp [revealSuccessor]
          simp only [recoveryStep, Sum.elim_inl, Finset.notMem_empty, ↓reduceIte,
            packet, OwnAction.disclosure, failed, PMF.mem_support_pure_iff] at reached
          subst result
          exact Or.inl (Finset.mem_insert_self _ _)
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases recoveryStep_deviation who next point intended.2 joint move chosen acting
              offered extra after supported with excluded | debt
          · exact Or.inl excluded
          · exact Or.inr ⟨debt.1, debt.2.1.elim (fun owed => Or.inl (Or.inr owed))
              (fun owed => Or.inr (Or.inr owed)), debt.2.2⟩

end Vegas.SourceProgram.ProtocolState

namespace Vegas.SourceProgram.CommitRecoveryState

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

/-- Automatic closure of the first extra choice either retains its author's
public exclusion or leaves the newly created live debt in its original block. -/
theorem deviation (who : Player) (state : CommitRecoveryState program)
    (clear : state.excluded = ∅) (intended : ProtocolState.Intended program state.point)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (move : CommitRecoveryMove Player L) (chosen : joint who = some move)
    (acting : ProtocolState.actor program state.point = some who)
    (offered : move ∈ state.available who)
    (extra : move.missing = true ∨ move.action ∉ ProtocolView.intendedAvailable who program
      (ProtocolState.observe who program state.point))
    (next : CommitRecoveryState program) (reached : next ∈ (state.step joint).support) :
    who ∈ next.excluded ∨ (next.excluded = ∅ ∧
      ProtocolState.atCommit program state.point = true ∧
      ProtocolState.OwesFailure who program next.point) := by
  obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
  have rawClear : result.1 ∈
      (ProtocolState.recoveryStep program state.point ∅ joint).support := by
    simpa only [← clear] using raw
  rcases ProtocolState.recoveryStep_deviation who program state.point intended joint move chosen
      acting offered extra result.1 rawClear with excluded | latent
  · left
    rw [close_excluded]
    exact excluded
  · have noFailure : ¬ (state.install result.1 result.2).NewFailure := by
      simp only [NewFailure, install, latent.2.2, Finset.empty_sdiff,
        Finset.not_nonempty_empty, not_false_eq_true]
    refine Or.inr ⟨?_, latent.1, ?_⟩
    · simpa only [close_excluded, install] using latent.2.2
    · rw [close_point_of_no_new_failure _ noFailure]
      exact latent.2.1

end Vegas.SourceProgram.CommitRecoveryState
