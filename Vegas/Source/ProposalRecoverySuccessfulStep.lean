/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoverySuccessfulObservation
import Vegas.Source.CommitRecoveryClear
import Vegas.Source.CommitRecoveryRanks

/-! # Public successful-proposal extraction on actual clear source steps -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Along a genuinely clear recovery step, the newly observed successful
publication is exactly the pre-state-derived ordinary proposal. General guard
failures are excluded by the actual empty output exclusion set, not assumed
to reveal their hidden plaintext in the original source view. -/
theorem ProtocolView.successfulProposalWord_recoveryStep (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (joint : Player → Option (CommitRecoveryMove Player L))
      (result : ProtocolState program × Finset Player),
      result ∈ (ProtocolState.recoveryStep program point ∅ joint).support →
      result.2 = ∅ →
      successfulProposalWord who program (ProtocolState.observe who program result.1) =
        successfulProposalWord who program (ProtocolState.observe who program point) ++
          (ProtocolState.recoveryProposal program point
            (fun owner => (joint owner).map ProposalRecoveryMove.ordinary)).toList
  | _, _, .ret _, point, _joint, result, reached, _clear => by
      have same := (PMF.mem_support_pure_iff _ _).mp reached
      subst result
      rfl
  | _, _, .sample name fresh law next, point, joint, result, reached, clear => by
      cases point with
      | inl config =>
          obtain ⟨value, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          simp only [ProtocolState.observe, Sum.elim_inl, Sum.elim_inr,
            successfulProposalWord, successfulProposalWord_entry, List.map_nil,
            ProtocolState.recoveryProposal, Option.toList_none, List.nil_append]
      | inr later =>
          obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          have previous := successfulProposalWord_recoveryStep who next later joint after
            supported clear
          simpa only [ProtocolState.observe, Sum.elim_inr, successfulProposalWord,
            ProtocolState.recoveryProposal, List.map_append, Option.toList_map] using
              congrArg (List.map fun pair : Nat × Sigma L.Val => (pair.1 + 1, pair.2)) previous
  | _, _, .commit name owner fresh guard next, point, joint, result, reached, clear => by
      cases point with
      | inl config =>
          simp only [ProtocolState.recoveryStep, Sum.elim_inl, Finset.notMem_empty,
            ite_false, PMF.mem_support_pure_iff] at reached
          subst result
          simp only [ProtocolState.observe, Sum.elim_inl, Sum.elim_inr,
            successfulProposalWord, successfulProposalWord_entry, List.map_nil,
            ProtocolState.recoveryProposal, Option.toList_none, List.nil_append]
      | inr later =>
          obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          have previous := successfulProposalWord_recoveryStep who next later joint after
            supported clear
          simpa only [ProtocolState.observe, Sum.elim_inr, successfulProposalWord,
            ProtocolState.recoveryProposal, List.map_append, Option.toList_map] using
              congrArg (List.map fun pair : Nat × Sigma L.Val => (pair.1 + 1, pair.2)) previous
  | _, _, .reveal published owner name fresh source unresolved next,
      point, joint, result, reached, clear => by
      cases point with
      | inl config =>
          let disclose := OwnAction.disclosure ((joint owner).map (·.action))
          let after := revealSuccessor published source config disclose
          simp only [ProtocolState.recoveryStep, Sum.elim_inl, Finset.notMem_empty,
            ite_false, PMF.mem_support_pure_iff] at reached
          subst result
          change (match after.state.get .here with
            | .failure => insert owner ∅
            | .success _ => ∅) = ∅ at clear
          have success : ∃ value, after.state.get .here = .success value := by
            cases verdict : after.state.get .here with
            | failure => simp [verdict] at clear
            | success value => exact ⟨value, rfl⟩
          obtain ⟨value, success⟩ := success
          have original := revealSuccessor_binding_of_success source config disclose value success
          have seen : (after.view who).1.cells.get .here = .success value := by
            exact (sourceObserve_publication who after.state .here).trans success
          dsimp only [after, disclose] at seen
          have exposed : (((joint owner).map ProposalRecoveryMove.ordinary).map
              (·.discloses)).getD false = disclose := by
            cases selected : joint owner with
            | none => simp only [disclose, selected, Option.map_none,
                Option.getD_none, OwnAction.disclosure]
            | some move =>
                simp only [disclose, selected, Option.map_some, Option.getD_some,
                  ProposalRecoveryMove.discloses, ProposalRecoveryMove.ordinary, Bool.or_false]
          simp only [ProtocolState.observe, Sum.elim_inl, Sum.elim_inr,
            successfulProposalWord, entryView_observe_entry, successfulProposalWord_entry,
            seen, List.map_nil, List.append_nil, List.nil_append,
            ProtocolState.recoveryProposal, exposed, original.1, ite_true, original.2,
            Option.toList_some]
      | inr later =>
          obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          have previous := successfulProposalWord_recoveryStep who next later joint after
            supported clear
          have entry := entryView_recoveryStep who next later ∅ joint after supported
            (by simp only [Finset.notMem_empty, not_false_eq_true])
          simp only [ProtocolState.observe, Sum.elim_inr, successfulProposalWord,
            ProtocolState.recoveryProposal, entry, Option.toList_map]
          rw [previous, List.map_append]
          simp only [List.append_assoc]


end Vegas.SourceProgram
