module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensLedgerClient
public import Vegas.Pending.ReactiveCandidateBudget
public import Interaction.ReactiveRecovery

@[expose] public section

/-! # Candidate slot use in the Odds–Evens client's response recall -/

noncomputable section

namespace Vegas.Examples.OddsEvensLedgerClient

open OddsEvens EventGraphRuntime EventGraph Interaction GameTheory.Math.Probability

private theorem responseCandidateSlot_of_publication (who : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) (event : compiled.EventId)
    (choice : compiled.Action event)
    (publication : compiled.outputLayout event = .publication BaseTy.bool) :
    responseCandidateSlot timeouts OddsEvensService.leaks
      (ordinaryResponse who past view event choice) = none := by
  by_cases inactive : who ∈ view.application.publicView.observation.defaulted
  · rw [ordinaryResponse, canonicalServiceDecision_defaulted _ _ _ _ _ _ _ inactive]
    rfl
  unfold ordinaryResponse canonicalServiceDecision canonicalReactiveDecision
  simp only [ite_eq_right inactive]
  cases node : nodeView compiled event with
  | sample => rfl
  | bind owner payload outputEq codeEq =>
    cases publication.symm.trans outputEq
  | resolve owner payload binding checks outputEq codeEq =>
    dsimp only
    rcases reactiveResolutionPacket_shape who event payload binding checks outputEq choice
        view.application with ⟨candidate, raw, packet⟩ | silent
    · rw [packet]
      rfl
    · rw [silent]
      rfl

private theorem candidate_slot_names_binding (who : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) (action : app.Action)
    (supported : action ∈ (policy who past view).support) (serial : Nat)
    (reserved : responseCandidateSlot timeouts OddsEvensService.leaks action = some serial) :
    submittedEvent? timeouts OddsEvensService.leaks action =
      some (eventId (if who then 1 else 0)) := by
  let retainedPast := past.map (ReactiveApplication.PlayerEntry.ledgerOnly app)
  let retainedView := view.ledgerOnly app
  change action ∈ (respond who retainedPast retainedView).support at supported
  by_cases inactive : who ∈ retainedView.application.publicView.observation.defaulted
  · simp only [respond, ite_eq_left inactive, PMF.mem_support_pure_iff] at supported
    subst action
    cases reserved
  cases turn : retainedView.application.publicView.ownTurn? who with
  | none =>
    simp only [respond, ite_eq_right inactive, turn, PMF.mem_support_pure_iff] at supported
    subst action
    cases reserved
  | some event =>
    have owner := (retainedView.application.publicView.ownTurn?_spec who event turn).2
    cases recorded : eventRecorded timeouts OddsEvensService.leaks retainedPast event with
    | true =>
      simp only [respond, ite_eq_right inactive, turn, recorded, ↓reduceIte,
        PMF.mem_support_pure_iff] at supported
      subst action
      cases reserved
    | false =>
      simp only [respond, ite_eq_right inactive, turn, recorded, Bool.false_eq_true,
        ↓reduceIte] at supported
      have named (event : compiled.EventId) (choice : compiled.Action event)
          (chosen : action = ordinaryResponse who retainedPast retainedView event choice) :
          submittedEvent? timeouts OddsEvensService.leaks action = some event := by
        rw [chosen] at reserved ⊢
        rcases canonicalServiceDecision_cases timeouts OddsEvensService.leaks who retainedPast
          retainedView event choice with silent | addressed
        · change responseCandidateSlot timeouts OddsEvensService.leaks
            (canonicalServiceDecision timeouts OddsEvensService.leaks who retainedPast retainedView
              event choice) = some serial at reserved
          rw [silent] at reserved
          cases reserved
        · exact addressed
      change Fin 4 at event
      fin_cases event
      · obtain ⟨bit, _, chosen⟩ := PMF.support_map .. ▸ supported
        have whoEq : who = even := (Option.some.inj owner).symm
        subst who
        exact named (eventId 0) (some (.success bit)) chosen.symm
      · obtain ⟨bit, _, chosen⟩ := PMF.support_map .. ▸ supported
        have whoEq : who = odd := (Option.some.inj owner).symm
        subst who
        exact named (eventId 1) (some (.success bit)) chosen.symm
      · have chosen := (PMF.mem_support_pure_iff _ _).mp supported
        rw [chosen, responseCandidateSlot_of_publication who retainedPast retainedView
          (eventId 2) true rfl] at reserved
        cases reserved
      · have chosen := (PMF.mem_support_pure_iff _ _).mp supported
        rw [chosen, responseCandidateSlot_of_publication who retainedPast retainedView
          (eventId 3) true rfl] at reserved
        cases reserved

/-- A player who has followed its client has reserved no prepared slot before
its own binding submission is recorded. This holds even if the opponent's
behavior is arbitrary. -/
theorem submittedCandidateSlots_eq_nil_of_compatible (who : Player)
    (past : List app.PlayerEntry) (compatible : (policy who).Consistent past)
    (unrecorded : eventRecorded timeouts OddsEvensService.leaks past
      (eventId (if who then 1 else 0)) = false) :
    submittedCandidateSlots timeouts OddsEvensService.leaks past = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro serial member
  obtain ⟨action, actionMember, reserved⟩ := List.mem_filterMap.mp member
  obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp actionMember
  obtain ⟨prior, later, split⟩ := List.append_of_mem entryMember
  have consistent : (policy who).Consistent ((prior ++ [entry]) ++ later) := by
    simpa only [List.append_assoc, List.singleton_append, ← split] using compatible
  have supported := ((ReactiveApplication.Policy.consistent_snoc_iff (policy who)
    prior entry).mp consistent.of_append).2
  have named := candidate_slot_names_binding who prior entry.beforeView entry.action
    supported serial reserved
  have recorded := (eventRecorded_iff timeouts OddsEvensService.leaks past _).mpr
    ⟨entry, entryMember, named⟩
  rw [unrecorded] at recorded
  cases recorded

end Vegas.Examples.OddsEvensLedgerClient
