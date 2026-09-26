/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.FiniteInformation

/-! # Recall at genuine decision information sets

Only information sets where a player can act need determine its earlier
information and actions. Inactive observations may be shared across histories
with different own-play records. This premise adds no observations or memory
operations to the protocol.
-/

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol

variable {Player : Type*} {E : ExecutionProtocol Player} (M : InformationModel E)

/-- Histories in each genuine decision fiber have the same own-play record. -/
def DecisionRecall : Prop :=
  ∀ (who : Player) (site : M.InformationSite who)
    (first second : M.InformationHistory who site.1),
    M.ownPlay who first.1.trace = M.ownPlay who second.1.trace

theorem decisionRecall_of_perfectRecall (recall : M.PerfectRecall) : M.DecisionRecall := by
  intro who site first second
  exact recall who _ _ (first.2.trans second.2.symm)

private theorem shorter_prior_record (who : Player) :
    ∀ {state : E.State} (trace : E.Trace state) {info : M.InfoState who},
      info ∈ M.actedAt who trace →
        ∃ earlier : E.History, M.infoOf who earlier.trace = info ∧
          (M.ownPlay who earlier.trace).length < (M.ownPlay who trace).length
  | _, .start, _, member => by cases member
  | _, .extend prior joint legal realized, info, member => by
      cases chosen : joint who with
      | none =>
          simp only [InfoSignals.actedAt, chosen] at member
          obtain ⟨earlier, same, shorter⟩ := shorter_prior_record who prior member
          exact ⟨earlier, same, by simpa only [InfoSignals.ownPlay, chosen] using shorter⟩
      | some action =>
          simp only [InfoSignals.actedAt, chosen, List.mem_cons] at member
          rcases member with same | member
          · subst info
            refine ⟨⟨_, prior⟩, rfl, ?_⟩
            simp only [InfoSignals.ownPlay, chosen, List.length_cons]
            exact Nat.lt_succ_self _
          · obtain ⟨earlier, same, shorter⟩ := shorter_prior_record who prior member
            refine ⟨earlier, same, ?_⟩
            simp only [InfoSignals.ownPlay, chosen, List.length_cons]
            exact Nat.lt_succ_of_lt shorter

namespace DecisionRecall

variable {M} (recall : M.DecisionRecall)

include recall

/-- The arbitrary representative used by `recordAt` is sound at decisions. -/
theorem recordAt_eq_ownPlay (who : Player) (site : M.InformationSite who)
    (history : M.InformationHistory who site.1) :
    M.recordAt who site.1 = M.ownPlay who history.1.trace := by
  have reached : ∃ other : E.History, M.infoOf who other.trace = site.1 :=
    ⟨history.1, history.2⟩
  rw [InformationModel.recordAt, dite_eq_left reached]
  exact recall who site ⟨_, Classical.choose_spec reached⟩ history

theorem recordAt_eq_ownPlay_of_active (who : Player) (history : E.History)
    (running : ¬ E.terminal history.state) (active : E.active history.state who) :
    M.recordAt who (M.infoOf who history.trace) = M.ownPlay who history.trace := by
  obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history running active
  rw [← same]
  exact recall.recordAt_eq_ownPlay who site ⟨history, same.symm⟩

/-- Once a player acts, the decision information cannot recur. -/
theorem infoOf_ne_after_step (who : Player)
    {history later : E.History} {fuel : Nat}
    {joint : ∀ player, Option (E.Action player)} (legal : E.Legal history.state joint)
    {next : E.State} (realized : next ∈ (E.step history.state ⟨joint, legal⟩).support)
    (active : E.active history.state who)
    (path : E.ReachesWithin fuel (history.extend legal realized) later) :
    M.infoOf who later.trace ≠ M.infoOf who history.trace := by
  intro same
  obtain ⟨action, chosen⟩ :=
    (E.legalOption_of_legal legal who).exists_eq_some_of_active (joint who) active
  have permitted : some action ∈ M.menu who (M.infoOf who history.trace) := by
    rw [← chosen]
    exact (M.menu_adequate who history.trace _).mpr (E.legalOption_of_legal legal who)
  let site := M.informationSite who history action legal.1 permitted
  have own := recall who site ⟨history, rfl⟩ ⟨later, same⟩
  change M.ownPlay who history.trace = M.ownPlay who later.trace at own
  have length := (M.ownPlay_isSuffix_of_reachesWithin who path).length_le
  simp only [History.extend, InfoSignals.ownPlay_extend, chosen, List.length_cons] at length
  rw [← own] at length
  omega

theorem antichain : M.DecisionInformationAntichain := by
  intro who site first second joint legal next realized fuel path
  exact recall.infoOf_ne_after_step who legal realized (InformationSite.active M site first)
    path (second.2.trans first.2.symm)

/-- Every actual own-action record has distinct information states. -/
theorem actsOnce : M.ActsOnceAtEachInfoState := by
  intro who state trace
  induction trace with
  | start => simp [InfoSignals.actedAt]
  | @extend before after prior joint legal realized ih =>
      cases chosen : joint who with
      | none => simpa only [InfoSignals.actedAt, chosen] using ih
      | some action =>
          simp only [InfoSignals.actedAt, chosen, List.nodup_cons]
          refine ⟨?_, ih⟩
          intro member
          obtain ⟨earlier, same, shorter⟩ := M.shorter_prior_record who prior member
          have permitted : some action ∈ M.menu who (M.infoOf who prior) := by
            rw [← chosen]
            exact (M.menu_adequate who prior _).mpr (E.legalOption_of_legal legal who)
          let site := M.informationSite who ⟨before, prior⟩ action legal.1 permitted
          have own := recall who site ⟨earlier, same⟩ ⟨⟨before, prior⟩, rfl⟩
          change M.ownPlay who earlier.trace = M.ownPlay who prior at own
          rw [own] at shorter
          exact (Nat.lt_irrefl _ shorter)

theorem actsOnceWhereItMatters : M.ActsOnceWhereItMatters :=
  M.actsOnceWhereItMatters_of_actsOnce recall.actsOnce

end DecisionRecall
end GameTheory.Protocol.InformationModel
