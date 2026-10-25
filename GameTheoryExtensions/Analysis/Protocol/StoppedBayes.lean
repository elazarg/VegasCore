/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.PassageBayes
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom

/-! # Bayes state beliefs from first passage before a bad event -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type*} [Fintype Player] {E : ExecutionProtocol Player}
  (model : InformationModel E)

open Classical in
private def siteEntry (who : Player) (site : model.InformationSite who)
    (history : E.History) : Option (model.InformationHistory who site.1) :=
  if hit : model.infoOf who history.trace = site.1 then some ⟨history, hit⟩ else none

private theorem stopped_site_ancestor_law
    (certificate : E.WellFoundedHistories) {bound : Nat} (bounded : E.BoundedHorizon bound)
    (profile : ∀ who, model.BehavioralPolicy who) (who : Player)
    (site : model.InformationSite who) (antichain : site.IsHistoryAntichain)
    (bad : E.History → Prop)
    (avoids : ∀ (prior : E.History) (atSite : model.InformationHistory who site.1),
      E.HistoryReaches prior atSite.1 → ¬ bad prior) :
    (model.runBehavioralUntil certificate profile
      (fun history => bad history ∨ model.infoOf who history.trace = site.1)
      E.initHistory).map (siteEntry model who site) =
    (model.runBehavioralTerminalFrom certificate profile E.initHistory).map
      (site.ancestor? model) := by
  classical
  let stopped := fun history => bad history ∨ model.infoOf who history.trace = site.1
  let stoppedLaw := model.runBehavioralUntil certificate profile stopped E.initHistory
  have each (current : E.History) (member : current ∈ stoppedLaw.support)
      (final : E.History)
      (continued : final ∈ (model.runBehavioralTerminalFrom certificate profile current).support) :
      site.ancestor? model final = siteEntry model who site current := by
    have path : E.HistoryReaches current final := by
      rw [model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
        at continued
      exact ⟨bound, model.runBehavioralFrom_reachesWithin profile bound current final continued⟩
    by_cases hit : model.infoOf who current.trace = site.1
    · rw [siteEntry, dite_eq_left hit]
      exact (site.ancestor?_eq_some_iff model antichain final ⟨current, hit⟩).mpr path
    · rw [siteEntry, dite_eq_right hit]
      unfold InformationSite.ancestor?
      split
      · rename_i encountered
        obtain ⟨prior, priorPath⟩ := encountered
        obtain ⟨firstFuel, firstPath⟩ := path
        obtain ⟨secondFuel, secondPath⟩ := priorPath
        by_cases earlier : prior.1.trace.length < current.trace.length
        · have earlierPrefix := (secondPath.ancestor_comparable firstPath earlier.le).tracePrefix
          have first := model.runBehavioralUntil_support_first certificate profile stopped
            E.initHistory current member prior.1 (TracePrefix.start prior.1.trace) earlierPrefix
            earlier
          exact (first (Or.inr prior.2)).elim
        · have after := firstPath.ancestor_comparable secondPath (Nat.le_of_not_gt earlier)
          have ended := model.mem_support_runBehavioralUntil certificate profile stopped
            E.initHistory current member
          rcases ended with failed | terminal
          · rcases failed with failed | same
            · exact (avoids current prior ⟨firstFuel, after⟩ failed).elim
            · exact (hit same).elim
          · cases after with
            | refl => exact (hit prior.2).elim
            | step joint legal realized suffix => exact (legal.1 terminal).elim
      · rfl
  rw [model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate profile stopped,
    PMF.map_bind]
  change stoppedLaw.map (siteEntry model who site) = _
  rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support
  intro current member
  symm
  calc
    _ = (model.runBehavioralTerminalFrom certificate profile current).map
        (fun _ => siteEntry model who site current) :=
      map_congr_on_support _ fun final continued => each current member final continued
    _ = _ := PMF.map_const _ _

private theorem stopped_site_apply
    (certificate : E.WellFoundedHistories) {bound : Nat} (bounded : E.BoundedHorizon bound)
    (profile : ∀ who, model.BehavioralPolicy who) (who : Player)
    (site : model.InformationSite who) (antichain : site.IsHistoryAntichain)
    (bad : E.History → Prop)
    (avoids : ∀ (prior : E.History) (atSite : model.InformationHistory who site.1),
      E.HistoryReaches prior atSite.1 → ¬ bad prior)
    (history : model.InformationHistory who site.1) :
    (model.runBehavioralUntil certificate profile
      (fun history => bad history ∨ model.infoOf who history.trace = site.1)
      E.initHistory) history.1 = model.historyReachWeight profile history.1 := by
  classical
  let stoppedLaw := model.runBehavioralUntil certificate profile
    (fun history => bad history ∨ model.infoOf who history.trace = site.1) E.initHistory
  have passage := stopped_site_ancestor_law model certificate bounded profile who site antichain
    bad avoids
  have entry : (stoppedLaw.map (siteEntry model who site)) (some history) =
      stoppedLaw history.1 := by
    rw [PMF.map_apply, tsum_eq_single history.1]
    · simp only [siteEntry, dite_eq_left history.2, ↓reduceIte]
    · intro other different
      by_cases hit : model.infoOf who other.trace = site.1
      · simp only [siteEntry, dite_eq_left hit]
        rw [ite_eq_right]
        intro equal
        exact different (congrArg Subtype.val (Option.some.inj equal)).symm
      · simp only [siteEntry, dite_eq_right hit, reduceCtorEq, ↓reduceIte]
  rw [← entry, passage]
  exact site.terminal_ancestor_apply model antichain certificate profile history

/-- The first-hit observation probability is exactly the site's information
mass, including zero mass. Only the chosen observation fiber must agree. -/
theorem informationMass_eq_stopped_observation
    (certificate : E.WellFoundedHistories) {bound : Nat} (bounded : E.BoundedHorizon bound)
    (profile : ∀ who, model.BehavioralPolicy who) (who : Player)
    (site : model.InformationSite who) (antichain : site.IsHistoryAntichain)
    (bad : E.History → Prop)
    (avoids : ∀ (prior : E.History) (atSite : model.InformationHistory who site.1),
      E.HistoryReaches prior atSite.1 → ¬ bad prior)
    {Observation : Type*} (observe : E.History → Observation) (observed : Observation)
    (information : ∀ history ∈ (model.runBehavioralUntil certificate profile
      (fun history => bad history ∨ model.infoOf who history.trace = site.1)
      E.initHistory).support,
      model.infoOf who history.trace = site.1 ↔ observe history = observed) :
    ((model.runBehavioralUntil certificate profile
      (fun history => bad history ∨ model.infoOf who history.trace = site.1)
      E.initHistory).map observe) observed = model.informationMass profile who site := by
  classical
  let stoppedLaw := model.runBehavioralUntil certificate profile
    (fun history => bad history ∨ model.infoOf who history.trace = site.1) E.initHistory
  calc
    _ = (stoppedLaw.map (fun history => model.infoOf who history.trace)) site.1 := by
      rw [PMF.map_apply, PMF.map_apply]
      apply tsum_congr
      intro history
      change (if observed = observe history then stoppedLaw history else 0) =
        (if site.1 = model.infoOf who history.trace then stoppedLaw history else 0)
      by_cases supported : history ∈ stoppedLaw.support
      · by_cases hit : model.infoOf who history.trace = site.1
        · rw [ite_eq_left ((information history supported).mp hit).symm,
            ite_eq_left hit.symm]
        · rw [ite_eq_right (fun equal => hit ((information history supported).mpr equal.symm)),
            ite_eq_right (Ne.symm hit)]
      · have zero := (PMF.apply_eq_zero_iff _ _).mpr supported
        simp only [zero, ite_self]
    _ = stoppedLaw.toOuterMeasure {history | model.infoOf who history.trace = site.1} := by
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
      rfl
    _ = ∑' history : model.InformationHistory who site.1, stoppedLaw history.1 := by
      rw [PMF.toOuterMeasure_apply, ← tsum_subtype]
      rfl
    _ = _ := tsum_congr fun history =>
      stopped_site_apply model certificate bounded profile who site antichain bad avoids history

/-- The first-hit posterior before a bad event is the actual Bayes belief
pushed to the retained readout. The bad event need only be absent at ancestors
of this site; a global history bijection and common information depth are unnecessary. -/
theorem bayesBelief_eq_stopped_fiber_map
    (certificate : E.WellFoundedHistories) {bound : Nat} (bounded : E.BoundedHorizon bound)
    (profile : ∀ who, model.BehavioralPolicy who) (who : Player)
    (site : model.InformationSite who) (antichain : site.IsHistoryAntichain)
    (positive : 0 < model.informationMass profile who site)
    (bad : E.History → Prop)
    (avoids : ∀ (prior : E.History) (atSite : model.InformationHistory who site.1),
      E.HistoryReaches prior atSite.1 → ¬ bad prior)
    {State Observation : Type*} (read : E.History → State) (observe : State → Observation)
    (observed : Observation)
    (information : ∀ history ∈ (model.runBehavioralUntil certificate profile
      (fun history => bad history ∨ model.infoOf who history.trace = site.1)
      E.initHistory).support,
      model.infoOf who history.trace = site.1 ↔ observe (read history) = observed) :
    let stopped := model.runBehavioralUntil certificate profile
      (fun history => bad history ∨ model.infoOf who history.trace = site.1) E.initHistory
    fiberPosterior (stopped.map read) observe observed =
      (model.bayesBelief profile who site antichain positive).map
        (fun history => read history.1) := by
  classical
  dsimp only
  let stoppedLaw := model.runBehavioralUntil certificate profile
    (fun history => bad history ∨ model.infoOf who history.trace = site.1) E.initHistory
  have atom := stopped_site_apply model certificate bounded profile who site antichain bad avoids
  have mass := model.informationMass_eq_stopped_observation certificate bounded profile who site
    antichain bad avoids (fun history => model.infoOf who history.trace) site.1
    (fun _history _supported => Iff.rfl)
  have present : site.1 ∈
      (stoppedLaw.map (fun history => model.infoOf who history.trace)).support := by
    rw [PMF.mem_support_iff, mass]
    exact positive.ne'
  have posterior : fiberPosterior stoppedLaw
      (fun history => model.infoOf who history.trace) site.1 =
      (model.bayesBelief profile who site antichain positive).map Subtype.val := by
    ext history
    by_cases hit : model.infoOf who history.trace = site.1
    · rw [fiberPosterior_apply _ _ _ present, Set.indicator_of_mem (show history ∈
          {a | model.infoOf who a.trace = site.1} from hit), mass,
        pmf_map_apply_of_injective _ Subtype.val_injective ⟨history, hit⟩,
        model.bayesBelief_apply]
      rw [atom ⟨history, hit⟩]
      rfl
    · rw [fiberPosterior_apply _ _ _ present, Set.indicator_of_notMem (show history ∉
          {a | model.infoOf who a.trace = site.1} from hit), zero_mul]
      symm
      apply (PMF.apply_eq_zero_iff _ _).mpr
      intro member
      obtain ⟨prior, _supported, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact hit (equal ▸ prior.2)
  have sameFiber : fiberPosterior stoppedLaw
      (fun history => model.infoOf who history.trace) site.1 =
      fiberPosterior stoppedLaw (observe ∘ read) observed :=
    fiberPosterior_eq_of_support_fiber _ _ _ _ _ information
  have readPresent : observed ∈ (stoppedLaw.map (observe ∘ read)).support := by
    obtain ⟨history, supported, hit⟩ := (PMF.mem_support_map_iff _ _ _).mp present
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨history, supported, (information history supported).mp hit⟩
  rw [← map_fiberPosterior_readout stoppedLaw read observe observed readPresent,
    ← sameFiber, posterior, PMF.map_comp]
  rfl

end GameTheory.Protocol.InformationModel
