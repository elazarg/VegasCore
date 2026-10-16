/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseAttemptPassage
import Vegas.Pending.PhaseAttemptEntryStopping
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom

/-! # Actual attempt entry makes information passage a direct stopped hit -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "E" => menu.protocol initial horizon scheduler
local notation "N" => menu.information initial horizon scheduler

/-- A genuine first-entry/first-exit continuation cannot hide an older visit
to the requested full information. Its ancestor readout is the current hit. -/
theorem phase_attempt_first_passage_eq_some
    (certificate : (E).WellFoundedHistories)
    (entryProfile profile : ∀ owner, (N).BehavioralPolicy owner)
    {who : Player} (site : (N).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view))
    (entry ending : (E).History) (atSite : (N).InformationHistory who site.1) :
    let entryStop := fun history : (E).History =>
      phaseAttemptEntryStop runtime leaks view.application.2.attempt history.state
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ view.application.2.attempt ∨
          (N).infoOf who history.trace = site.1
    entry ∈ ((N).runBehavioralUntil certificate entryProfile entryStop (E).initHistory).support →
    ending ∈ ((N).runBehavioralUntil certificate profile stopped entry).support →
      (site.ancestor? (N) ending = some atSite ↔ ending = atSite.1) := by
  classical
  intro entryStop stopped entrySupported supported
  have antichain := menu.decisionInformationAntichain initial horizon scheduler who site
  rw [site.ancestor?_eq_some_iff (N) antichain]
  constructor
  · rintro ⟨fuel, path⟩
    have sitePrefix := path.tracePrefix
    have entryPrefix := (N).runBehavioralUntil_support_prefix certificate profile stopped
      entry ending supported
    have haltEntry : entryStop atSite.1 := by
      obtain ⟨control, state, _excluded, attempt⟩ := phase_information_control_of_view
        runtime leaks menu initial horizon scheduler site past view observed atSite
      simp only [entryStop, phaseAttemptEntryStop, state]
      exact Or.inr attempt
    have haltSegment : stopped atSite.1 := by
      obtain ⟨control, state, _excluded, _attempt⟩ := phase_information_control_of_view
        runtime leaks menu initial horizon scheduler site past view observed atSite
      simp only [stopped, state]
      exact Or.inr (Or.inr atSite.2)
    by_cases earlier : atSite.1.trace.length < entry.trace.length
    · have beforeEntry := (path.ancestor_comparable entryPrefix.reachesWithin
        (Nat.le_of_lt earlier)).tracePrefix
      exact False.elim ((N).runBehavioralUntil_support_first certificate entryProfile entryStop
        (E).initHistory entry entrySupported atSite.1 (TracePrefix.start _) beforeEntry earlier
          haltEntry)
    · have afterEntry := (entryPrefix.reachesWithin.ancestor_comparable path
        (Nat.le_of_not_gt earlier)).tracePrefix
      have noEarlier := (N).runBehavioralUntil_support_first certificate profile stopped entry
        ending supported atSite.1 afterEntry sitePrefix
      have sameLength : atSite.1.trace.length = ending.trace.length := by
        have lower := sitePrefix.length_le
        by_contra different
        exact noEarlier (by omega) haltSegment
      exact (sitePrefix.eq_of_length sameLength).symm
  · intro same
    rw [same]
    exact HistoryReaches.refl (E) atSite.1

/-- At every actual supported first attempt entry, passage through a chosen
information history has exactly its ORIGINAL stopped continuation atom. -/
theorem phase_attempt_first_passage_atom
    (certificate : (E).WellFoundedHistories)
    (entryProfile profile : ∀ owner, (N).BehavioralPolicy owner)
    {who : Player} (site : (N).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view))
    (entry : (E).History) (atSite : (N).InformationHistory who site.1) :
    let entryStop := fun history : (E).History =>
      phaseAttemptEntryStop runtime leaks view.application.2.attempt history.state
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ view.application.2.attempt ∨
          (N).infoOf who history.trace = site.1
    entry ∈ ((N).runBehavioralUntil certificate entryProfile entryStop (E).initHistory).support →
      (((N).runBehavioralUntil certificate profile stopped entry).map
        (site.ancestor? (N))) (some atSite) =
        (N).runBehavioralUntil certificate profile stopped entry atSite.1 := by
  classical
  intro entryStop stopped entrySupported
  let law := (N).runBehavioralUntil certificate profile stopped entry
  have readout := phase_attempt_first_passage_eq_some runtime leaks menu initial horizon scheduler
    certificate entryProfile profile site past view observed entry
  rw [PMF.map_apply, tsum_eq_single atSite.1]
  · have current : site.ancestor? (N) atSite.1 = some atSite :=
      (site.ancestor?_eq_some_iff (N)
        (menu.decisionInformationAntichain initial horizon scheduler who site) _ _).mpr
          (HistoryReaches.refl (E) _)
    simp only [current, ↓reduceIte]
  · intro ending different
    by_cases supported : ending ∈ law.support
    · have absent : site.ancestor? (N) ending ≠ some atSite := by
        intro selected
        exact different ((readout ending atSite entrySupported supported).mp selected)
      simp only [Ne.symm absent, ↓reduceIte]
    · have zero := (PMF.apply_eq_zero_iff _ _).mpr supported
      change law ending = 0 at zero
      split
      · exact zero
      · rfl

end Vegas.EventGraphRuntime
