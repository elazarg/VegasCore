/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCanonicalMenu
import Vegas.Pending.ReactiveServiceAudit
import Interaction.ReactiveMenuRestriction

/-! # A candidate continuation menu after locally visible service risk

The public trigger is owner-specific: only `missedBindingBy who` affects
`who`'s menu. The private trigger reads that owner's response recall. An entry
must identify the owner in its before-view, submit an event owned by that
player, and fail that event's protected inclusion window in the before-view.
It uses no hidden execution state, unsampled packet, or watcher verdict.

Before either trigger the candidate menu is the canonical menu. After a
trigger it admits every bounded raw response. A protected submission does not
itself trigger expansion, even when another submission of its event was
already recorded. At a clear history the canonical first-submission rule still
excludes retries.

These are local menu and recall facts for a candidate one-escrow continuation
design. The trigger alone does not establish a collected charge or that
expected collection is constant across continuations. No equilibrium theorem
is asserted here.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bound : graph.EventId → Nat)

/-- The actual local fields needed to test one recalled submission. The
emitted envelope, pending-message sample, and receipts are not consulted. -/
def submissionRiskRecord (entry : (runtime.reactiveApplication leaks).PlayerEntry) :
    Player × PublicView graph × Option graph.EventId :=
  (entry.beforeView.application.who, entry.beforeView.application.publicView,
    runtime.submittedEvent? leaks entry.action)

/-- An owned event call made outside its protected inclusion window. A
protected call remains clear regardless of prior calls of the same event. -/
def submissionRisk (who : Player)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) : Bool :=
  if entry.beforeView.application.who = who then
    match runtime.submittedEvent? leaks entry.action with
    | none => false
    | some event => decide (graph.actor? event = some who) &&
        !decide (entry.beforeView.application.publicView.InclusionFitsDeadline runtime bound event)
  else false

theorem submissionRisk_iff (who : Player)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) :
    runtime.submissionRisk leaks bound who entry = true ↔
      entry.beforeView.application.who = who ∧
        ∃ event, runtime.submittedEvent? leaks entry.action = some event ∧
          graph.actor? event = some who ∧
          ¬ entry.beforeView.application.publicView.InclusionFitsDeadline runtime bound event := by
  unfold submissionRisk
  by_cases identity : entry.beforeView.application.who = who
  · simp only [identity, ↓reduceIte, true_and]
    cases named : runtime.submittedEvent? leaks entry.action with
    | none => simp
    | some event => simp
  · simp only [identity, ↓reduceIte, Bool.false_eq_true, false_and]

theorem submissionRisk_congr (who : Player)
    (left right : (runtime.reactiveApplication leaks).PlayerEntry)
    (same : runtime.submissionRiskRecord leaks left = runtime.submissionRiskRecord leaks right) :
    runtime.submissionRisk leaks bound who left = runtime.submissionRisk leaks bound who right := by
  have identity := congrArg (fun record : Player × PublicView graph × Option graph.EventId =>
    record.1) same
  have publicViewEq := congrArg (fun record : Player × PublicView graph × Option graph.EventId =>
    record.2.1) same
  have named := congrArg (fun record : Player × PublicView graph × Option graph.EventId =>
    record.2.2) same
  change left.beforeView.application.who = right.beforeView.application.who at identity
  change left.beforeView.application.publicView =
    right.beforeView.application.publicView at publicViewEq
  change runtime.submittedEvent? leaks left.action =
    runtime.submittedEvent? leaks right.action at named
  simp only [submissionRisk, identity, publicViewEq, named]

theorem submissionRisk_none (who : Player)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (silent : runtime.submittedEvent? leaks entry.action = none) :
    runtime.submissionRisk leaks bound who entry = false := by
  simp only [submissionRisk, silent, ite_self]

/-- A recorded protected submission contributes no private risk. This fact
does not require that it was the first submission of its event. -/
theorem submissionRisk_protected (who : Player)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) (event : graph.EventId)
    (named : runtime.submittedEvent? leaks entry.action = some event)
    (fits : entry.beforeView.application.publicView.InclusionFitsDeadline runtime bound event) :
    runtime.submissionRisk leaks bound who entry = false := by
  simp only [submissionRisk, named, fits, decide_true, Bool.not_true, Bool.and_false, ite_self]

/-- Persistent private risk in the owner's supplied response recall. -/
def recalledSubmissionRisk (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry) : Bool :=
  past.any (runtime.submissionRisk leaks bound who)

theorem recalledSubmissionRisk_iff (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry) :
    runtime.recalledSubmissionRisk leaks bound who past = true ↔
      ∃ entry ∈ past, entry.beforeView.application.who = who ∧
        ∃ event, runtime.submittedEvent? leaks entry.action = some event ∧
          graph.actor? event = some who ∧
          ¬ entry.beforeView.application.publicView.InclusionFitsDeadline runtime bound event := by
  simp only [recalledSubmissionRisk, List.any_eq_true, runtime.submissionRisk_iff]

/-- Only the owner's identity, public before-views and submitted event names
enter the private risk test. Hidden packet state and emitted envelopes do not. -/
theorem recalledSubmissionRisk_congr (who : Player)
    (left right : List (runtime.reactiveApplication leaks).PlayerEntry)
    (same : left.map (runtime.submissionRiskRecord leaks) =
      right.map (runtime.submissionRiskRecord leaks)) :
    runtime.recalledSubmissionRisk leaks bound who left =
      runtime.recalledSubmissionRisk leaks bound who right := by
  have observed := congrArg (fun records :
      List (Player × PublicView graph × Option graph.EventId) =>
    records.any fun record => if record.1 = who then
      match record.2.2 with
      | none => false
      | some event => decide (graph.actor? event = some who) &&
          !decide (record.2.1.InclusionFitsDeadline runtime bound event)
      else false) same
  simp only [submissionRiskRecord, List.any_map, Function.comp_def] at observed
  exact observed

@[simp] theorem recalledSubmissionRisk_nil (who : Player) :
    runtime.recalledSubmissionRisk leaks bound who [] = false := rfl

theorem recalledSubmissionRisk_append (who : Player)
    (past extra : List (runtime.reactiveApplication leaks).PlayerEntry) :
    runtime.recalledSubmissionRisk leaks bound who (past ++ extra) =
      (runtime.recalledSubmissionRisk leaks bound who past ||
        runtime.recalledSubmissionRisk leaks bound who extra) :=
  List.any_append

/-- Appending later own recall cannot remove an earlier private risk witness. -/
theorem recalledSubmissionRisk_mono (who : Player)
    (past extra : List (runtime.reactiveApplication leaks).PlayerEntry)
    (risky : runtime.recalledSubmissionRisk leaks bound who past = true) :
    runtime.recalledSubmissionRisk leaks bound who (past ++ extra) = true := by
  rw [runtime.recalledSubmissionRisk_append, risky, Bool.true_or]

theorem recalledSubmissionRisk_prefix (who : Player)
    (past later : List (runtime.reactiveApplication leaks).PlayerEntry)
    (prefixOf : past <+: later)
    (risky : runtime.recalledSubmissionRisk leaks bound who past = true) :
    runtime.recalledSubmissionRisk leaks bound who later = true := by
  obtain ⟨extra, rfl⟩ := prefixOf
  exact runtime.recalledSubmissionRisk_mono leaks bound who past extra risky

/-- Recall consisting only of protected owned submissions has no private risk.
Silent responses and submissions naming foreign events need no protection premise. -/
theorem recalledSubmissionRisk_clear (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (allFit : ∀ entry ∈ past, entry.beforeView.application.who = who →
      ∀ event, runtime.submittedEvent? leaks entry.action = some event →
        graph.actor? event = some who →
          entry.beforeView.application.publicView.InclusionFitsDeadline runtime bound event) :
    runtime.recalledSubmissionRisk leaks bound who past = false := by
  apply Bool.eq_false_of_not_eq_true
  rintro risky
  obtain ⟨entry, present, identity, event, named, owned, unprotected⟩ :=
    (runtime.recalledSubmissionRisk_iff leaks bound who past).mp risky
  exact unprotected (allFit entry present identity event named owned)

theorem recalledSubmissionRisk_clear_iff (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry) :
    runtime.recalledSubmissionRisk leaks bound who past = false ↔
      ∀ entry ∈ past, entry.beforeView.application.who = who →
        ∀ event, runtime.submittedEvent? leaks entry.action = some event →
          graph.actor? event = some who →
            entry.beforeView.application.publicView.InclusionFitsDeadline runtime bound event := by
  constructor
  · intro clear entry present identity event named owned
    by_contra unprotected
    have risky := (runtime.recalledSubmissionRisk_iff leaks bound who past).mpr
      ⟨entry, present, identity, event, named, owned, unprotected⟩
    rw [clear] at risky
    cases risky
  · exact runtime.recalledSubmissionRisk_clear leaks bound who past

/-- Appending clear entries preserves the private risk flag exactly. -/
theorem recalledSubmissionRisk_append_clear (who : Player)
    (past extra : List (runtime.reactiveApplication leaks).PlayerEntry)
    (clear : ∀ entry ∈ extra, runtime.submissionRisk leaks bound who entry = false) :
    runtime.recalledSubmissionRisk leaks bound who (past ++ extra) =
      runtime.recalledSubmissionRisk leaks bound who past := by
  have extraClear : runtime.recalledSubmissionRisk leaks bound who extra = false :=
    List.any_eq_false.mpr fun entry present => Bool.eq_false_iff.mp (clear entry present)
  rw [runtime.recalledSubmissionRisk_append, extraClear, Bool.or_false]

/-- An actual protected response cannot add private risk to its author's
recall. Protection concerns the recorded before-view, not later inclusion. -/
theorem recalledSubmissionRisk_respond_protected
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (allFit : ∀ event, runtime.submittedEvent? leaks response = some event →
      PublicView.InclusionFitsDeadline runtime bound
        (execution.observe (runtime.reactiveApplication leaks) who).application.publicView event) :
    runtime.recalledSubmissionRisk leaks bound who
        ((execution.respond (runtime.reactiveApplication leaks) who response).recall who) =
      runtime.recalledSubmissionRisk leaks bound who (execution.recall who) := by
  have entryClear : ∀ emitted, runtime.submissionRisk leaks bound who
      ⟨execution.observe (runtime.reactiveApplication leaks) who, response, emitted⟩ = false := by
    intro emitted
    cases named : runtime.submittedEvent? leaks response with
    | none => exact runtime.submissionRisk_none leaks bound who _ named
    | some event =>
        exact runtime.submissionRisk_protected leaks bound who _ event named (allFit event named)
  obtain ⟨transmission⟩ := response
  cases transmission <;>
    simp only [recalledSubmissionRisk, ReactiveApplication.Execution.respond, ↓reduceIte,
      List.any_append, List.any_cons, List.any_nil, entryClear, Bool.or_false]

/-- The menu expansion signal uses only this owner's public miss and own recall. -/
def serviceRisk (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) : Bool :=
  view.application.publicView.missedBindingBy who ||
    runtime.recalledSubmissionRisk leaks bound who past

theorem serviceRisk_iff (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    runtime.serviceRisk leaks bound who past view = true ↔
      view.application.publicView.missedBindingBy who = true ∨
        runtime.recalledSubmissionRisk leaks bound who past = true :=
  by simp only [serviceRisk, Bool.or_eq_true]

theorem serviceRisk_clear_iff (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    runtime.serviceRisk leaks bound who past view = false ↔
      view.application.publicView.missedBindingBy who = false ∧
        runtime.recalledSubmissionRisk leaks bound who past = false := by
  unfold serviceRisk
  cases view.application.publicView.missedBindingBy who <;>
    cases runtime.recalledSubmissionRisk leaks bound who past <;> simp

theorem serviceRisk_clear (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (publicClear : view.application.publicView.missedBindingBy who = false)
    (privateClear : runtime.recalledSubmissionRisk leaks bound who past = false) :
    runtime.serviceRisk leaks bound who past view = false := by
  simp only [serviceRisk, publicClear, privateClear, Bool.false_or]

/-- The expansion flag is determined by public miss data and the owner's
local risk records, independent of all other fields of the observations. -/
theorem serviceRisk_congr (who : Player)
    (leftPast rightPast : List (runtime.reactiveApplication leaks).PlayerEntry)
    (leftView rightView : (runtime.reactiveApplication leaks).PlayerView)
    (publicEq : leftView.application.publicView = rightView.application.publicView)
    (recallEq : leftPast.map (runtime.submissionRiskRecord leaks) =
      rightPast.map (runtime.submissionRiskRecord leaks)) :
    runtime.serviceRisk leaks bound who leftPast leftView =
      runtime.serviceRisk leaks bound who rightPast rightView := by
  have privateEq := runtime.recalledSubmissionRisk_congr leaks bound who leftPast rightPast recallEq
  simp only [serviceRisk, publicEq, privateEq]

/-- An actual protected response changes neither the public miss signal nor
the author's recalled risk signal. -/
theorem serviceRisk_respond_protected
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (allFit : ∀ event, runtime.submittedEvent? leaks response = some event →
      PublicView.InclusionFitsDeadline runtime bound
        (execution.observe (runtime.reactiveApplication leaks) who).application.publicView event) :
    runtime.serviceRisk leaks bound who
        ((execution.respond (runtime.reactiveApplication leaks) who response).recall who)
        ((execution.respond (runtime.reactiveApplication leaks) who response).observe
          (runtime.reactiveApplication leaks) who) =
      runtime.serviceRisk leaks bound who (execution.recall who)
        (execution.observe (runtime.reactiveApplication leaks) who) := by
  have publicEq := (runtime.reactive_respond_application leaks execution who response).2
  have privateEq := runtime.recalledSubmissionRisk_respond_protected leaks bound execution who
    response allFit
  exact congrArg₂ (fun publicFlag privateFlag : Bool => publicFlag || privateFlag)
    (congrArg (fun view : PublicView graph => view.missedBindingBy who) publicEq) privateEq

theorem serviceRisk_of_public_miss (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (missed : view.application.publicView.missedBindingBy who = true) :
    runtime.serviceRisk leaks bound who past view = true := by
  simp only [serviceRisk, missed, Bool.true_or]

theorem serviceRisk_of_recalled (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (risky : runtime.recalledSubmissionRisk leaks bound who past = true) :
    runtime.serviceRisk leaks bound who past view = true := by
  simp only [serviceRisk, risky, Bool.or_true]

namespace MessageBounds

variable [Fintype Player] (bounds : MessageBounds graph)

/-- Canonical responses remain bounded before expansion. -/
theorem canonicalActions_raw (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    bounds.canonicalActions runtime leaks who past view ⊆
      (bounds.rawMenu runtime leaks).actions who past view := by
  intro response member
  obtain ⟨original, allowed, normal⟩ := (runtime.reactiveNormalization leaks).menu_mem
    (bounds.rawMenu runtime leaks) who past view response |>.mp
      (bounds.canonicalActions_effective runtime leaks who past view member)
  rw [← normal]
  exact bounds.rawMenu_closed runtime leaks who past view original allowed

/-- Candidate menu: canonical actions while clear, all bounded raw actions
after this owner's public miss or private recalled service risk. -/
def riskActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  if runtime.serviceRisk leaks bound who past view then
    (bounds.rawMenu runtime leaks).actions who past view
  else bounds.canonicalActions runtime leaks who past view

theorem riskActions_of_clear (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (clear : runtime.serviceRisk leaks bound who past view = false) :
    bounds.riskActions runtime leaks bound who past view =
      bounds.canonicalActions runtime leaks who past view := by
  simp only [riskActions, clear, Bool.false_eq_true, ↓reduceIte]

theorem riskActions_of_risk (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (risky : runtime.serviceRisk leaks bound who past view = true) :
    bounds.riskActions runtime leaks bound who past view =
      (bounds.rawMenu runtime leaks).actions who past view := by
  simp only [riskActions, risky, ↓reduceIte]

theorem riskActions_raw (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    bounds.riskActions runtime leaks bound who past view ⊆
      (bounds.rawMenu runtime leaks).actions who past view := by
  unfold riskActions
  split
  · exact Finset.Subset.refl _
  · exact bounds.canonicalActions_raw runtime leaks who past view

theorem canonicalActions_subset_risk (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    bounds.canonicalActions runtime leaks who past view ⊆
      bounds.riskActions runtime leaks bound who past view := by
  unfold riskActions
  split
  · exact bounds.canonicalActions_raw runtime leaks who past view
  · exact Finset.Subset.refl _

theorem riskActions_no_second_submission (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (clear : runtime.serviceRisk leaks bound who past view = false)
    (event : graph.EventId) (recorded : runtime.eventRecorded leaks past event = true)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.riskActions runtime leaks bound who past view) :
    runtime.submittedEvent? leaks response ≠ some event := by
  rw [bounds.riskActions_of_clear runtime leaks bound who past view clear] at member
  exact bounds.canonical_no_second_submission runtime leaks who past view event recorded
    response member

def riskMenu : (runtime.reactiveApplication leaks).ResponseMenu where
  actions := bounds.riskActions runtime leaks bound
  nonempty who past view := by
    unfold riskActions
    split
    · exact (bounds.rawMenu runtime leaks).nonempty who past view
    · exact bounds.canonicalActions_nonempty runtime leaks who past view

theorem riskMenu_in_raw :
    (bounds.riskMenu runtime leaks bound).IncludedIn (bounds.rawMenu runtime leaks) :=
  bounds.riskActions_raw runtime leaks bound

theorem canonicalMenu_in_risk :
    (bounds.canonicalMenu runtime leaks).IncludedIn (bounds.riskMenu runtime leaks bound) :=
  bounds.canonicalActions_subset_risk runtime leaks bound

end MessageBounds

end Vegas.EventGraphRuntime
