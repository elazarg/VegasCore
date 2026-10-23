/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCanonicalMenu
import Vegas.Pending.ReactiveServiceAudit
import Vegas.Pending.ReactiveServiceConformance
import Vegas.Pending.EvidenceNormalization
import Interaction.ReactiveMenuRestriction
import Interaction.ReactiveSubmissionSerial

/-! # A candidate continuation menu after locally visible service risk

The public trigger is owner-specific: only `missedBindingBy who` affects
`who`'s menu. Private recall remembers unprotected owned submissions and
unprotected first binding opportunities. They include a ready binding already
due for expiry and open the complete effective menu before the first attempt. Any response
latches the opportunity, including silence or a packet for a foreign event.
Each recorded before-view is tested against the recall prefix preceding it,
so a protected pending submission stays clear.

Persistent risk and the current opportunity are separate. Environment commands
can change the current opportunity without changing own recall. When both are
clear the menu admits the canonical responses and every first submission whose
envelope, computed from own recall and view, passes the public send-time check,
whatever its private material; otherwise it admits every bounded effective
response.
Resolution withholding does not itself trigger expansion: it is represented
by silence and is not a binding opportunity. No trigger reads hidden execution
state, an unsampled packet, or a watcher verdict.

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

/-- Persistent private risk in the owner's supplied response recall. -/
def recalledSubmissionRisk (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry) : Bool :=
  past.any (runtime.submissionRisk leaks bound who)

@[simp] theorem recalledSubmissionRisk_nil (who : Player) :
    runtime.recalledSubmissionRisk leaks bound who [] = false := rfl

open Classical in
/-- A ready binding has no recorded call and its inclusion is no longer
protected. Due-but-unexpired bindings are included: expiry is explicit. This
is tested before choosing a response, not after sending. -/
def firstUnprotectedBindingOpportunity (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) : Bool :=
  if view.application.who = who then
    match view.application.publicView.ownTurn? who with
    | none => false
    | some event =>
        match graph.outputLayout event with
        | .binding _ _ => !runtime.eventRecorded leaks past event &&
            !decide (view.application.publicView.InclusionFitsDeadline runtime bound event)
        | _ => false
  else false

theorem firstUnprotectedBindingOpportunity_iff (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    runtime.firstUnprotectedBindingOpportunity leaks bound who past view = true ↔
      view.application.who = who ∧ ∃ event owner payload,
        view.application.publicView.ownTurn? who = some event ∧
        graph.outputLayout event = .binding owner payload ∧
        runtime.eventRecorded leaks past event = false ∧
        ¬ view.application.publicView.InclusionFitsDeadline runtime bound event := by
  unfold firstUnprotectedBindingOpportunity
  by_cases identity : view.application.who = who
  · simp only [identity, ↓reduceIte, true_and]
    cases selected : view.application.publicView.ownTurn? who with
    | none => simp
    | some event =>
        cases layout : graph.outputLayout event <;> simp [layout]
  · simp only [identity, ↓reduceIte, Bool.false_eq_true, false_and]

/-- Scan before-views using the recall prefix that preceded each response.
The response itself is appended only after testing its opportunity. -/
def recalledBindingOpportunityRiskFrom (who : Player)
    (earlier : List (runtime.reactiveApplication leaks).PlayerEntry) :
    List (runtime.reactiveApplication leaks).PlayerEntry → Bool
  | [] => false
  | entry :: rest => runtime.firstUnprotectedBindingOpportunity leaks bound who earlier
      entry.beforeView || recalledBindingOpportunityRiskFrom who (earlier ++ [entry]) rest

def recalledBindingOpportunityRisk (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry) : Bool :=
  runtime.recalledBindingOpportunityRiskFrom leaks bound who [] past

theorem recalledBindingOpportunityRiskFrom_append (who : Player)
    (earlier past extra : List (runtime.reactiveApplication leaks).PlayerEntry) :
    runtime.recalledBindingOpportunityRiskFrom leaks bound who earlier (past ++ extra) =
      (runtime.recalledBindingOpportunityRiskFrom leaks bound who earlier past ||
        runtime.recalledBindingOpportunityRiskFrom leaks bound who (earlier ++ past) extra) := by
  induction past generalizing earlier with
  | nil => simp [recalledBindingOpportunityRiskFrom]
  | cons entry rest ih =>
      simp only [List.cons_append, recalledBindingOpportunityRiskFrom, ih,
        Bool.or_assoc, List.append_assoc, List.nil_append]

@[simp] theorem recalledBindingOpportunityRisk_nil (who : Player) :
    runtime.recalledBindingOpportunityRisk leaks bound who [] = false := rfl

theorem recalledBindingOpportunityRisk_append (who : Player)
    (past extra : List (runtime.reactiveApplication leaks).PlayerEntry) :
    runtime.recalledBindingOpportunityRisk leaks bound who (past ++ extra) =
      (runtime.recalledBindingOpportunityRisk leaks bound who past ||
        runtime.recalledBindingOpportunityRiskFrom leaks bound who past extra) := by
  simpa only [recalledBindingOpportunityRisk, List.nil_append] using
    runtime.recalledBindingOpportunityRiskFrom_append leaks bound who [] past extra

/-- Any own response records the opportunity, regardless of its transmission. -/
theorem recalledBindingOpportunityRisk_respond
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action) :
    runtime.recalledBindingOpportunityRisk leaks bound who
        ((execution.respond (runtime.reactiveApplication leaks) who response).recall who) =
      (runtime.recalledBindingOpportunityRisk leaks bound who (execution.recall who) ||
        runtime.firstUnprotectedBindingOpportunity leaks bound who (execution.recall who)
          (execution.observe (runtime.reactiveApplication leaks) who)) := by
  simp only [ReactiveApplication.Execution.respond, ↓reduceIte,
    runtime.recalledBindingOpportunityRisk_append, recalledBindingOpportunityRiskFrom,
    Bool.or_false]

theorem recalledBindingOpportunityRisk_respond_clear
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (clear : runtime.firstUnprotectedBindingOpportunity leaks bound who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who) = false) :
    runtime.recalledBindingOpportunityRisk leaks bound who
        ((execution.respond (runtime.reactiveApplication leaks) who response).recall who) =
      runtime.recalledBindingOpportunityRisk leaks bound who (execution.recall who) := by
  rw [runtime.recalledBindingOpportunityRisk_respond, clear, Bool.or_false]

/-- The signed envelope a submission would carry, computed from the owner's
recall and current view: the next own serial, the call, the requested evidence
as the owner can resolve it, and the token the public view issues for the
call. -/
def localEnvelope (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (material : (runtime.reactiveApplication leaks).Submission) :
    Message Player (WitnessedPacket graph) :=
  ⟨(who, (runtime.reactiveApplication leaks).submissionCount past),
    ⟨material.call.packet,
      material.evidence.resolve who (material.call.candidateAfter who view.application.candidates)
        (ReactiveApplication.ResponseMenu.knownPackets past view),
      view.application.publicView.tokenFor material.call.packet⟩⟩

/-- A first submission whose envelope passes the public send-time check at the
current view. Its private material is unrestricted. -/
def ConformantResponse (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) : Prop :=
  ∃ material, response.transmission = some material ∧
    runtime.firstSubmission leaks past response = true ∧
    runtime.freshServiceEnvelope view.application.publicView
      (runtime.localEnvelope leaks who past view material)

namespace MessageBounds

variable [Fintype Player] (bounds : MessageBounds graph)

open Classical in
/-- The bounded effective responses that are conformant first submissions. -/
def conformantActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  ((bounds.menu runtime leaks).actions who past view).filter
    (runtime.ConformantResponse leaks who past view)

theorem mem_conformantActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) :
    response ∈ bounds.conformantActions runtime leaks who past view ↔
      response ∈ (bounds.menu runtime leaks).actions who past view ∧
        runtime.ConformantResponse leaks who past view response := by
  classical
  simp only [conformantActions, Finset.mem_filter]

open Classical in
/-- The menu at a clear site: canonical responses and conformant first
submissions. -/
def clearActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  bounds.canonicalActions runtime leaks who past view ∪
    bounds.conformantActions runtime leaks who past view

/-- A clear-site response is canonical, or a bounded effective conformant first
submission. -/
theorem clearActions_cases (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.clearActions runtime leaks who past view) :
    response ∈ bounds.canonicalActions runtime leaks who past view ∨
      (response ∈ (bounds.menu runtime leaks).actions who past view ∧
        runtime.ConformantResponse leaks who past view response) := by
  classical
  rcases Finset.mem_union.mp member with canonical | conformant
  · exact Or.inl canonical
  · exact Or.inr ((bounds.mem_conformantActions runtime leaks who past view response).mp
      conformant)

theorem canonicalActions_subset_clear (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    bounds.canonicalActions runtime leaks who past view ⊆
      bounds.clearActions runtime leaks who past view := by
  classical
  exact Finset.subset_union_left

theorem clearActions_effective (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    bounds.clearActions runtime leaks who past view ⊆
      (bounds.menu runtime leaks).actions who past view := by
  classical
  intro response member
  rcases bounds.clearActions_cases runtime leaks who past view response member with
    canonical | ⟨effective, _⟩
  · exact bounds.canonicalActions_effective runtime leaks who past view canonical
  · exact effective

end MessageBounds

end Vegas.EventGraphRuntime
