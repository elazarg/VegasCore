/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveCanonicalMenu
import Vegas.Pending.ReactiveServiceConformance
import Interaction.ReactiveSubmissionSerial

/-! # A candidate continuation menu after locally visible service risk

Own recall remembers unprotected submissions by this player and unprotected
first binding opportunities. They include a ready binding already
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
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bound : graph.EventId → Nat)

/-- An owned event call made outside its protected inclusion window. A
protected call remains clear regardless of prior calls of the same event. -/
def submissionRisk (who : Player)
    (entry : ((reactiveApplication timeouts) leaks).PlayerEntry) : Bool :=
  if entry.beforeView.application.who = who then
    match (submittedEvent? timeouts) leaks entry.action with
    | none => false
    | some event => decide (graph.actor? event = some who) &&
        !decide (entry.beforeView.application.publicView.InclusionFitsDeadline timeouts bound event)
  else false

/-- Persistent private risk in the owner's supplied response recall. -/
def recalledSubmissionRisk (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry) : Bool :=
  past.any ((submissionRisk timeouts) leaks bound who)

@[simp] theorem recalledSubmissionRisk_nil (who : Player) :
    (recalledSubmissionRisk timeouts) leaks bound who [] = false := rfl

open Classical in
/-- A ready binding has no recorded call and its inclusion is no longer
protected. Due-but-unexpired bindings are included: expiry is explicit. This
is tested before choosing a response, not after sending. -/
def firstUnprotectedBindingOpportunity (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) : Bool :=
  if view.application.who = who then
    match view.application.publicView.ownTurn? who with
    | none => false
    | some event =>
        match graph.outputLayout event with
        | .binding _ _ => !timeouts.eventRecorded leaks past event &&
            !decide (view.application.publicView.InclusionFitsDeadline timeouts bound event)
        | _ => false
  else false

theorem firstUnprotectedBindingOpportunity_iff (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    (firstUnprotectedBindingOpportunity timeouts) leaks bound who past view = true ↔
      view.application.who = who ∧ ∃ event owner payload,
        view.application.publicView.ownTurn? who = some event ∧
        graph.outputLayout event = .binding owner payload ∧
        (eventRecorded timeouts) leaks past event = false ∧
        ¬ view.application.publicView.InclusionFitsDeadline timeouts bound event := by
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
    (earlier : List ((reactiveApplication timeouts) leaks).PlayerEntry) :
    List ((reactiveApplication timeouts) leaks).PlayerEntry → Bool
  | [] => false
  | entry :: rest => (firstUnprotectedBindingOpportunity timeouts) leaks bound who earlier
      entry.beforeView || recalledBindingOpportunityRiskFrom who (earlier ++ [entry]) rest

def recalledBindingOpportunityRisk (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry) : Bool :=
  (recalledBindingOpportunityRiskFrom timeouts) leaks bound who [] past

theorem recalledBindingOpportunityRiskFrom_append (who : Player)
    (earlier past extra : List ((reactiveApplication timeouts) leaks).PlayerEntry) :
    (recalledBindingOpportunityRiskFrom timeouts) leaks bound who earlier (past ++ extra) =
      ((recalledBindingOpportunityRiskFrom timeouts) leaks bound who earlier past ||
        (recalledBindingOpportunityRiskFrom timeouts) leaks bound who (earlier ++ past) extra) := by
  induction past generalizing earlier with
  | nil => simp [recalledBindingOpportunityRiskFrom]
  | cons entry rest ih =>
      simp only [List.cons_append, recalledBindingOpportunityRiskFrom, ih,
        Bool.or_assoc, List.append_assoc, List.nil_append]

@[simp] theorem recalledBindingOpportunityRisk_nil (who : Player) :
    (recalledBindingOpportunityRisk timeouts) leaks bound who [] = false := rfl

theorem recalledBindingOpportunityRisk_append (who : Player)
    (past extra : List ((reactiveApplication timeouts) leaks).PlayerEntry) :
    (recalledBindingOpportunityRisk timeouts) leaks bound who (past ++ extra) =
      ((recalledBindingOpportunityRisk timeouts) leaks bound who past ||
        (recalledBindingOpportunityRiskFrom timeouts) leaks bound who past extra) := by
  simpa only [recalledBindingOpportunityRisk, List.nil_append] using
    (recalledBindingOpportunityRiskFrom_append timeouts) leaks bound who [] past extra

/-- Any own response records the opportunity, regardless of its transmission. -/
theorem recalledBindingOpportunityRisk_respond
    (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (response : ((reactiveApplication timeouts) leaks).Action) :
    (recalledBindingOpportunityRisk timeouts) leaks bound who
        ((execution.respond ((reactiveApplication timeouts) leaks) who response).logs who) =
      ((recalledBindingOpportunityRisk timeouts) leaks bound who (execution.logs who) ||
        (firstUnprotectedBindingOpportunity timeouts) leaks bound who (execution.logs who)
          (execution.observe ((reactiveApplication timeouts) leaks) who)) := by
  simp only [ReactiveApplication.Execution.respond, ↓reduceIte,
    (recalledBindingOpportunityRisk_append timeouts), recalledBindingOpportunityRiskFrom,
    Bool.or_false]

theorem recalledBindingOpportunityRisk_respond_clear
    (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (clear : (firstUnprotectedBindingOpportunity timeouts) leaks bound who (execution.logs who)
      (execution.observe ((reactiveApplication timeouts) leaks) who) = false) :
    (recalledBindingOpportunityRisk timeouts) leaks bound who
        ((execution.respond ((reactiveApplication timeouts) leaks) who response).logs who) =
      (recalledBindingOpportunityRisk timeouts) leaks bound who (execution.logs who) := by
  rw [(recalledBindingOpportunityRisk_respond timeouts), clear, Bool.or_false]

/-- The signed envelope a submission would carry, computed from the owner's
recall and current view: the next own serial, the call, the requested evidence
as the owner can resolve it, and the token the public view issues for the
call. -/
def localEnvelope (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (material : ((reactiveApplication timeouts) leaks).Submission) :
    Message Player (WitnessedPacket graph) :=
  ⟨(who, ((reactiveApplication timeouts) leaks).submissionCount past),
    ⟨material.call.packet,
      material.evidence.resolve who (material.call.candidateAfter who view.application.candidates)
        (ReactiveApplication.ResponseMenu.knownPackets past view),
      view.application.publicView.tokenFor material.call.packet⟩⟩

/-- A first submission whose envelope passes the public send-time check at the
current view. Its private material is unrestricted. -/
def ConformantResponse (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action) : Prop :=
  ∃ material, response.transmission = some material ∧
    (firstSubmission timeouts) leaks past response = true ∧
    (freshServiceEnvelope timeouts) view.application.publicView
      ((localEnvelope timeouts) leaks who past view material)

namespace MessageBounds

variable [Fintype Player] (bounds : MessageBounds graph)

open Classical in
/-- The bounded effective responses that are conformant first submissions. -/
def conformantActions (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    Finset ((reactiveApplication timeouts) leaks).Action :=
  ((bounds.menu timeouts leaks).actions who past view).filter
    ((ConformantResponse timeouts) leaks who past view)

theorem mem_conformantActions (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action) :
    response ∈ bounds.conformantActions timeouts leaks who past view ↔
      response ∈ (bounds.menu timeouts leaks).actions who past view ∧
        (ConformantResponse timeouts) leaks who past view response := by
  classical
  simp only [conformantActions, Finset.mem_filter]

open Classical in
/-- The menu at a clear site: canonical responses and conformant first
submissions. -/
def clearActions (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    Finset ((reactiveApplication timeouts) leaks).Action :=
  bounds.canonicalActions timeouts leaks who past view ∪
    bounds.conformantActions timeouts leaks who past view

/-- A clear-site response is canonical, or a bounded effective conformant first
submission. -/
theorem clearActions_cases (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (member : response ∈ bounds.clearActions timeouts leaks who past view) :
    response ∈ bounds.canonicalActions timeouts leaks who past view ∨
      (response ∈ (bounds.menu timeouts leaks).actions who past view ∧
        (ConformantResponse timeouts) leaks who past view response) := by
  classical
  rcases Finset.mem_union.mp member with canonical | conformant
  · exact Or.inl canonical
  · exact Or.inr ((bounds.mem_conformantActions timeouts leaks who past view response).mp
      conformant)

theorem canonicalActions_subset_clear (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    bounds.canonicalActions timeouts leaks who past view ⊆
      bounds.clearActions timeouts leaks who past view := by
  classical
  exact Finset.subset_union_left

theorem clearActions_effective (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    bounds.clearActions timeouts leaks who past view ⊆
      (bounds.menu timeouts leaks).actions who past view := by
  classical
  intro response member
  rcases bounds.clearActions_cases timeouts leaks who past view response member with
    canonical | ⟨effective, _⟩
  · exact bounds.canonicalActions_effective timeouts leaks who past view canonical
  · exact effective

end MessageBounds

end Vegas.EventGraphRuntime
