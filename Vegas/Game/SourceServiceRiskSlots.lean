/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRetainedSlots
import Vegas.Pending.ReactiveRiskPersistence

/-! # Owner-local canonical slots at clear risk-menu histories

A clear persistent risk signal implies that the owner's earlier responses
were canonical. Own recall latches every unprotected first owned opportunity,
even when the chosen response is silent or names a foreign event. Current
opportunities can change between responses, so they are not assumed persistent.
Other owners may use every raw response admitted by their expanded menus.

The result is the counted-slot invariant and freshness for the clear owner,
without requiring a globally canonical history or excluding other owners'
public misses. No charge or equilibrium conclusion follows from these facts.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private def ownerPersistentRisk (bound : (graph setup).EventId → Nat)
    (execution : (application setup leaks).Execution) (who : Player) : Bool :=
  (runtime setup).persistentServiceRisk leaks bound who (execution.recall who)
    (execution.observe (application setup leaks) who)

/-- Every named submission on the prescribed policy's support passes its
protection gate, regardless of the selected turn index or source profile. -/
theorem sourceServiceTurnPolicy_submissionFits
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {timing : TurnTiming setup turns} {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {response : (application setup leaks).Action}
    (chosen : response ∈
      (sourceServiceTurnPolicy setup leaks bound turns timing profile who past view).support)
    (event : (graph setup).EventId)
    (submitted : (runtime setup).submittedEvent? leaks response = some event) :
    view.application.publicView.InclusionFitsDeadline (runtime setup) bound event := by
  have transmission : ∃ material, response.transmission = some material := by
    cases emitted : response.transmission with
    | none => simp [EventGraphRuntime.submittedEvent?, emitted] at submitted
    | some material => exact ⟨material, rfl⟩
  obtain ⟨material, emitted⟩ := transmission
  obtain ⟨chosenEvent, action, _, _, fits, rfl⟩ :=
    sourceServiceTurnPolicy_submission chosen emitted
  rw [submittedEvent_canonicalServiceDecision setup leaks who past view chosenEvent action event
    submitted]
  exact fits

/-- An actual prescribed submission is at a protected own turn, so its
before-view cannot be an unprotected first owned opportunity. This premise
concerns a submission; it is not inferred from silence or deferred turns. -/
theorem sourceServiceTurnPolicy_submitting_opportunityClear
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {timing : TurnTiming setup turns} {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {response : (application setup leaks).Action}
    (chosen : response ∈
      (sourceServiceTurnPolicy setup leaks bound turns timing profile who past view).support)
    {material : (application setup leaks).Submission}
    (submits : response.transmission = some material) :
    (runtime setup).firstUnprotectedOpportunity leaks bound who past view = false := by
  obtain ⟨event, _, turn, _, fits, _⟩ := sourceServiceTurnPolicy_submission chosen submits
  exact (runtime setup).firstUnprotectedOpportunity_protected leaks bound who past view
    event turn fits

/-- A prescribed protected first binding response, and every other actual
prescribed submission, adds no opportunity-risk record to the owner's recall. -/
theorem sourceServiceTurnPolicy_submitting_no_opportunityRecall
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {timing : TurnTiming setup turns} {profile : BehavioralProfile setup.program}
    (execution : (application setup leaks).Execution) (who : Player)
    {response : (application setup leaks).Action}
    (chosen : response ∈ (sourceServiceTurnPolicy setup leaks bound turns timing profile who
      (execution.recall who) (execution.observe (application setup leaks) who)).support)
    {material : (application setup leaks).Submission}
    (submits : response.transmission = some material) :
    (runtime setup).recalledOpportunityRisk leaks bound who
        ((execution.respond (application setup leaks) who response).recall who) =
      (runtime setup).recalledOpportunityRisk leaks bound who (execution.recall who) :=
  (runtime setup).recalledOpportunityRisk_respond_clear leaks bound execution who response
    (sourceServiceTurnPolicy_submitting_opportunityClear chosen submits)

/-- Following the prescribed policy cannot introduce recalled submission risk.
This component is separate from opportunity risk: late deferral can latch an
unprotected owned opportunity even when it submits nothing. Foreign responses
and every environment command, including chance, preserve own recall. -/
theorem sourceServiceTurnPolicy_recalledSubmissionRiskInvariant
    (players : Player → (application setup leaks).Policy) (who : Player)
    {bound : (graph setup).EventId → Nat} {turns : Nat} (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who) :
    (application setup leaks).PolicyInvariant players (fun execution =>
      (runtime setup).recalledSubmissionRisk leaks bound who (execution.recall who) = false) where
  respond execution actor response clear chosen := by
    by_cases same : actor = who
    · subst actor
      rw [follows] at chosen
      exact ((runtime setup).recalledSubmissionRisk_respond_protected leaks bound execution who
        response (sourceServiceTurnPolicy_submissionFits chosen)).trans clear
    · have different : who ≠ actor := fun equal => same equal.symm
      rw [(application setup leaks).respond_recall_other execution actor who different response]
      exact clear
  environment execution next command clear moved := by
    rw [(application setup leaks).environmentStep_recall execution next command moved]
    exact clear

/-- The actual submission-risk component stays clear along any number of
prescribed rounds. Opportunity risk and public decision misses are separate. -/
theorem sourceServiceTurnPolicy_recalledSubmissionRisk_roundsFrom
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {bound : (graph setup).EventId → Nat} {turns : Nat} (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (count : Nat) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    (runtime setup).recalledSubmissionRisk leaks bound who (execution.recall who) = false := by
  obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have invariant := sourceServiceTurnPolicy_recalledSubmissionRiskInvariant players who timing
    profile follows
  exact invariant.runRounds scheduler count _ execution
    ((runtime setup).recalledSubmissionRisk_nil leaks bound who) supported

/-- Also covers the intermediate execution before an activated player responds,
so the flag here reads the current private recall rather than a prior boundary. -/
theorem sourceServiceTurnPolicy_recalledSubmissionRisk_roundSupported
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {bound : (graph setup).EventId → Nat} {turns : Nat} (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (horizon : Nat) (control : (application setup leaks).Control)
    (reached : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some control)) :
    (runtime setup).recalledSubmissionRisk leaks bound who
      (control.execution.recall who) = false := by
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      exact sourceServiceTurnPolicy_recalledSubmissionRisk_roundsFrom scheduler players who timing
        profile follows _ execution reached.2
  | some responder =>
      obtain ⟨_, count, prior, command, _, priorMem, _, _, moved⟩ := reached
      rw [(application setup leaks).environmentStep_recall prior execution command moved]
      exact sourceServiceTurnPolicy_recalledSubmissionRisk_roundsFrom scheduler players who timing
        profile follows count prior priorMem

variable [Fintype Player]
  (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)

omit [Fintype Player] in
/-- A real environment transition preserves the owner's conditional slot
resources. Foreign actions and current transient opportunity changes do not
require a globally retained history. -/
theorem riskCanonicalSlots_environment
    (execution next : (application setup leaks).Execution) (who : Player)
    (command : (application setup leaks).Command)
    (prior : (runtime setup).persistentServiceRisk leaks bound who (execution.recall who)
        (execution.observe (application setup leaks) who) = false →
      OwnSubmissionsAtTurn setup leaks execution who ∧ CanonicalSlotsUsed setup leaks execution who)
    (clear : (runtime setup).persistentServiceRisk leaks bound who (next.recall who)
      (next.observe (application setup leaks) who) = false)
    (moved : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    OwnSubmissionsAtTurn setup leaks next who ∧ CanonicalSlotsUsed setup leaks next who := by
  obtain ⟨atTurn, slots⟩ := prior
    ((runtime setup).persistentServiceRisk_clear_before_environment leaks bound who clear moved)
  have recallEq := (application setup leaks).environmentStep_recall execution next command moved
  refine ⟨?_, canonicalSlotsUsed_environment moved who slots⟩
  unfold OwnSubmissionsAtTurn
  rwa [recallEq]

/-- A real response preserves the owner's conditional slot resources when its
actual focal response belongs to the risk menu. Foreign responses are arbitrary.
The local membership is consumed at this transition, not assumed for a future
policy or inferred from a frame. -/
theorem riskCanonicalSlots_respond
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who responder : Player)
    (response : (application setup leaks).Action)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some responder, execution⟩))
    (prior : (runtime setup).persistentServiceRisk leaks bound who (execution.recall who)
        (execution.observe (application setup leaks) who) = false →
      OwnSubmissionsAtTurn setup leaks execution who ∧ CanonicalSlotsUsed setup leaks execution who)
    (member : responder = who → response ∈ bounds.riskActions (runtime setup) leaks bound who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (clear : (runtime setup).persistentServiceRisk leaks bound who
      ((execution.respond (application setup leaks) responder response).recall who)
      ((execution.respond (application setup leaks) responder response).observe
        (application setup leaks) who) = false) :
    OwnSubmissionsAtTurn setup leaks
        (execution.respond (application setup leaks) responder response) who ∧
      CanonicalSlotsUsed setup leaks
        (execution.respond (application setup leaks) responder response) who := by
  let app := application setup leaks
  obtain ⟨atTurn, slots⟩ := prior
    ((runtime setup).persistentServiceRisk_clear_before_respond leaks bound execution responder who
      response clear)
  by_cases same : responder = who
  · subst responder
    have retained := member rfl
    have menuClear := (runtime setup).serviceRisk_clear_before_respond leaks bound execution who
      response clear
    rw [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ menuClear] at retained
    exact ⟨retainedOwnSubmissionsAtTurn_respond bounds execution who response retained atTurn,
      retainedCanonicalSlots_respond bounds trace retained atTurn slots⟩
  · have different : who ≠ responder := fun equal => same equal.symm
    refine ⟨?_, canonicalSlotsUsed_respond_other execution different response slots⟩
    unfold OwnSubmissionsAtTurn
    rwa [app.respond_recall_other execution responder who different response]

private theorem riskSlots_round {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy} {who : Player}
    (covered : ∀ past view response, response ∈ (players who past view).support →
      response ∈ bounds.riskActions (runtime setup) leaks bound who past view)
    {execution next : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (prior : ownerPersistentRisk bound execution who = false →
      OwnSubmissionsAtTurn setup leaks execution who ∧
        CanonicalSlotsUsed setup leaks execution who)
    (clear : ownerPersistentRisk bound next who = false)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    OwnSubmissionsAtTurn setup leaks next who ∧ CanonicalSlotsUsed setup leaks next who := by
  let app := application setup leaks
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have conditional : ownerPersistentRisk bound middle who = false →
      OwnSubmissionsAtTurn setup leaks middle who ∧ CanonicalSlotsUsed setup leaks middle who := by
    intro clearMiddle
    exact riskCanonicalSlots_environment bound execution middle who command prior clearMiddle
      moved
  rcases cases with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
  · exact conditional clear
  · obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
      remaining execution middle command trace selected moved
    rw [active] at middleTrace
    exact riskCanonicalSlots_respond bounds bound middle who responder response middleTrace
      conditional (fun same => by subst responder; exact covered _ _ response chosen) clear

/-- Only this owner's menu coverage is needed. All foreign policies are
arbitrary, and may send raw responses after their own risk signals trigger. -/
theorem riskCanonicalSlots_roundsFrom (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (covered : ∀ past view response, response ∈ (players who past view).support →
      response ∈ bounds.riskActions (runtime setup) leaks bound who past view)
    (count : Nat) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (clear : (runtime setup).persistentServiceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false) :
    OwnSubmissionsAtTurn setup leaks execution who ∧
      CanonicalSlotsUsed setup leaks execution who := by
  let app := application setup leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      refine ⟨fun entry member => ?_, fun serial used => ?_⟩
      · cases member
      · cases used
  | succ count ih =>
      rw [app.roundsFrom_succ (initialLaw setup) scheduler players count] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) (count + 1) scheduler
        players count (Nat.le_succ count) prior priorMem
      rw [show count + 1 - count = 0 + 1 by omega] at trace
      exact riskSlots_round bounds bound covered trace (ih prior priorMem) clear moved

/-- Every clear owner at a legal risk-menu history has its own canonical-slot
and submission-turn invariants, even when other owners used expanded raw menus. -/
theorem riskCanonicalSlots_history {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some control)) (who : Player)
    (clear : (runtime setup).persistentServiceRisk leaks bound who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) = false) :
    OwnSubmissionsAtTurn setup leaks control.execution who ∧
      CanonicalSlotsUsed setup leaks control.execution who := by
  let app := application setup leaks
  let menu := bounds.riskMenu (runtime setup) leaks bound
  have covered : ∀ past view response,
      response ∈ (menu.uniformResponses who past view).support →
        response ∈ bounds.riskActions (runtime setup) leaks bound who past view := by
    intro past view response supported
    exact (menu.uniformResponses_support who past view response).mp supported
  have supported := menu.roundSupported_uniform (initialLaw setup) horizon scheduler trace
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      exact riskCanonicalSlots_roundsFrom bounds bound scheduler menu.uniformResponses who covered
        _ execution supported.2 clear
  | some responder =>
      obtain ⟨_, count, prior, command, _, priorMem, _, _, moved⟩ := supported
      obtain ⟨atTurn, valid⟩ := riskCanonicalSlots_roundsFrom bounds bound scheduler
        menu.uniformResponses who covered count prior priorMem
        ((runtime setup).persistentServiceRisk_clear_before_environment leaks bound who clear
          moved)
      have recallEq := app.environmentStep_recall prior execution command moved
      refine ⟨?_, canonicalSlotsUsed_environment moved who valid⟩
      unfold OwnSubmissionsAtTurn
      rw [recallEq]
      exact atTurn

/-- At a clear unrecorded own turn, the counted prepared slot is fresh. -/
theorem riskCanonicalSlot_fresh_at_turn {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some control)) (who : Player)
    (clear : (runtime setup).persistentServiceRisk leaks bound who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) = false)
    (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime setup).eventRecorded leaks
      (control.execution.recall who) event = false) :
    control.execution.application.candidates.lookup
      (who, .prepared (control.execution.application.publicView.bindingCount who)) = .fresh := by
  obtain ⟨atTurn, valid⟩ := riskCanonicalSlots_history bounds bound control trace who clear
  have rawTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace (initialLaw setup)
    horizon scheduler trace
  exact canonicalSlot_fresh_of_used rawTrace who atTurn valid event turn unrecorded

/-- One slot per event gives a bounded canonical slot at every clear unsent
own turn. Other owners' misses or raw submissions need no density assumption. -/
theorem riskCanonicalSlot_resources {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (control : (application setup leaks).Control)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some control)) (who : Player)
    (clear : (runtime setup).persistentServiceRisk leaks bound who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) = false)
    (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime setup).eventRecorded leaks
      (control.execution.recall who) event = false) :
    control.execution.application.publicView.bindingCount who < bounds.candidateCount ∧
      control.execution.application.candidates.lookup
        (who, .prepared (control.execution.application.publicView.bindingCount who)) = .fresh ∧
      canonicalFreshSlot who
        (control.execution.observe (application setup leaks) who).application =
          some (control.execution.application.publicView.bindingCount who) := by
  classical
  have fresh := riskCanonicalSlot_fresh_at_turn bounds bound control trace who clear event turn
    unrecorded
  refine ⟨?_, fresh, canonicalFreshSlot_canonical who _ fresh⟩
  let history := control.execution.application.config.history.map EventGraph.Completion.event
  have ready := (control.execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have absent : event ∉ history := fun present => ready.1
    ((control.execution.application.config.history_exact event).mp present)
  have distinct : (event :: history).Nodup :=
    List.nodup_cons.mpr ⟨absent, control.execution.application.config.history_nodup⟩
  have lengthBound := distinct.length_le_card
  change history.countP _ < bounds.candidateCount
  apply lt_of_le_of_lt List.countP_le_length
  simp only [List.length_cons, Fintype.card_fin] at lengthBound
  omega

end Vegas
