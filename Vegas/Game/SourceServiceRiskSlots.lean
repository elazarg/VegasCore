/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRetainedSlots
import Vegas.Pending.ReactiveRiskPersistence

/-! # Owner-local canonical slots at clear risk-menu histories

A clear persistent risk signal implies that the owner's earlier responses
were canonical. Own recall latches every unprotected first binding opportunity,
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
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

private def ownerPersistentRisk (bound : (serviceGraph setup mode).EventId → Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution) (who : Player) : Bool :=
  (serviceRuntime setup mode deadline).persistentServiceRisk leaks bound who (execution.recall who)
    (execution.observe (serviceApplication setup mode deadline leaks) who)

/-- Every named submission on the prescribed policy's support passes its
protection gate, regardless of the selected turn index or source profile. -/
theorem sourceServiceTurnPolicy_submissionFits
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
    {timing : TurnTiming setup turns mode} {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView} {response :
        (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈
      (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who past
          view).support)
    (event : (serviceGraph setup mode).EventId)
    (submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks response = some event) :
    view.application.publicView.InclusionFitsDeadline
        (serviceRuntime setup mode deadline) bound event := by
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
before-view cannot be an unprotected first binding opportunity. This premise
concerns a submission; it is not inferred from silence or deferred turns. -/
theorem sourceServiceTurnPolicy_submitting_opportunityClear
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
    {timing : TurnTiming setup turns mode} {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView} {response :
        (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈
      (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who past
          view).support)
    {material : (serviceApplication setup mode deadline leaks).Submission}
    (submits : response.transmission = some material) :
    (serviceRuntime setup mode deadline).firstUnprotectedBindingOpportunity leaks bound who past
        view = false := by
  obtain ⟨event, _, turn, _, fits, _⟩ := sourceServiceTurnPolicy_submission chosen submits
  exact (serviceRuntime setup mode deadline).firstUnprotectedBindingOpportunity_protected leaks
      bound who past view
    event turn fits

/-- A prescribed protected first binding response, and every other actual
prescribed submission, adds no opportunity-risk record to the owner's recall. -/
theorem sourceServiceTurnPolicy_submitting_no_opportunityRecall
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
    {timing : TurnTiming setup turns mode} {profile : BehavioralProfile setup.program}
    (execution : (serviceApplication setup mode deadline leaks).Execution) (who : Player)
    {response : (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈ (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who
      (execution.recall who) (execution.observe
          (serviceApplication setup mode deadline leaks) who)).support)
    {material : (serviceApplication setup mode deadline leaks).Submission}
    (submits : response.transmission = some material) :
    (serviceRuntime setup mode deadline).recalledBindingOpportunityRisk leaks bound who
        ((execution.respond
            (serviceApplication setup mode deadline leaks) who response).recall who) =
      (serviceRuntime setup mode deadline).recalledBindingOpportunityRisk leaks bound who
          (execution.recall who) :=
  (serviceRuntime setup mode deadline).recalledBindingOpportunityRisk_respond_clear leaks bound
      execution who response
    (sourceServiceTurnPolicy_submitting_opportunityClear chosen submits)

/-- Following the prescribed policy cannot introduce recalled submission risk.
This component is separate from opportunity risk: late deferral can latch an
unprotected binding opportunity even when it submits nothing. Foreign responses
and every environment command, including chance, preserve own recall. -/
theorem sourceServiceTurnPolicy_recalledSubmissionRiskInvariant
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
        (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program)
    (follows : players who =
        serviceTurnPolicy setup mode deadline leaks bound turns timing profile who) :
    (serviceApplication setup mode deadline leaks).PolicyInvariant players (fun execution =>
      (serviceRuntime setup mode deadline).recalledSubmissionRisk leaks bound who
          (execution.recall who) = false) where
  respond execution actor response clear chosen := by
    by_cases same : actor = who
    · subst actor
      rw [follows] at chosen
      exact ((serviceRuntime setup mode deadline).recalledSubmissionRisk_respond_protected leaks
          bound execution who
        response (sourceServiceTurnPolicy_submissionFits chosen)).trans clear
    · have different : who ≠ actor := fun equal => same equal.symm
      rw [(serviceApplication setup mode deadline leaks).respond_recall_other execution actor who
          different response]
      exact clear
  environment execution next command clear moved := by
    rw [(serviceApplication setup mode deadline leaks).environmentStep_recall execution next
        command moved]
    exact clear

/-- The actual submission-risk component stays clear along any number of
prescribed rounds. Opportunity risk and public binding misses are separate. -/
theorem sourceServiceTurnPolicy_recalledSubmissionRisk_roundsFrom
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
        (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program)
    (follows : players who =
        serviceTurnPolicy setup mode deadline leaks bound turns timing profile who)
    (count : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (reached : execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
        (serviceInitialLaw setup mode) scheduler
      players count).support) :
    (serviceRuntime setup mode deadline).recalledSubmissionRisk leaks bound who
        (execution.recall who) = false := by
  obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have invariant := sourceServiceTurnPolicy_recalledSubmissionRiskInvariant players who timing
    profile follows
  exact invariant.runRounds scheduler count _ execution
    ((serviceRuntime setup mode deadline).recalledSubmissionRisk_nil leaks bound who) supported

/-- Also covers the intermediate execution before an activated player responds,
so the flag here reads the current private recall rather than a prior boundary. -/
theorem sourceServiceTurnPolicy_recalledSubmissionRisk_roundSupported
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
        (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program)
    (follows : players who =
        serviceTurnPolicy setup mode deadline leaks bound turns timing profile who)
    (horizon : Nat) (control : (serviceApplication setup mode deadline leaks).Control)
    (reached : (serviceApplication setup mode deadline leaks).RoundSupported
        (serviceInitialLaw setup mode) horizon scheduler
      players (some control)) :
    (serviceRuntime setup mode deadline).recalledSubmissionRisk leaks bound who
      (control.execution.recall who) = false := by
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      exact sourceServiceTurnPolicy_recalledSubmissionRisk_roundsFrom scheduler players who timing
        profile follows _ execution reached.2
  | some responder =>
      obtain ⟨_, count, prior, command, _, priorMem, _, _, moved⟩ := reached
      rw [(serviceApplication setup mode deadline leaks).environmentStep_recall prior execution
          command moved]
      exact sourceServiceTurnPolicy_recalledSubmissionRisk_roundsFrom scheduler players who timing
        profile follows count prior priorMem

variable [Fintype Player]
  (bounds : MessageBounds (serviceGraph setup mode)) (bound : (serviceGraph setup mode).EventId →
      Nat)

private theorem riskSlots_round {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {who : Player}
    (covered : ∀ past view response, response ∈ (players who past view).support →
      response ∈ bounds.riskActions (serviceRuntime setup mode deadline) leaks bound who past view)
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (prior : ownerPersistentRisk bound execution who = false →
      OwnSubmissionsAtTurn setup leaks execution who ∧
        CanonicalSlotsUsed setup leaks execution who)
    (clear : ownerPersistentRisk bound next who = false)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
            execution).support) :
    OwnSubmissionsAtTurn setup leaks next who ∧ CanonicalSlotsUsed setup leaks next who := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have clearMiddle : ownerPersistentRisk bound middle who = false := by
    rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, _, rfl⟩
    · exact clear
    · exact (serviceRuntime setup mode deadline).persistentServiceRisk_clear_before_respond leaks
        bound middle responder
        who response clear
  obtain ⟨atTurn, valid⟩ :=
    prior ((serviceRuntime setup mode deadline).persistentServiceRisk_clear_before_environment
        leaks bound who
      clearMiddle moved)
  have atMiddle : OwnSubmissionsAtTurn setup leaks middle who := by
    unfold OwnSubmissionsAtTurn
    rw [recallEq]
    exact atTurn
  have validMiddle := canonicalSlotsUsed_environment moved who valid
  rcases cases with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
  · exact ⟨atMiddle, validMiddle⟩
  · obtain ⟨middleTrace⟩ := app.raw_trace_environment
      (serviceInitialLaw setup mode) horizon scheduler
      remaining execution middle command trace selected moved
    rw [active] at middleTrace
    by_cases same : responder = who
    · subst responder
      have member := covered _ _ response chosen
      have menuClear :=
          (serviceRuntime setup mode deadline).serviceRisk_clear_before_respond leaks bound middle
              who
        response clear
      rw [bounds.riskActions_of_clear
          (serviceRuntime setup mode deadline) leaks bound who _ _ menuClear] at member
      exact ⟨retainedOwnSubmissionsAtTurn_respond bounds middle who response member atMiddle,
        retainedCanonicalSlots_respond bounds middleTrace member atMiddle validMiddle⟩
    · have different : who ≠ responder := fun equal => same equal.symm
      refine ⟨?_, canonicalSlotsUsed_respond_other middle different response validMiddle⟩
      unfold OwnSubmissionsAtTurn
      rw [app.respond_recall_other middle responder who different response]
      exact atMiddle

/-- Only this owner's menu coverage is needed. All foreign policies are
arbitrary, and may send raw responses after their own risk signals trigger. -/
theorem riskCanonicalSlots_roundsFrom (scheduler :
    (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    (covered : ∀ past view response, response ∈ (players who past view).support →
      response ∈ bounds.riskActions (serviceRuntime setup mode deadline) leaks bound who past view)
    (count : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (reached : execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
        (serviceInitialLaw setup mode) scheduler
      players count).support)
    (clear : (serviceRuntime setup mode deadline).persistentServiceRisk leaks bound who
        (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) = false) :
    OwnSubmissionsAtTurn setup leaks execution who ∧
      CanonicalSlotsUsed setup leaks execution who := by
  let app := serviceApplication setup mode deadline leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      refine ⟨fun entry member => ?_, fun serial used => ?_⟩
      · cases member
      · cases used
  | succ count ih =>
      rw [app.roundsFrom_succ (serviceInitialLaw setup mode) scheduler players count] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode)
          (count + 1) scheduler
        players count (Nat.le_succ count) prior priorMem
      rw [show count + 1 - count = 0 + 1 by omega] at trace
      exact riskSlots_round bounds bound covered trace (ih prior priorMem) clear moved

/-- Every clear owner at a legal risk-menu history has its own canonical-slot
and submission-turn invariants, even when other owners used expanded raw menus. -/
theorem riskCanonicalSlots_history {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
        (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some control)) (who : Player)
    (clear : (serviceRuntime setup mode deadline).persistentServiceRisk leaks bound who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) = false) :
    OwnSubmissionsAtTurn setup leaks control.execution who ∧
      CanonicalSlotsUsed setup leaks control.execution who := by
  let app := serviceApplication setup mode deadline leaks
  let menu := bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound
  have covered : ∀ past view response,
      response ∈ (menu.uniformResponses who past view).support →
        response ∈ bounds.riskActions
            (serviceRuntime setup mode deadline) leaks bound who past view := by
    intro past view response supported
    exact (menu.uniformResponses_support who past view response).mp supported
  have supported := menu.roundSupported_uniform
      (serviceInitialLaw setup mode) horizon scheduler trace
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      exact riskCanonicalSlots_roundsFrom bounds bound scheduler menu.uniformResponses who covered
        _ execution supported.2 clear
  | some responder =>
      obtain ⟨_, count, prior, command, _, priorMem, _, _, moved⟩ := supported
      obtain ⟨atTurn, valid⟩ := riskCanonicalSlots_roundsFrom bounds bound scheduler
        menu.uniformResponses who covered count prior priorMem
        ((serviceRuntime setup mode deadline).persistentServiceRisk_clear_before_environment leaks
            bound who clear
          moved)
      have recallEq := app.environmentStep_recall prior execution command moved
      refine ⟨?_, canonicalSlotsUsed_environment moved who valid⟩
      unfold OwnSubmissionsAtTurn
      rw [recallEq]
      exact atTurn

/-- At a clear unrecorded own turn, the counted prepared slot is fresh. -/
theorem riskCanonicalSlot_fresh_at_turn {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
        (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some control)) (who : Player)
    (clear : (serviceRuntime setup mode deadline).persistentServiceRisk leaks bound who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) = false)
    (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (control.execution.recall who) event = false) :
    control.execution.application.candidates.lookup
      (who, .prepared (control.execution.application.publicView.bindingCount who)) = .fresh := by
  obtain ⟨atTurn, valid⟩ := riskCanonicalSlots_history bounds bound control trace who clear
  have rawTrace := (bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).toRawTrace
      (serviceInitialLaw setup mode)
    horizon scheduler trace
  exact canonicalSlot_fresh_of_used rawTrace who atTurn valid event turn unrecorded

/-- One slot per event gives a bounded canonical slot at every clear unsent
own turn. Other owners' misses or raw submissions need no density assumption. -/
theorem riskCanonicalSlot_resources {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
        (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some control)) (who : Player)
    (clear : (serviceRuntime setup mode deadline).persistentServiceRisk leaks bound who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) = false)
    (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (control.execution.recall who) event = false) :
    control.execution.application.publicView.bindingCount who < bounds.candidateCount ∧
      control.execution.application.candidates.lookup
        (who, .prepared (control.execution.application.publicView.bindingCount who)) = .fresh ∧
      canonicalFreshSlot who
        (control.execution.observe (serviceApplication setup mode deadline leaks) who).application =
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
