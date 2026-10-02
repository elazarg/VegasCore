/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRetainedSlots
import Vegas.Pending.ReactiveRiskMenu

/-! # Owner-local canonical slots at clear risk-menu histories

A clear current risk signal implies that the same owner's earlier signals
were clear: private recall only grows, and public binding misses persist.
Only this owner's response is consequently restricted to canonical actions.
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

private def ownerRisk (bound : (graph setup).EventId → Nat)
    (execution : (application setup leaks).Execution) (who : Player) : Bool :=
  (runtime setup).serviceRisk leaks bound who (execution.recall who)
    (execution.observe (application setup leaks) who)

private theorem publicMiss_environment {execution next : (application setup leaks).Execution}
    {command : (application setup leaks).Command} (who : Player)
    (missed : execution.application.publicView.missedBindingBy who = true)
    (moved : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    next.application.publicView.missedBindingBy who = true := by
  obtain ⟨event, owned, omission⟩ := of_decide_eq_true missed
  apply PublicView.missedBindingBy_of_event _ who event owned
  cases kind : (graph setup).outputLayout event with
  | binding actor payload =>
      have invariant :=
        (runtime setup).reactiveMissedBindingInvariant leaks event actor payload kind
      exact invariant.environmentStep execution next command omission moved
  | publicData payload | privateInput actor payload | publication payload =>
      simp only [PublicView.missedBinding, kind, Bool.false_eq_true] at omission

private theorem ownerRisk_environment_mono
    (bound : (graph setup).EventId → Nat) (who : Player)
    {execution next : (application setup leaks).Execution}
    {command : (application setup leaks).Command}
    (risky : ownerRisk bound execution who = true)
    (moved : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    ownerRisk bound next who = true := by
  rcases ((runtime setup).serviceRisk_iff leaks bound who _ _).mp risky with publicMiss | recalled
  · exact (runtime setup).serviceRisk_of_public_miss leaks bound who _ _
      (publicMiss_environment who publicMiss moved)
  · apply (runtime setup).serviceRisk_of_recalled leaks bound who _ _
    have recallEq := (application setup leaks).environmentStep_recall execution next command moved
    rw [recallEq]
    exact recalled

private theorem ownerRisk_respond_mono
    (bound : (graph setup).EventId → Nat) (execution : (application setup leaks).Execution)
    (actor who : Player) (response : (application setup leaks).Action)
    (risky : ownerRisk bound execution who = true) :
    ownerRisk bound (execution.respond (application setup leaks) actor response) who = true := by
  rcases ((runtime setup).serviceRisk_iff leaks bound who _ _).mp risky with publicMiss | recalled
  · apply (runtime setup).serviceRisk_of_public_miss leaks bound who _ _
    have publicEq := (runtime setup).reactive_respond_application leaks execution actor response
    exact (congrArg (fun view : PublicView (graph setup) => view.missedBindingBy who)
      publicEq.2).trans publicMiss
  · apply (runtime setup).serviceRisk_of_recalled leaks bound who _ _
    obtain ⟨entry, present, identity, event, named, owned, unprotected⟩ :=
      ((runtime setup).recalledSubmissionRisk_iff leaks bound who _).mp recalled
    apply ((runtime setup).recalledSubmissionRisk_iff leaks bound who _).mpr
    exact ⟨entry,
      (application setup leaks).respond_recall_mono execution actor who response present,
      identity, event, named, owned, unprotected⟩

private theorem ownerRisk_clear_before_environment
    (bound : (graph setup).EventId → Nat) (who : Player)
    {execution next : (application setup leaks).Execution}
    {command : (application setup leaks).Command}
    (clear : ownerRisk bound next who = false)
    (moved : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    ownerRisk bound execution who = false := by
  apply Bool.eq_false_of_not_eq_true
  intro risky
  have persists := ownerRisk_environment_mono bound who risky moved
  rw [clear] at persists
  cases persists

private theorem ownerRisk_clear_before_respond
    (bound : (graph setup).EventId → Nat) (execution : (application setup leaks).Execution)
    (actor who : Player) (response : (application setup leaks).Action)
    (clear : ownerRisk bound (execution.respond (application setup leaks) actor response) who =
      false) : ownerRisk bound execution who = false := by
  apply Bool.eq_false_of_not_eq_true
  intro risky
  have persists := ownerRisk_respond_mono bound execution actor who response risky
  rw [clear] at persists
  cases persists

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

/-- Following the prescribed policy cannot introduce privately recalled risk.
Foreign responses and every environment command, including chance, preserve
the owner's recall predicate without constraining their behavior. -/
theorem sourceServiceTurnPolicy_recalledRiskInvariant
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

/-- The actual own recall stays clear along any number of prescribed rounds.
This does not assert that a deferred binding cannot publicly miss its deadline. -/
theorem sourceServiceTurnPolicy_recalledRisk_roundsFrom
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
  have invariant := sourceServiceTurnPolicy_recalledRiskInvariant players who timing profile follows
  exact invariant.runRounds scheduler count _ execution
    ((runtime setup).recalledSubmissionRisk_nil leaks bound who) supported

/-- Also covers the intermediate execution before an activated player responds,
so the flag here reads the current private recall rather than a prior boundary. -/
theorem sourceServiceTurnPolicy_recalledRisk_roundSupported
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {bound : (graph setup).EventId → Nat} {turns : Nat} (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (horizon : Nat) (control : (application setup leaks).Control)
    (reached : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler players
      (some control)) :
    (runtime setup).recalledSubmissionRisk leaks bound who
      (control.execution.recall who) = false := by
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      exact sourceServiceTurnPolicy_recalledRisk_roundsFrom scheduler players who timing profile
        follows _ execution reached.2
  | some responder =>
      obtain ⟨_, count, prior, command, _, priorMem, _, _, moved⟩ := reached
      rw [(application setup leaks).environmentStep_recall prior execution command moved]
      exact sourceServiceTurnPolicy_recalledRisk_roundsFrom scheduler players who timing profile
        follows count prior priorMem

variable [Fintype Player]
  (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)

private theorem riskSlots_round {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy} {who : Player}
    (covered : ∀ past view response, response ∈ (players who past view).support →
      response ∈ bounds.riskActions (runtime setup) leaks bound who past view)
    {execution next : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (prior : ownerRisk bound execution who = false →
      OwnSubmissionsAtTurn setup leaks execution who ∧ CanonicalSlotsUsed setup leaks execution who)
    (clear : ownerRisk bound next who = false)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    OwnSubmissionsAtTurn setup leaks next who ∧ CanonicalSlotsUsed setup leaks next who := by
  let app := application setup leaks
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have clearMiddle : ownerRisk bound middle who = false := by
    rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, _, rfl⟩
    · exact clear
    · exact ownerRisk_clear_before_respond bound middle responder who response clear
  obtain ⟨atTurn, valid⟩ := prior (ownerRisk_clear_before_environment bound who clearMiddle moved)
  have atMiddle : OwnSubmissionsAtTurn setup leaks middle who := by
    unfold OwnSubmissionsAtTurn
    rw [recallEq]
    exact atTurn
  have validMiddle := canonicalSlotsUsed_environment moved who valid
  rcases cases with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
  · exact ⟨atMiddle, validMiddle⟩
  · obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
      remaining execution middle command trace selected moved
    rw [active] at middleTrace
    by_cases same : responder = who
    · subst responder
      have member := covered _ _ response chosen
      rw [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ clearMiddle] at member
      exact ⟨retainedOwnSubmissionsAtTurn_respond bounds middle who response member atMiddle,
        retainedCanonicalSlots_respond bounds middleTrace member atMiddle validMiddle⟩
    · have different : who ≠ responder := fun equal => same equal.symm
      refine ⟨?_, canonicalSlotsUsed_respond_other middle different response validMiddle⟩
      unfold OwnSubmissionsAtTurn
      rw [app.respond_recall_other middle responder who different response]
      exact atMiddle

/-- Only this owner's menu coverage is needed. All foreign policies are
arbitrary, and may send raw responses after their own risk signals trigger. -/
theorem riskCanonicalSlots_roundsFrom (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (covered : ∀ past view response, response ∈ (players who past view).support →
      response ∈ bounds.riskActions (runtime setup) leaks bound who past view)
    (count : Nat) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
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
    (clear : (runtime setup).serviceRisk leaks bound who (control.execution.recall who)
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
        (ownerRisk_clear_before_environment bound who clear moved)
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
    (clear : (runtime setup).serviceRisk leaks bound who (control.execution.recall who)
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
    (clear : (runtime setup).serviceRisk leaks bound who (control.execution.recall who)
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
