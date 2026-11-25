module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ActivationRecall
public import Vegas.Pending.ExecutionFacts
public import Vegas.Pending.TurnClient
public import Vegas.Pending.ReactiveCanonicalMenu

@[expose] public section

/-! # A graph turn client's submissions name its own ready event -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A policy submits fresh packets only for the event that is its player's
own turn. -/
def SubmitsAtTurn (policy : ((reactiveApplication timeouts) leaks).Policy) (who : Player) :
    Prop := ∀ past view response, response ∈ (policy past view).support → ∀ event,
    (submittedEvent? timeouts) leaks response = some event →
    view.application.publicView.ownTurn? who = some event

theorem silentPolicy_submitsAtTurn (who : Player) :
    SubmitsAtTurn timeouts leaks ((reactiveApplication timeouts) leaks).silentPolicy who := by
  intro past view response chosen event submitted
  obtain rfl := ((reactiveApplication timeouts) leaks).silentPolicy_cases past view
      response chosen
  simp [EventGraphRuntime.submittedEvent?] at submitted

/-- A canonical compiled decision submits only for its own event. -/
theorem submittedEvent_canonicalServiceDecision (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId)
    (action : graph.Action event) (other : graph.EventId)
    (submitted : (submittedEvent? timeouts) leaks
      ((canonicalServiceDecision timeouts) leaks who past view event
          action) = some other) :
    other = event := by
  rcases (canonicalServiceDecision_cases timeouts) leaks who past view
      event action with silent | named
  · rw [silent] at submitted
    cases submitted
  · exact (Option.some.inj (named.symm.trans submitted)).symm

theorem referencePolicy_submitsAtTurn (reference :
    graph.BehavioralProfile)
    (who : Player) :
    SubmitsAtTurn timeouts leaks (referencePolicy timeouts leaks reference who)
        who := by
  intro past view response chosen event submitted
  unfold EventGraphRuntime.referencePolicy at chosen
  split at chosen
  · rename_i identity
    split at chosen
    · rw [PMF.mem_support_pure_iff] at chosen
      subst chosen
      simp [EventGraphRuntime.submittedEvent?] at submitted
    · rename_i turn selected
      split at chosen
      · dsimp only at chosen
        split at chosen
        · rw [PMF.mem_support_pure_iff] at chosen
          subst chosen
          cases submitted
        · rw [PMF.support_map] at chosen
          obtain ⟨action, _, rfl⟩ := chosen
          rw [submittedEvent_canonicalServiceDecision timeouts leaks who past view turn action event
            submitted]
          exact selected
      · rw [PMF.mem_support_pure_iff] at chosen
        subst chosen
        simp [EventGraphRuntime.submittedEvent?] at submitted
  · rw [PMF.mem_support_pure_iff] at chosen
    subst chosen
    simp [EventGraphRuntime.submittedEvent?] at submitted

theorem referenceOpportunity_submitsAtTurn
    (bound : graph.EventId → Nat) (reference :
      graph.BehavioralProfile)
    (who : Player) (event : graph.EventId) : SubmitsAtTurn timeouts leaks
      (referenceOpportunity timeouts leaks bound reference who event) who := by
  intro past view response chosen other submitted
  unfold EventGraphRuntime.referenceOpportunity at chosen
  split at chosen
  · exact silentPolicy_submitsAtTurn timeouts leaks who past view response chosen other submitted
  · split at chosen
    · rw [PMF.support_bind] at chosen
      obtain ⟨decided, decidedChosen, member⟩ := Set.mem_iUnion₂.mp chosen
      split at member
      · exact silentPolicy_submitsAtTurn timeouts leaks who past view response member other
          submitted
      · rw [PMF.mem_support_pure_iff] at member
        subst member
        exact referencePolicy_submitsAtTurn timeouts leaks reference who past
          view
          response decidedChosen other submitted
    · exact silentPolicy_submitsAtTurn timeouts leaks who past view response chosen other
        submitted

theorem turnScheduledPolicy_submitsAtTurn
    (turn : List ((reactiveApplication timeouts) leaks).PlayerEntry →
      ((reactiveApplication timeouts) leaks).PlayerView → Option Nat)
    {slots : Nat} (selected : Option (Fin slots))
    (opening waiting : ((reactiveApplication timeouts) leaks).Policy) (who : Player)
    (openingAt : SubmitsAtTurn timeouts leaks opening who)
    (waitingAt : SubmitsAtTurn timeouts leaks waiting who) :
    SubmitsAtTurn timeouts leaks
      (((reactiveApplication timeouts) leaks).turnScheduledPolicy turn selected opening
          waiting) who := by
  intro past view response chosen event submitted
  unfold ReactiveApplication.turnScheduledPolicy at chosen
  split at chosen
  · exact waitingAt past view response chosen event submitted
  · split at chosen
    · exact openingAt past view response chosen event submitted
    · exact waitingAt past view response chosen event submitted

theorem policyMixture_submitsAtTurn {Index : Type} (initial : PMF Index)
    (policies : Index → ((reactiveApplication timeouts) leaks).Policy) (who : Player)
    (each : ∀ index, SubmitsAtTurn timeouts leaks (policies index) who) :
    SubmitsAtTurn timeouts leaks
      (((reactiveApplication timeouts) leaks).policyMixture initial policies).policy
      who := by
  intro past view response chosen event submitted
  rw [ReactiveApplication.policyMixture_policy, PMF.support_bind] at chosen
  obtain ⟨index, _, member⟩ := Set.mem_iUnion₂.mp chosen
  exact each index past view response member event submitted

theorem turnPolicy_submitsAtTurn (bound :
    graph.EventId → Nat)
    (turns : Nat) (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile) (who : Player) :
    SubmitsAtTurn timeouts leaks
        (turnPolicy timeouts leaks bound turns timing reference who)
      who := by
  intro past view response chosen event submitted
  unfold EventGraphRuntime.turnPolicy at chosen
  split at chosen
  · exact silentPolicy_submitsAtTurn timeouts leaks who past view response chosen event submitted
  · split at chosen
    · rename_i turnEvent _ owned
      exact policyMixture_submitsAtTurn timeouts leaks _ _ who (fun slot =>
        turnScheduledPolicy_submitsAtTurn timeouts leaks _ _ _ _ who
          (referenceOpportunity_submitsAtTurn timeouts leaks bound reference who
            turnEvent)
          (silentPolicy_submitsAtTurn timeouts leaks who)) past view response chosen event submitted
    · exact silentPolicy_submitsAtTurn timeouts leaks who past view response chosen event
        submitted

/-- A round in which `who` submits only at its own turns keeps every recorded
submission of `who` at its turn, whatever the other players do. -/
theorem round_ownSubmissionsAtTurn
    {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
    {players : Player → ((reactiveApplication timeouts) leaks).Policy} {who : Player}
    (atTurn : SubmitsAtTurn timeouts leaks (players who) who)
    {execution next : ((reactiveApplication timeouts) leaks).Execution}
    (valid : OwnSubmissionsAtTurn timeouts leaks execution who)
    (reached : next ∈
        (((reactiveApplication timeouts) leaks).round scheduler players
        execution).support) :
    OwnSubmissionsAtTurn timeouts leaks next who := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases timeouts leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, chosen, rfl⟩
  · intro entry member
    rw [recallEq] at member
    exact valid entry member
  · intro entry member event submitted
    by_cases same : responder = who
    · subst responder
      obtain ⟨emitted, recalled, _⟩ := respond_recall_self timeouts leaks middle who response
      rw [recalled] at member
      rcases List.mem_append.mp member with prior | fresh
      · rw [recallEq] at prior
        exact valid entry prior event submitted
      · rw [List.mem_singleton] at fresh
        subst fresh
        exact atTurn _ _ response chosen event submitted
    · rw [app.respond_recall_other middle responder who (fun equal => same equal.symm)
        response, recallEq] at member
      exact valid entry member event submitted

/-- Every initialized round preserves one player's submission discipline,
independently of the other players and the initial native law. -/
theorem SubmitsAtTurn.roundsFrom
    {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
    {players : Player → ((reactiveApplication timeouts) leaks).Policy} {who : Player}
    (atTurn : SubmitsAtTurn timeouts leaks (players who) who)
    (initial : PMF ((reactiveApplication timeouts) leaks).State) :
    ∀ (count : Nat) (execution : ((reactiveApplication timeouts) leaks).Execution),
      execution ∈ (((reactiveApplication timeouts) leaks).roundsFrom initial
        scheduler players count).support → OwnSubmissionsAtTurn timeouts leaks execution who := by
  let app := (reactiveApplication timeouts) leaks
  intro count
  induction count with
  | zero =>
      intro execution supported
      obtain ⟨state, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      cases (PMF.mem_support_pure_iff _ _).mp reached
      intro entry member
      cases member
  | succ count ih =>
      intro execution supported
      rw [app.roundsFrom_succ initial scheduler players count] at supported
      obtain ⟨prior, priorMember, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      exact round_ownSubmissionsAtTurn timeouts leaks atTurn (ih prior priorMember) moved

end Vegas.EventGraphRuntime
