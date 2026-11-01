/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceFirstTurnMixture
import Vegas.Game.SourceServiceFacts
import Vegas.Game.SourceServiceCompletion
import Vegas.Pending.ReactiveAcceptedOutput
import Vegas.Pending.ReactiveCanonicalMenu

/-! # Fresh submissions only at the author's own turn

The prescribed responses submit fresh packets only for the event that is the
responding player's own turn: the source decision is compiled at that event,
and every other response is silent. This is a property of play on the support
of the turn-counted policy, trembles included, and of the policies deciding
one fixed action at the first turn (`Vegas.SubmissionsAtTurn`).

Every scheduler activation is answered within its round, so a player's recall
contains a response for every activation the environment recorded, at the same
public view (`Vegas.ActivationsAnswered`). Both facts hold along rounds of any
such players under every scheduler.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- A policy submits fresh packets only for the event that is its player's
own turn. -/
def SubmitsAtTurn (policy : (serviceApplication setup mode deadline leaks).Policy) (who : Player) :
    Prop := ∀ past view response, response ∈ (policy past view).support → ∀ event,
    (serviceRuntime setup mode deadline).submittedEvent? leaks response = some event →
    view.application.publicView.ownTurn? who = some event

/-- Every recorded fresh submission was for its author's own turn. -/
def SubmissionsAtTurn (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop := ∀ who, ∀ entry ∈ execution.recall who, ∀ event,
    (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event →
    entry.beforeView.application.publicView.ownTurn? who = some event

theorem silentPolicy_submitsAtTurn (who : Player) :
    SubmitsAtTurn setup leaks (serviceApplication setup mode deadline leaks).silentPolicy who := by
  intro past view response chosen event submitted
  obtain rfl := (serviceApplication setup mode deadline leaks).silentPolicy_cases past view
      response chosen
  simp [EventGraphRuntime.submittedEvent?] at submitted

/-- A canonical compiled decision submits only for its own event. -/
theorem submittedEvent_canonicalServiceDecision (who : Player)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (event : (serviceGraph setup mode).EventId)
    (action : (serviceGraph setup mode).Action event) (other : (serviceGraph setup mode).EventId)
    (submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks
      ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who past view event
          action) = some other) :
    other = event := by
  rcases (serviceRuntime setup mode deadline).canonicalServiceDecision_cases leaks who past view
      event action with silent | named
  · rw [silent] at submitted
    cases submitted
  · exact (Option.some.inj (named.symm.trans submitted)).symm

theorem sourceServiceCanonicalPolicy_submitsAtTurn (profile : BehavioralProfile setup.program)
    (who : Player) :
    SubmitsAtTurn setup leaks (serviceCanonicalPolicy setup mode deadline leaks profile who)
        who := by
  intro past view response chosen event submitted
  unfold serviceCanonicalPolicy at chosen
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
          rw [submittedEvent_canonicalServiceDecision setup leaks who past view turn action event
            submitted]
          exact selected
      · rw [PMF.mem_support_pure_iff] at chosen
        subst chosen
        simp [EventGraphRuntime.submittedEvent?] at submitted
  · rw [PMF.mem_support_pure_iff] at chosen
    subst chosen
    simp [EventGraphRuntime.submittedEvent?] at submitted

theorem sourceServiceCanonicalOpportunity_submitsAtTurn
    (bound : (serviceGraph setup mode).EventId → Nat) (profile : BehavioralProfile setup.program)
    (who : Player) (event : (serviceGraph setup mode).EventId) : SubmitsAtTurn setup leaks
      (serviceCanonicalOpportunity setup mode deadline leaks bound profile who event) who := by
  intro past view response chosen other submitted
  unfold serviceCanonicalOpportunity at chosen
  split at chosen
  · exact silentPolicy_submitsAtTurn setup leaks who past view response chosen other submitted
  · split at chosen
    · rw [PMF.support_bind] at chosen
      obtain ⟨decided, decidedChosen, member⟩ := Set.mem_iUnion₂.mp chosen
      split at member
      · exact silentPolicy_submitsAtTurn setup leaks who past view response member other
          submitted
      · rw [PMF.mem_support_pure_iff] at member
        subst member
        exact sourceServiceCanonicalPolicy_submitsAtTurn setup leaks profile who past view
          response decidedChosen other submitted
    · exact silentPolicy_submitsAtTurn setup leaks who past view response chosen other
        submitted

theorem turnScheduledPolicy_submitsAtTurn
    (turn : List (serviceApplication setup mode deadline leaks).PlayerEntry →
      (serviceApplication setup mode deadline leaks).PlayerView → Option Nat)
    {slots : Nat} (selected : Option (Fin slots))
    (opening waiting : (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    (openingAt : SubmitsAtTurn setup leaks opening who)
    (waitingAt : SubmitsAtTurn setup leaks waiting who) :
    SubmitsAtTurn setup leaks
      ((serviceApplication setup mode deadline leaks).turnScheduledPolicy turn selected opening
          waiting) who := by
  intro past view response chosen event submitted
  unfold ReactiveApplication.turnScheduledPolicy at chosen
  split at chosen
  · exact waitingAt past view response chosen event submitted
  · split at chosen
    · exact openingAt past view response chosen event submitted
    · exact waitingAt past view response chosen event submitted

theorem policyMixture_submitsAtTurn {Index : Type} (initial : PMF Index)
    (policies : Index → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    (each : ∀ index, SubmitsAtTurn setup leaks (policies index) who) :
    SubmitsAtTurn setup leaks
      ((serviceApplication setup mode deadline leaks).policyMixture initial policies).policy
      who := by
  intro past view response chosen event submitted
  rw [ReactiveApplication.policyMixture_policy, PMF.support_bind] at chosen
  obtain ⟨index, _, member⟩ := Set.mem_iUnion₂.mp chosen
  exact each index past view response member event submitted

theorem sourceServiceTurnPolicy_submitsAtTurn (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program) (who : Player) :
    SubmitsAtTurn setup leaks
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who)
      who := by
  intro past view response chosen event submitted
  unfold serviceTurnPolicy at chosen
  split at chosen
  · exact silentPolicy_submitsAtTurn setup leaks who past view response chosen event submitted
  · split at chosen
    · rename_i turnEvent _ owned
      exact policyMixture_submitsAtTurn setup leaks _ _ who (fun slot =>
        turnScheduledPolicy_submitsAtTurn setup leaks _ _ _ _ who
          (sourceServiceCanonicalOpportunity_submitsAtTurn setup leaks bound profile who
            turnEvent)
          (silentPolicy_submitsAtTurn setup leaks who)) past view response chosen event submitted
    · exact silentPolicy_submitsAtTurn setup leaks who past view response chosen event
        submitted

/-- Deciding a fixed action at the first turn submits only for that event,
and only at an input where it is the owner's turn. -/
theorem decidedTurnPolicy_submitsAtTurn (bound : (serviceGraph setup mode).EventId → Nat)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (action : (serviceGraph setup mode).Action event) :
    SubmitsAtTurn setup leaks
        (decidedTurnPolicy (deadline := deadline) setup leaks bound owner event
      action) owner := by
  intro past view response chosen other submitted
  unfold decidedTurnPolicy ReactiveApplication.turnScheduledPolicy at chosen
  dsimp only at chosen
  split at chosen
  · rename_i first
    have turn : view.application.publicView.ownTurn? owner = some event := by
      unfold serviceTurn at first
      split at first
      · assumption
      · cases first
    unfold decidedOpportunity at chosen
    split at chosen
    · exact silentPolicy_submitsAtTurn setup leaks owner past view response chosen other
        submitted
    · split at chosen
      · split at chosen
        · exact silentPolicy_submitsAtTurn setup leaks owner past view response chosen other
            submitted
        · rw [PMF.mem_support_pure_iff] at chosen
          subst chosen
          rw [submittedEvent_canonicalServiceDecision setup leaks owner past view event action
            other submitted]
          exact turn
      · exact silentPolicy_submitsAtTurn setup leaks owner past view response chosen other
          submitted
  · exact silentPolicy_submitsAtTurn setup leaks owner past view response chosen other submitted

variable {setup leaks} in
/-- Submissions at every author's turn are in particular one author's
submissions at its turns. -/
theorem SubmissionsAtTurn.own {execution : (serviceApplication setup mode deadline leaks).Execution}
    (valid : SubmissionsAtTurn setup leaks execution) (who : Player) :
    OwnSubmissionsAtTurn setup leaks execution who :=
  fun entry member event submitted => valid who entry member event submitted

/-- A round in which `who` submits only at its own turns keeps every recorded
submission of `who` at its turn, whatever the other players do. -/
theorem round_ownSubmissionsAtTurn
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {who : Player}
    (atTurn : SubmitsAtTurn setup leaks (players who) who)
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (valid : OwnSubmissionsAtTurn setup leaks execution who)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    OwnSubmissionsAtTurn setup leaks next who := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, chosen, rfl⟩
  · intro entry member
    rw [recallEq] at member
    exact valid entry member
  · intro entry member event submitted
    by_cases same : responder = who
    · subst responder
      obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
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
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {who : Player}
    (atTurn : SubmitsAtTurn setup leaks (players who) who)
    (initial : PMF (serviceApplication setup mode deadline leaks).State) :
    ∀ (count : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution),
      execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom initial
        scheduler players count).support → OwnSubmissionsAtTurn setup leaks execution who := by
  let app := serviceApplication setup mode deadline leaks
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
      exact round_ownSubmissionsAtTurn setup leaks atTurn (ih prior priorMember) moved

/-- A round never changes a candidate whose meaning is fixed. -/
theorem round_candidate_fixed {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players execution).support)
    (handle : Handle (serviceGraph setup mode))
    (fixed : execution.application.candidates.lookup handle ≠ .fresh) :
    next.application.candidates.lookup handle =
      execution.application.candidates.lookup handle := by
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
  have stepped := ((serviceRuntime setup mode deadline).keepsFixedCandidates_step
    leaks).environmentStep execution middle command moved handle fixed
  rcases cases with ⟨_, rfl⟩ | ⟨who, _, response, _, rfl⟩
  · exact stepped
  · rw [((serviceRuntime setup mode deadline).keepsFixedCandidates_step leaks).respond
      middle who response handle (stepped ▸ fixed), stepped]

end Vegas
