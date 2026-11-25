module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceFirstTurnMixture
public import Vegas.Game.SourceServiceFacts
public import Vegas.Game.SourceServiceCompletion
public import Vegas.Pending.ReactiveAcceptedOutput
public import Vegas.Pending.TurnSubmissionDiscipline

@[expose] public section

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
  (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

/-- A policy submits fresh packets only for the event that is its player's
own turn. -/
abbrev SubmitsAtTurn (policy : (serviceApplication setup deps duration leaks).Policy)
    (who : Player) :
    Prop := EventGraphRuntime.SubmitsAtTurn (serviceTimeouts setup deps duration) leaks policy who

/-- Every recorded fresh submission was for its author's own turn. -/
def SubmissionsAtTurn (execution : (serviceApplication setup deps duration leaks).Execution) :
    Prop := ∀ who, ∀ entry ∈ execution.logs who, ∀ event,
    (submittedEvent? (serviceTimeouts setup deps duration)) leaks entry.action = some event →
    entry.beforeView.application.publicView.ownTurn? who = some event

theorem sourceServiceCanonicalPolicy_submitsAtTurn_reference (reference :
    (serviceGraph setup deps).BehavioralProfile)
    (who : Player) :
    SubmitsAtTurn setup leaks (referencePolicy (serviceTimeouts setup deps duration)
      leaks reference who)
        who :=
  EventGraphRuntime.referencePolicy_submitsAtTurn (serviceTimeouts setup deps duration) leaks
    reference who

theorem sourceServiceCanonicalPolicy_submitsAtTurn (profile : BehavioralProfile setup.program)
    (who : Player) :
    SubmitsAtTurn setup leaks (serviceCanonicalPolicy setup deps duration leaks profile who)
        who := by
  apply sourceServiceCanonicalPolicy_submitsAtTurn_reference (deps := deps) (duration := duration)
    (reference := compileEventProfile setup.program profile)

theorem sourceServiceCanonicalOpportunity_submitsAtTurn_reference
    (bound : (serviceGraph setup deps).EventId → Nat) (reference :
      (serviceGraph setup deps).BehavioralProfile)
    (who : Player) (event : (serviceGraph setup deps).EventId) : SubmitsAtTurn setup leaks
      (referenceOpportunity (serviceTimeouts setup deps duration) leaks
        bound reference who event) who :=
  EventGraphRuntime.referenceOpportunity_submitsAtTurn (serviceTimeouts setup deps duration) leaks
    bound reference who event

theorem sourceServiceCanonicalOpportunity_submitsAtTurn
    (bound : (serviceGraph setup deps).EventId → Nat) (profile : BehavioralProfile setup.program)
    (who : Player) (event : (serviceGraph setup deps).EventId) : SubmitsAtTurn setup leaks
      (serviceCanonicalOpportunity setup deps duration leaks bound profile who event) who := by
  apply sourceServiceCanonicalOpportunity_submitsAtTurn_reference (deps := deps) (duration :=
    duration)
    (reference := compileEventProfile setup.program profile)

theorem sourceServiceTurnPolicy_submitsAtTurn_reference (bound :
    (serviceGraph setup deps).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns deps)
    (reference : (serviceGraph setup deps).BehavioralProfile) (who : Player) :
    SubmitsAtTurn setup leaks
        (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns timing reference who)
      who :=
  EventGraphRuntime.turnPolicy_submitsAtTurn (serviceTimeouts setup deps duration) leaks
    bound turns timing reference who

theorem sourceServiceTurnPolicy_submitsAtTurn (bound : (serviceGraph setup deps).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns deps)
    (profile : BehavioralProfile setup.program) (who : Player) :
    SubmitsAtTurn setup leaks
        (serviceTurnPolicy setup deps duration leaks bound turns timing profile who)
      who := by
  apply sourceServiceTurnPolicy_submitsAtTurn_reference (deps := deps) (duration := duration)
    (reference := compileEventProfile setup.program profile)

/-- Deciding a fixed action at the first turn submits only for that event,
and only at an input where it is the owner's turn. -/
theorem decidedTurnPolicy_submitsAtTurn (bound : (serviceGraph setup deps).EventId → Nat)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (action : (serviceGraph setup deps).Action event) :
    SubmitsAtTurn setup leaks
        (decidedTurnPolicy (duration := duration) setup leaks bound owner event
      action) owner := by
  intro past view response chosen other submitted
  have silentAt := silentPolicy_submitsAtTurn (serviceTimeouts setup deps duration) leaks owner
  unfold decidedTurnPolicy ReactiveApplication.turnScheduledPolicy at chosen
  dsimp only at chosen
  split at chosen
  · rename_i first
    have turn : view.application.publicView.ownTurn? owner = some event := by
      unfold EventGraphRuntime.turnIndex at first
      split at first
      · assumption
      · cases first
    let timeouts := serviceTimeouts setup deps duration
    let decision := canonicalServiceDecision timeouts leaks owner past view event action
    have fromDecision (equal : response = decision) : other = event := by
      subst response
      exact submittedEvent_canonicalServiceDecision timeouts leaks owner past view event action
        other submitted
    by_cases prior : eventRecorded timeouts leaks past event
    · rw [fixedOpportunity, ite_eq_left prior] at chosen
      exact silentAt past view response chosen other submitted
    · rw [fixedOpportunity, ite_eq_right prior] at chosen
      by_cases fits : view.application.publicView.InclusionFitsDeadline timeouts bound event
      · rw [ite_eq_left fits] at chosen
        by_cases silent : decision.transmission = none
        · rw [ite_eq_left silent] at chosen
          exact silentAt past view response chosen other submitted
        · rw [ite_eq_right silent, PMF.mem_support_pure_iff] at chosen
          exact (fromDecision chosen).symm ▸ turn
      · rw [ite_eq_right fits] at chosen
        exact silentAt past view response chosen other submitted
  · exact silentAt past view response chosen other submitted

variable {setup leaks} in
/-- Submissions at every author's turn are in particular one author's
submissions at its turns. -/
theorem SubmissionsAtTurn.own {execution : (serviceApplication setup deps duration leaks).Execution}
    (valid : SubmissionsAtTurn setup leaks execution) (who : Player) :
    OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks execution who :=
  fun entry member event submitted => valid who entry member event submitted

/-- Every initialized round preserves one player's submission discipline,
independently of the other players and the initial native law. -/
theorem SubmitsAtTurn.roundsFrom
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {players : Player → (serviceApplication setup deps duration leaks).Policy} {who : Player}
    (atTurn : SubmitsAtTurn setup leaks (players who) who)
    (initial : PMF (serviceApplication setup deps duration leaks).State) :
    ∀ (count : Nat) (execution : (serviceApplication setup deps duration leaks).Execution),
      execution ∈ ((serviceApplication setup deps duration leaks).roundsFrom initial
        scheduler players count).support → OwnSubmissionsAtTurn
          (serviceTimeouts setup deps duration) leaks execution who :=
  EventGraphRuntime.SubmitsAtTurn.roundsFrom (serviceTimeouts setup deps duration) leaks
    atTurn initial

/-- A round never changes a candidate whose meaning is fixed. -/
theorem round_candidate_fixed {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {players : Player → (serviceApplication setup deps duration leaks).Policy}
    {execution next : (serviceApplication setup deps duration leaks).Execution}
    (reached : next ∈
        ((serviceApplication setup deps duration leaks).round scheduler players execution).support)
    (handle : Handle (serviceGraph setup deps))
    (fixed : execution.application.candidates.lookup handle ≠ .fresh) :
    next.application.candidates.lookup handle =
      execution.application.candidates.lookup handle := by
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
  have stepped := ((keepsFixedCandidates_step (serviceTimeouts setup deps duration))
    leaks).environmentStep execution middle command moved handle fixed
  rcases cases with ⟨_, rfl⟩ | ⟨who, _, response, _, rfl⟩
  · exact stepped
  · rw [((keepsFixedCandidates_step (serviceTimeouts setup deps duration)) leaks).respond
      middle who response handle (stepped ▸ fixed), stepped]

end Vegas
