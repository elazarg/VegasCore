/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnBinding
import Vegas.Game.SourceServiceFirstTurnOpportunity
import Vegas.Game.SourceServiceRiskSlots

/-! # Clear opportunity recall under exact first-turn play

At every own binding turn the event has either already been submitted, or
the turn is the first one and the asynchronous reaction budget protects it.
The first-turn prescribed response submits that binding and records its event.
Thus no own response latches an unprotected first binding opportunity.

The proof constrains only this owner's policy. Foreign policies remain
arbitrary, including raw continuations after their own risk. Bounds on the
number of rounds are explicit because the service contract covers the fixed
raw protocol horizon. This result concerns private opportunity recall; it
does not claim zero audit charge or absence of public binding misses.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Every earlier own binding turn has a submitted call naming that event in
the owner's current actual recall. This does not assert successful inclusion. -/
def BindingTurnsRecorded (execution : (application setup leaks).Execution) (who : Player) : Prop :=
  ∀ entry ∈ execution.recall who, ∀ event owner payload,
    entry.beforeView.application.publicView.ownTurn? who = some event →
      (graph setup).outputLayout event = .binding owner payload →
        (runtime setup).eventRecorded leaks (execution.recall who) event = true

variable {setup leaks}

private theorem bindingTurnsRecorded_environment
    {execution next : (application setup leaks).Execution}
    {command : (application setup leaks).Command} (who : Player)
    (valid : BindingTurnsRecorded setup leaks execution who)
    (moved : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    BindingTurnsRecorded setup leaks next who := by
  unfold BindingTurnsRecorded
  rw [(application setup leaks).environmentStep_recall execution next command moved]
  exact valid

private theorem bindingTurnsRecorded_respond_other
    (execution : (application setup leaks).Execution) (actor who : Player)
    (response : (application setup leaks).Action) (different : who ≠ actor)
    (valid : BindingTurnsRecorded setup leaks execution who) :
    BindingTurnsRecorded setup leaks
      (execution.respond (application setup leaks) actor response) who := by
  unfold BindingTurnsRecorded
  rw [(application setup leaks).respond_recall_other execution actor who different response]
  exact valid

private theorem firstTurn_recallFacts_round {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    {players : Player → (application setup leaks).Policy} {who : Player} {turns : Nat}
    {profile : BehavioralProfile setup.program}
    (follows : players who =
      sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile who)
    {execution next : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (slots : CanonicalSlotsUsed setup leaks execution who)
    (valid : BindingTurnsRecorded setup leaks execution who)
    (clear : (runtime setup).recalledBindingOpportunityRisk leaks bound who
      (execution.recall who) = false)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    BindingTurnsRecorded setup leaks next who ∧
      (runtime setup).recalledBindingOpportunityRisk leaks bound who
        (next.recall who) = false := by
  let app := application setup leaks
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have validMiddle := bindingTurnsRecorded_environment who valid moved
  have clearMiddle : (runtime setup).recalledBindingOpportunityRisk leaks bound who
      (middle.recall who) = false := by rw [recallEq]; exact clear
  rcases cases with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
  · exact ⟨validMiddle, clearMiddle⟩
  · by_cases same : responder = who
    · subst responder
      have commandEq : command = .activate who := by
        cases command with
        | activate actor =>
            exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
        | wait | «include» _ | application _ => cases active
      subst commandEq
      have appEq := activation_application setup leaks execution middle who moved
      obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
        remaining execution middle (.activate who) trace selected moved
      change ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining, some who, middle⟩) at middleTrace
      have atMiddle : OwnSubmissionsAtTurn setup leaks middle who := by
        unfold OwnSubmissionsAtTurn
        rw [recallEq]
        exact atTurn
      have slotsMiddle := canonicalSlotsUsed_environment moved who slots
      have dichotomy (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
          (turn : middle.application.publicView.ownTurn? who = some event)
          (binding : (graph setup).outputLayout event = .binding owner payload) :
          (runtime setup).eventRecorded leaks (middle.recall who) event = true ∨
            (sourceServiceTurn setup leaks who event (middle.recall who)
              (middle.observe app who) = some 0 ∧
                middle.application.publicView.InclusionFitsDeadline (runtime setup) bound
                  event) := by
        by_cases recorded : (runtime setup).eventRecorded leaks (middle.recall who) event = true
        · exact Or.inl recorded
        · have first : sourceServiceTurn setup leaks who event (middle.recall who)
              (middle.observe app who) = some 0 := by
            change (if middle.application.publicView.ownTurn? who = some event then
              some ((middle.recall who).countP fun entry =>
                decide (entry.beforeView.application.publicView.ownTurn? who = some event))
              else none) = some 0
            simp only [turn, ↓reduceIte]
            apply congrArg some
            exact List.countP_eq_zero.mpr fun entry member seen =>
              recorded (validMiddle entry member event owner payload
                (of_decide_eq_true seen) binding)
          have owned := (PublicView.ownTurn?_spec _ who event turn).2
          have ready : execution.application.config.cut.Ready event := by
            rw [← appEq]
            exact (middle.application.publicView_eventReady event).mp
              (PublicView.ownTurn?_spec _ who event turn).1
          have firstBefore : sourceServiceTurn setup leaks who event (execution.recall who)
              (middle.observe app who) = some 0 := by rw [← recallEq]; exact first
          have fits :=
            firstTurn_inclusionFits contract timely trace answered owned ready firstBefore
          refine Or.inr ⟨first, ?_⟩
          rw [appEq]
          exact fits
      have opportunityClear : (runtime setup).firstUnprotectedBindingOpportunity leaks bound who
          (middle.recall who) (middle.observe app who) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro risky
        obtain ⟨_, event, owner, payload, turn, binding, unrecorded, unprotected⟩ :=
          ((runtime setup).firstUnprotectedBindingOpportunity_iff leaks bound who _ _).mp risky
        rcases dichotomy event owner payload turn binding with recorded | ⟨_, fits⟩
        · rw [unrecorded] at recorded
          cases recorded
        · exact unprotected fits
      have nextClear := ((runtime setup).recalledBindingOpportunityRisk_respond_clear leaks bound
        middle who response opportunityClear).trans clearMiddle
      refine ⟨?_, nextClear⟩
      obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
      intro entry member event owner payload turn binding
      rw [recalled] at member
      rcases List.mem_append.mp member with old | new
      · exact (runtime setup).eventRecorded_respond_of_recorded leaks middle who who response event
          (validMiddle entry old event owner payload turn binding)
      · cases List.mem_singleton.mp new
        change middle.application.publicView.ownTurn? who = some event at turn
        rcases dichotomy event owner payload turn binding with recorded | ⟨first, fits⟩
        · exact (runtime setup).eventRecorded_respond_of_recorded leaks middle who who response
            event recorded
        · rw [follows] at chosen
          cases node : nodeView (graph setup) event with
          | sample sampled law outputEq codeEq =>
              rw [outputEq] at binding
              cases binding
          | resolve actor resolutionPayload bindingRef checks outputEq codeEq =>
              rw [outputEq] at binding
              cases binding
          | bind actor bindingPayload outputEq codeEq =>
              have actorEq : actor = who := Option.some.inj
                ((nodeView_bind_actor outputEq codeEq).symm.trans
                  (PublicView.ownTurn?_spec _ who event turn).2)
              subst actorEq
              obtain ⟨material, _, _, _, recorded⟩ := sourceServiceFirstTurn_binding_call
                middleTrace atMiddle slotsMiddle event bindingPayload outputEq codeEq node first
                  fits response chosen
              exact recorded
    · have different : who ≠ responder := Ne.symm same
      refine ⟨bindingTurnsRecorded_respond_other middle responder who response different
        validMiddle, ?_⟩
      rw [app.respond_recall_other middle responder who different response]
      exact clearMiddle

/-- Exact first-turn timing never records an unprotected first binding
opportunity. Every earlier own binding turn has already recorded its event.
No restriction is imposed on any foreign policy. -/
theorem sourceServiceFirstTurn_recallFacts {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who =
      sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile who)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    BindingTurnsRecorded setup leaks execution who ∧
      (runtime setup).recalledBindingOpportunityRisk leaks bound who (execution.recall who) =
        false := by
  let app := application setup leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      refine ⟨?_, (runtime setup).recalledBindingOpportunityRisk_nil leaks bound who⟩
      intro entry member
      cases member
  | succ count ih =>
      rw [app.roundsFrom_succ (initialLaw setup) scheduler players count] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨valid, clear⟩ := ih (by omega) prior priorMem
      have answered := roundsFrom_activationsAnswered count prior priorMem
      obtain ⟨atTurn, slots⟩ := canonicalSlots_roundsFrom scheduler players who
        (firstTurnTiming setup turns) profile follows count prior priorMem
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players count
        (by omega) prior priorMem
      rw [show horizon - count = (horizon - (count + 1)) + 1 by omega] at trace
      exact firstTurn_recallFacts_round contract timely follows trace answered atTurn slots valid
        clear moved

/-- The current actual private recall is also clear at a pending activation,
not only after a completed scheduler round. -/
theorem sourceServiceFirstTurn_recallFacts_roundSupported {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who =
      sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile who)
    (control : (application setup leaks).Control)
    (reached : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some control)) :
    BindingTurnsRecorded setup leaks control.execution who ∧
      (runtime setup).recalledBindingOpportunityRisk leaks bound who
        (control.execution.recall who) = false := by
  obtain ⟨remaining, actor, execution⟩ := control
  cases actor with
  | none =>
      have within : execution.environmentRecall.length ≤ horizon := by
        have lengths := reached.1
        change execution.environmentRecall.length + remaining = horizon at lengths
        omega
      exact sourceServiceFirstTurn_recallFacts contract timely players who turns profile follows
        _ within execution reached.2
  | some responder =>
      obtain ⟨lengthEq, count, prior, command, counted, priorMem, _, _, moved⟩ := reached
      obtain ⟨valid, clear⟩ := sourceServiceFirstTurn_recallFacts contract timely players who turns
        profile follows count (by omega) prior priorMem
      refine ⟨bindingTurnsRecorded_environment who valid moved, ?_⟩
      rw [(application setup leaks).environmentStep_recall prior execution command moved]
      exact clear

end Vegas
