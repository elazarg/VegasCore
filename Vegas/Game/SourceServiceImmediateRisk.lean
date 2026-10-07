/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceImmediatePolicy
import Vegas.Game.SourceServiceBindingMiss
import Vegas.Game.SourceServiceFirstTurnRisk
import Vegas.Game.SourceServiceCanonicalSerial

/-! # Local risk preservation for immediate continuation

An actual scheduler boundary with answered activations and recorded earlier
binding turns has no unprotected unrecorded binding opportunity. Immediate
responses preserve binding-turn records and clear private opportunity recall.
A new public miss would require due expiry after an earlier answered own turn;
that turn's recorded protected sole call rules the miss out.

These local steps use actual prefix and packet invariants. They do not assume
a source policy on earlier histories or establish an equilibrium comparison.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}



/-- A scheduler round cannot create an owner miss from answered activations
and recorded earlier binding turns when its actual resulting calls remain
protected, conforming and unique. No response policy is assumed here. -/
theorem recordedBindings_no_public_miss_round {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution) (who : Player)
    (turned : BindingTurnsRecorded setup leaks execution who)
    (clear : execution.application.publicView.missedBindingBy who = false)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players execution).support)
    (nextTrace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, none, next⟩))
    (calls : OwnFreshCalls setup leaks bound next who)
    (conform : FreshCallsConform setup leaks next who)
    (once : OneCallPerEvent setup leaks next who)
    (atTurn : OwnSubmissionsAtTurn setup leaks next who) :
    next.application.publicView.missedBindingBy who = false := by
  let app := serviceApplication setup mode deadline leaks
  classical
  apply decide_eq_false
  rintro ⟨event, owned, missing⟩
  cases node : nodeView (serviceGraph setup mode) event with
  | sample payload law outputEq codeEq =>
      simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missing
  | resolve actor payload binding checks outputEq codeEq =>
      simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missing
  | bind actor payload outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actor
      have clearEvent : execution.application.publicView.missedBinding event = false := by
        apply Bool.eq_false_of_not_eq_true
        intro missed
        have flag := PublicView.missedBindingBy_of_event execution.application.publicView who
          event owned missed
        rw [clear] at flag
        cases flag
      obtain ⟨command, _, middle, dispatched, effect⟩ := round_cases setup leaks reached
      have middleMissing : middle.application.publicView.missedBinding event = true := by
        rcases effect with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
        · exact missing
        · have same := (serviceRuntime setup mode deadline).reactive_respond_application leaks
              middle actor response
          exact (congrArg
                  (fun view : PublicView (serviceGraph setup mode) => view.missedBinding event)
                  same.2).symm.trans missing
      have facts := legalFacts setup leaks horizon scheduler _ trace
      obtain ⟨_, ready, entered, activated, due⟩ := new_binding_miss_expiry command facts.binding
        dispatched event who payload outputEq codeEq node clearEvent middleMissing
      change (serviceRuntime setup mode deadline).deadline event ≤ execution.application.clock -
          entered at due
      have delayFits := timely event (by rw [owned]; rfl)
      obtain ⟨entry, recalled, turn⟩ := opportunity_turn contract trace answered owned ready
        entered activated (by omega)
      have recordedBefore := turned entry recalled event who payload turn outputEq
      have grows : execution.recall who ⊆ next.recall who := by
        have same := app.environmentStep_recall execution middle command dispatched
        rcases effect with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
        · rw [same]
        · rw [← same]
          exact app.respond_recall_mono middle actor who response
      have recordedAfter : (serviceRuntime setup mode deadline).eventRecorded leaks
          (next.recall who) event = true := by
        obtain ⟨call, member, named⟩ := List.any_eq_true.mp recordedBefore
        exact List.any_eq_true.mpr ⟨call, grows member, named⟩
      have noMiss := owner_recorded_binding_no_miss contract.inclusion nextTrace who calls conform
        once atTurn event payload outputEq codeEq node recordedAfter
      rw [noMiss] at missing
      cases missing

/-- **Exact first-turn play has no public binding omission.** Under the
asynchronous contract, an owner following the first-turn policy never has a
completed binding without an accepted handle, whatever the other players do:
its first ready turn at a binding submits its commitment, whose protected
inclusion completes the event before expiry. -/
theorem sourceServiceFirstTurn_no_miss {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who =
      serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
          profile who)
    (count : Nat) (within : count ≤ horizon)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (reached : execution ∈
        ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler players count).support) :
    execution.application.publicView.missedBindingBy who = false := by
  let app := serviceApplication setup mode deadline leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, stateMem, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ stateMem
      apply PublicView.missedBindingBy_clear
      intro event
      apply Bool.eq_false_of_not_eq_true
      intro missed
      unfold PublicView.missedBinding at missed
      split at missed
      · have completed := (Bool.and_eq_true _ _ ▸ missed).1
        exact (Finset.notMem_empty event (of_decide_eq_true completed)).elim
      all_goals cases missed
  | succ count ih =>
      have reachedNext := reached
      rw [app.roundsFrom_succ (serviceInitialLaw setup mode) scheduler players count] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have clear := ih (by omega) prior priorMem
      have answered := roundsFrom_activationsAnswered count prior priorMem
      have turned := (sourceServiceFirstTurn_recallFacts contract timely players who turns profile
        follows count (by omega) prior priorMem).1
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
          players count (by omega) prior priorMem
      rw [show horizon - count = (horizon - (count + 1)) + 1 by omega] at trace
      obtain ⟨nextTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon
          scheduler players (count + 1) within execution reachedNext
      obtain ⟨calls, once, _⟩ := serialFacts_roundsFrom contract players who
        (firstTurnTiming setup turns mode) profile follows (count + 1) within execution reachedNext
      have conform : FreshCallsConform setup leaks execution who :=
        fun entry member material message fresh emitted =>
          sourceServiceTurnPolicy_freshServiceEnvelope scheduler players who
            (firstTurnTiming setup turns mode) profile follows (count + 1) execution
            reachedNext entry
            member material fresh message emitted
      have atTurn :=
          (canonicalSlots_roundsFrom scheduler players who (firstTurnTiming setup turns mode)
              profile follows (count + 1) execution reachedNext).1
      exact recordedBindings_no_public_miss_round contract timely trace answered who turned clear
        moved nextTrace calls conform once atTurn


section Generic

/-- Recorded earlier binding turns and answered activations protect every
unrecorded binding opportunity at an actual scheduler boundary. -/
theorem recordedBindings_currentOpportunity_clear {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    {remaining : Nat} {execution : (serviceApplication setup mode deadline leaks).Execution}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution) (who : Player)
    (turned : BindingTurnsRecorded setup leaks execution who) :
    (serviceRuntime setup mode deadline).firstUnprotectedBindingOpportunity leaks bound who
        (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) = false := by
  let app := serviceApplication setup mode deadline leaks
  apply Bool.eq_false_of_not_eq_true
  intro risky
  obtain ⟨_, event, owner, payload, turn, binding, unrecorded, unprotected⟩ :=
    ((serviceRuntime setup mode deadline).firstUnprotectedBindingOpportunity_iff leaks bound who _
        _).mp risky
  have turnActual : execution.application.publicView.ownTurn? who = some event := turn
  have first : serviceTurn setup mode deadline leaks who event (execution.recall who)
      (execution.observe app who) = some 0 := by
    change (if execution.application.publicView.ownTurn? who = some event then
      some ((execution.recall who).countP fun entry =>
        decide (entry.beforeView.application.publicView.ownTurn? who = some event))
      else none) = some 0
    simp only [turnActual, ↓reduceIte]
    apply congrArg some
    apply List.countP_eq_zero.mpr
    intro entry member seen
    have recorded := turned entry member event owner payload (of_decide_eq_true seen) binding
    rw [unrecorded] at recorded
    cases recorded
  have ownTurn := PublicView.ownTurn?_spec execution.application.publicView who event turnActual
  have fits := firstTurn_inclusionFits contract timely trace answered ownTurn.2
    ((execution.application.publicView_eventReady event).mp ownTurn.1) first
  exact unprotected fits


/-- An immediate response at clear risk keeps prior binding turns recorded,
records a fresh current binding turn, and adds no private opportunity risk. -/
theorem immediatePolicy_recallFacts_respond {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} {profile : BehavioralProfile setup.program}
    {middle : (serviceApplication setup mode deadline leaks).Execution} {who : Player}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining, some who, middle⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (slots : CanonicalSlotsUsed setup leaks middle who)
    (turned : BindingTurnsRecorded setup leaks middle who)
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who (middle.recall who)
      (middle.observe (serviceApplication setup mode deadline leaks) who) = false)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      (middle.recall who) (middle.observe
          (serviceApplication setup mode deadline leaks) who)).support) :
    BindingTurnsRecorded setup leaks (middle.respond
        (serviceApplication setup mode deadline leaks) who response) who ∧
      (serviceRuntime setup mode deadline).recalledBindingOpportunityRisk leaks bound who
        ((middle.respond
            (serviceApplication setup mode deadline leaks) who response).recall who) = false := by
  let app := serviceApplication setup mode deadline leaks
  have components :=
      ((serviceRuntime setup mode deadline).serviceRisk_clear_iff leaks bound who _ _).mp clear
  have recallClear :=
      ((serviceRuntime setup mode deadline).persistentServiceRisk_clear_iff leaks bound who _ _).mp
    components.1 |>.2
  have nextClear :=
      ((serviceRuntime setup mode deadline).recalledBindingOpportunityRisk_respond_clear leaks bound
    middle who response components.2).trans recallClear
  refine ⟨?_, nextClear⟩
  obtain ⟨_, recalled, _⟩ := respond_recall_self setup leaks middle who response
  intro entry member event owner payload turn binding
  rw [recalled] at member
  rcases List.mem_append.mp member with old | new
  · exact (serviceRuntime setup mode deadline).eventRecorded_respond_of_recorded leaks middle who
      who response event
      (turned entry old event owner payload turn binding)
  · cases List.mem_singleton.mp new
    change middle.application.publicView.ownTurn? who = some event at turn
    by_cases recorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (middle.recall who) event = true
    · exact (serviceRuntime setup mode deadline).eventRecorded_respond_of_recorded leaks middle
        who who response event
        recorded
    · have unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (middle.recall who) event = false :=
        Bool.eq_false_of_not_eq_true recorded
      cases node : nodeView (serviceGraph setup mode) event with
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
          obtain ⟨_, _, _, _, recordedAfter⟩ := sourceServiceImmediatePolicy_binding_call trace
            atTurn slots clear event bindingPayload outputEq codeEq node turn unrecorded response
            chosen
          exact recordedAfter

end Generic
end Vegas
