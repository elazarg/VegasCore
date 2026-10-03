/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceImmediatePolicy
import Vegas.Game.SourceServiceDecisionMiss
import Vegas.Game.SourceServiceFirstTurnRisk

/-! # Local risk preservation for immediate continuation

An actual scheduler boundary with answered activations and recorded earlier
own turns has no unprotected unrecorded owned opportunity. Immediate
responses preserve own-turn records and clear private opportunity recall.
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
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Recorded earlier own turns and answered activations protect every
unrecorded owned opportunity at an actual scheduler boundary. -/
theorem recordedTurns_currentOpportunity_clear {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution) (who : Player)
    (turned : OwnTurnsRecorded setup leaks execution who) :
    (runtime setup).firstUnprotectedOpportunity leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false := by
  let app := application setup leaks
  apply Bool.eq_false_of_not_eq_true
  intro risky
  obtain ⟨_, event, turn, unrecorded, unprotected⟩ :=
    ((runtime setup).firstUnprotectedOpportunity_iff leaks bound who _ _).mp risky
  have turnActual : execution.application.publicView.ownTurn? who = some event := turn
  have first : sourceServiceTurn setup leaks who event (execution.recall who)
      (execution.observe app who) = some 0 := by
    change (if execution.application.publicView.ownTurn? who = some event then
      some ((execution.recall who).countP fun entry =>
        decide (entry.beforeView.application.publicView.ownTurn? who = some event))
      else none) = some 0
    simp only [turnActual, ↓reduceIte]
    apply congrArg some
    apply List.countP_eq_zero.mpr
    intro entry member seen
    have recorded := turned entry member event (of_decide_eq_true seen)
    rw [unrecorded] at recorded
    cases recorded
  have ownTurn := PublicView.ownTurn?_spec execution.application.publicView who event turnActual
  have fits := firstTurn_inclusionFits contract timely trace answered ownTurn.2
    ((execution.application.publicView_eventReady event).mp ownTurn.1) first
  exact unprotected fits

/-- An immediate response at clear risk keeps prior own turns recorded,
records a fresh current own turn, and adds no private opportunity risk. -/
theorem immediatePolicy_recallFacts_respond {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat} {profile : BehavioralProfile setup.program}
    {middle : (application setup leaks).Execution} {who : Player}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, middle⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (slots : CanonicalSlotsUsed setup leaks middle who)
    (turned : OwnTurnsRecorded setup leaks middle who)
    (clear : (runtime setup).serviceRisk leaks bound who (middle.recall who)
      (middle.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (chosen : response ∈ (sourceServiceImmediatePolicy setup leaks bound profile who
      (middle.recall who) (middle.observe (application setup leaks) who)).support) :
    OwnTurnsRecorded setup leaks (middle.respond (application setup leaks) who response) who ∧
      (runtime setup).recalledOpportunityRisk leaks bound who
        ((middle.respond (application setup leaks) who response).recall who) = false := by
  let app := application setup leaks
  have components := ((runtime setup).serviceRisk_clear_iff leaks bound who _ _).mp clear
  have recallClear := ((runtime setup).persistentServiceRisk_clear_iff leaks bound who _ _).mp
    components.1 |>.2
  have nextClear := ((runtime setup).recalledOpportunityRisk_respond_clear leaks bound
    middle who response components.2).trans recallClear
  refine ⟨?_, nextClear⟩
  obtain ⟨_, recalled, _⟩ := respond_recall_self setup leaks middle who response
  intro entry member event turn
  rw [recalled] at member
  rcases List.mem_append.mp member with old | new
  · exact (runtime setup).eventRecorded_respond_of_recorded leaks middle who who response event
      (turned entry old event turn)
  · cases List.mem_singleton.mp new
    change middle.application.publicView.ownTurn? who = some event at turn
    by_cases recorded : (runtime setup).eventRecorded leaks (middle.recall who) event = true
    · exact (runtime setup).eventRecorded_respond_of_recorded leaks middle who who response event
        recorded
    · have unrecorded : (runtime setup).eventRecorded leaks (middle.recall who) event = false :=
        Bool.eq_false_of_not_eq_true recorded
      obtain ⟨_, _, _, recordedAfter⟩ := sourceServiceImmediatePolicy_call trace atTurn slots
        clear event turn unrecorded response chosen
      exact recordedAfter

/-- A scheduler round cannot create an owner miss from answered activations
and recorded earlier own turns when its actual resulting calls remain
protected, conforming and unique. No response policy is assumed here. -/
theorem recordedTurns_no_public_miss_round {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    {players : Player → (application setup leaks).Policy}
    {execution next : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution) (who : Player)
    (turned : OwnTurnsRecorded setup leaks execution who)
    (clear : execution.application.publicView.missedDecisionBy who = false)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support)
    (nextTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, next⟩))
    (calls : OwnFreshCalls setup leaks bound next who)
    (conform : FreshCallsConform setup leaks next who)
    (once : OneCallPerEvent setup leaks next who)
    (atTurn : OwnSubmissionsAtTurn setup leaks next who) :
    next.application.publicView.missedDecisionBy who = false := by
  let app := application setup leaks
  apply (next.application.publicView.missedDecisionBy_eq_false_iff who).mpr
  intro event owned missing
  have clearEvent : event ∉ execution.application.missedEvents :=
    (execution.application.publicView.missedDecisionBy_eq_false_iff who).mp clear event owned
  obtain ⟨command, _, middle, dispatched, effect⟩ := round_cases setup leaks reached
  have middleMissing : event ∈ middle.application.missedEvents := by
    rcases effect with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
    · exact missing
    · have same := congrArg PublicView.missedEvents
        ((runtime setup).reactive_respond_application leaks middle actor response).2
      change _ = middle.application.missedEvents at same
      exact same ▸ missing
  obtain ⟨_, ready, ⟨entered, activated, due⟩, _⟩ := reactive_new_missedEvent
    (runtime setup) leaks command dispatched event clearEvent middleMissing
  have delayFits := timely event (by rw [owned]; rfl)
  obtain ⟨entry, recalled, turn⟩ := opportunity_turn contract trace answered owned ready
    entered activated (by omega)
  have recordedBefore := turned entry recalled event turn
  have grows : execution.recall who ⊆ next.recall who := by
    have same := app.environmentStep_recall execution middle command dispatched
    rcases effect with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
    · rw [same]
    · rw [← same]
      exact app.respond_recall_mono middle actor who response
  have recordedAfter : (runtime setup).eventRecorded leaks (next.recall who) event = true := by
    obtain ⟨call, member, named⟩ := List.any_eq_true.mp recordedBefore
    exact List.any_eq_true.mpr ⟨call, grows member, named⟩
  exact owner_recorded_decision_no_miss contract.inclusion nextTrace who calls conform once atTurn
    event owned recordedAfter missing

end Vegas
