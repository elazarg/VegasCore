/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecidedCompletion
import Vegas.Pending.ReactiveCandidateBudget

/-! # Canonical slots on the support of the turn-counted policy

The audit expects a commitment of `who` at the prepared slot numbered by
`who`'s completed bindings. Play on the support of the turn-counted policy,
deferral trembles included and under every scheduler, keeps every prepared slot
of `who` at or above that count fresh, except the count itself while a binding
of `who` it has already submitted for is unfinished
(`Vegas.sourceServiceTurnPolicy_canonicalSlotsFresh`). Consequently, at each of
`who`'s turns at an event it has not yet submitted for, the counted slot is
fresh and the canonical decision commits there
(`Vegas.canonicalSlot_fresh_at_turn`).

The invariant is carried by the slots `who` has actually used: a prepared
slot that `who` never named is fresh on every legal history
(`Vegas.EventGraphRuntime.CandidateRecall`).
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

section Submissions

variable {setup leaks}

/-- Silence never makes a fresh submission. -/
theorem silentPolicy_not_submit
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    {response : (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈
        ((serviceApplication setup mode deadline leaks).silentPolicy past view).support)
    (material : (serviceApplication setup mode deadline leaks).Submission) :
    response.transmission ≠ some material := by
  obtain rfl := (serviceApplication setup mode deadline leaks).silentPolicy_cases past view
      response chosen
  simp

/-- A fresh submission of the canonical source policy is the canonical decision
at the player's own turn. -/
theorem sourceServiceCanonicalPolicy_submission {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    {response : (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈
        (serviceCanonicalPolicy setup mode deadline leaks profile who past view).support)
    {material : (serviceApplication setup mode deadline leaks).Submission}
    (submits : response.transmission = some material) :
    ∃ event action, view.application.publicView.ownTurn? who = some event ∧
      response = (serviceRuntime setup mode deadline).canonicalServiceDecision leaks who past view
          event action := by
  unfold serviceCanonicalPolicy at chosen
  split at chosen
  · split at chosen
    · rw [PMF.mem_support_pure_iff] at chosen
      subst chosen
      cases submits
    · rename_i event turn
      split at chosen
      · rw [PMF.support_map] at chosen
        obtain ⟨action, _, rfl⟩ := chosen
        exact ⟨event, action, turn, rfl⟩
      · rw [PMF.mem_support_pure_iff] at chosen
        subst chosen
        cases submits
  · rw [PMF.mem_support_pure_iff] at chosen
    subst chosen
    cases submits

/-- A fresh submission of a canonical opportunity is made before the event is
recorded and while a fresh call fits the deadline. -/
theorem sourceServiceCanonicalOpportunity_submission
    {bound : (serviceGraph setup mode).EventId → Nat} {profile : BehavioralProfile setup.program}
    {who : Player} {event : (serviceGraph setup mode).EventId}
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    {response : (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈
        (serviceCanonicalOpportunity setup mode deadline leaks bound profile who event past
        view).support) {material : (serviceApplication setup mode deadline leaks).Submission}
    (submits : response.transmission = some material) :
    (serviceRuntime setup mode deadline).eventRecorded leaks past event = false ∧
    view.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline) bound
    event ∧ ∃ turnEvent action, view.application.publicView.ownTurn? who = some turnEvent ∧
    response = (serviceRuntime setup mode deadline).canonicalServiceDecision leaks who past view
    turnEvent
          action := by
  unfold serviceCanonicalOpportunity at chosen
  split at chosen
  · exact (silentPolicy_not_submit chosen material submits).elim
  · rename_i unrecorded
    split at chosen
    · rename_i fits
      rw [PMF.support_bind] at chosen
      obtain ⟨decided, decidedChosen, member⟩ := Set.mem_iUnion₂.mp chosen
      split at member
      · exact (silentPolicy_not_submit member material submits).elim
      · rw [PMF.mem_support_pure_iff] at member
        subst member
        exact ⟨by simpa using unrecorded, fits,
          sourceServiceCanonicalPolicy_submission decidedChosen submits⟩
    · exact (silentPolicy_not_submit chosen material submits).elim

/-- **Fresh submissions of the turn-counted policy.** Every fresh submission on
its support, at any turn index, is the canonical decision at the player's own
turn, at an event not yet recorded in its recall, while a fresh call fits the
deadline within the inclusion bound. -/
theorem sourceServiceTurnPolicy_submission {bound : (serviceGraph setup mode).EventId → Nat}
    {turns : Nat} {timing : TurnTiming setup turns mode} {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    {response : (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who past
        view).support) {material : (serviceApplication setup mode deadline leaks).Submission}
    (submits : response.transmission = some material) : ∃ event action,
    view.application.publicView.ownTurn? who = some event ∧
    (serviceRuntime setup mode deadline).eventRecorded leaks past event = false ∧
    view.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
    bound event ∧
      response = (serviceRuntime setup mode deadline).canonicalServiceDecision leaks who past view
          event action := by
  unfold serviceTurnPolicy at chosen
  split at chosen
  · exact (silentPolicy_not_submit chosen material submits).elim
  · rename_i event turn
    split at chosen
    · rw [ReactiveApplication.policyMixture_policy, PMF.support_bind] at chosen
      obtain ⟨slot, _, member⟩ := Set.mem_iUnion₂.mp chosen
      unfold serviceTurnFamily ReactiveApplication.turnScheduledPolicy at member
      dsimp only at member
      split at member
      · obtain ⟨unrecorded, fits, other, action, otherTurn, rfl⟩ :=
          sourceServiceCanonicalOpportunity_submission member submits
        have same : other = event := Option.some.inj (otherTurn.symm.trans turn)
        subst same
        exact ⟨other, action, turn, unrecorded, fits, rfl⟩
      · exact (silentPolicy_not_submit member material submits).elim
    · exact (silentPolicy_not_submit chosen material submits).elim

/-- Every packet the policy sends is the canonical decision at the player's
own turn, at an event not yet recorded in its recall. -/
def SubmitsCanonically (policy : (serviceApplication setup mode deadline leaks).Policy)
    (who : Player) : Prop :=
  ∀ past view response, response ∈ (policy past view).support →
    ∀ material : (serviceApplication setup mode deadline leaks).Submission,
      response.transmission = some material → ∃ event action,
        view.application.publicView.ownTurn? who = some event ∧
        (serviceRuntime setup mode deadline).eventRecorded leaks past event = false ∧
        response = (serviceRuntime setup mode deadline).canonicalServiceDecision leaks who past view
          event action

/-- The turn-counted policy submits canonically. -/
theorem serviceTurnPolicy_submitsCanonically (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (who : Player) :
    SubmitsCanonically (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who)
      who := by
  intro past view response chosen material submits
  obtain ⟨event, action, turn, unrecorded, _, rfl⟩ :=
    sourceServiceTurnPolicy_submission chosen submits
  exact ⟨event, action, turn, unrecorded, rfl⟩

end Submissions

section Decision

variable {setup leaks}

/-- A resolution sends an opening of its event or nothing. -/
theorem reactiveResolutionPacket_shape {owner : Player} (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (action : (serviceGraph setup mode).Action event)
    (view : PlayerView (serviceGraph setup mode)) :
    (∃ candidate raw, reactiveResolutionPacket who event payload binding checks outputEq action
        view = some (.opening event candidate raw)) ∨
      reactiveResolutionPacket who event payload binding checks outputEq action view =
        none := by
  unfold reactiveResolutionPacket
  dsimp only
  repeat' split
  all_goals first
    | exact Or.inr rfl
    | exact Or.inl ⟨_, _, rfl⟩

/-- **The slot of a canonical decision.** When the canonical decision of the
owner of `event` uses a prepared slot, that slot is the one
`canonicalFreshSlot` selects, the event is a binding of the owner, and the
submission names the event. -/
theorem canonicalServiceDecision_candidateSlot (who : Player)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some who)
    (action : (serviceGraph setup mode).Action event)
    (serial : Nat)
    (slot : (serviceRuntime setup mode deadline).responseCandidateSlot leaks
      ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who past view event
          action) = some serial) :
    canonicalFreshSlot who view.application = some serial ∧
      (∃ payload, (serviceGraph setup mode).outputLayout event = .binding who payload) ∧
      (serviceRuntime setup mode deadline).submittedEvent? leaks
        ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who past view event
            action) =
          some event := by
  cases node : nodeView (serviceGraph setup mode) event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | bind actor payload outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      cases selected : canonicalFreshSlot actor view.application with
      | none =>
          simp only [EventGraphRuntime.canonicalServiceDecision,
            EventGraphRuntime.canonicalReactiveDecision, node, selected, Option.map_none] at slot
          cases slot
      | some chosen =>
          rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_binding leaks actor past
                  view event payload outputEq codeEq node chosen selected choice] at slot ⊢
          cases Option.some.inj slot
          exact ⟨rfl, ⟨payload, outputEq⟩, rfl⟩
  | resolve actor payload binding checks outputEq codeEq =>
      exfalso
      rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_eq_of_not_bind leaks who
              past view event action (fun _ _ _ _ bind => by rw [node] at bind; cases bind)] at slot
      unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision at slot
      simp only [node] at slot
      rcases reactiveResolutionPacket_shape who event payload binding checks outputEq action
          view.application with ⟨candidate, raw, packet⟩ | packet
      · rw [packet] at slot
        cases slot
      · rw [packet] at slot
        cases slot

end Decision

section Invariant

/-- `who` has an unfinished binding of its own for which it has already
submitted. -/
def PendingBinding (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) : Prop := ∃ event payload, (serviceGraph setup mode).outputLayout event =
    .binding who payload ∧ event ∉ execution.application.config.cut.completed ∧
    (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall who) event = true

/-- Every prepared slot of `who` at or above its public binding count is fresh,
except the count slot itself while a binding of `who` it has submitted for is
unfinished. -/
def CanonicalSlotsFresh (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) : Prop := ∀ serial, execution.application.publicView.bindingCount who ≤ serial →
    execution.application.candidates.lookup (who, .prepared serial) = .fresh ∨
    (serial = execution.application.publicView.bindingCount who ∧ PendingBinding setup leaks
        execution who)

/-- Every prepared slot `who` has used lies below its public binding count, or
at it while a binding of `who` it has submitted for is unfinished. -/
def CanonicalSlotsUsed (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) : Prop := ∀ serial ∈ (serviceRuntime setup mode deadline).submittedCandidateSlots
    leaks (execution.recall who), serial < execution.application.publicView.bindingCount who ∨
    (serial = execution.application.publicView.bindingCount who ∧ PendingBinding setup leaks
        execution who)

variable {setup leaks}

/-- At `who`'s turn at an event it has not submitted for, no binding of `who`
it has submitted for is unfinished: such a binding would be ready too, and a
player acts at most at one ready event (in every dependency mode). -/
theorem not_pendingBinding_at_turn {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some control))
    (who : Player) (atTurn : OwnSubmissionsAtTurn setup leaks control.execution who)
    (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (control.execution.recall who) event = false) :
    ¬ PendingBinding setup leaks control.execution who := by
  rintro ⟨other, payload, _, unfinished, recorded⟩
  have facts := legalFacts setup leaks horizon scheduler control trace
  have otherRecorded := recorded
  unfold EventGraphRuntime.eventRecorded at recorded
  obtain ⟨entry, member, submitted⟩ := List.any_eq_true.mp recorded
  have entryTurn := atTurn entry member other (of_decide_eq_true submitted)
  have entryReady := (PublicView.ownTurn?_spec _ who other entryTurn).1
  have readyOther : control.execution.application.config.cut.Ready other := by
    obtain ⟨extra, order, _, _, _⟩ := facts.eventStable who entry member other entryReady
      unfinished
    exact ready_of_eventReady_extends order entryReady unfinished
  have readyEvent := (PublicView.ownTurn?_spec _ who event turn).1
  have same : other = event :=
    (serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
      control.execution.application.config.cut
      ((control.execution.application.publicView_eventReady event).mp readyEvent) readyOther
      (PublicView.ownTurn?_spec _ who event turn).2
      (PublicView.ownTurn?_spec _ who other entryTurn).2
  subst same
  rw [unrecorded] at otherRecorded
  cases otherRecorded

/-- At `who`'s turn at an event it has not submitted for, the counted slot is
unused and therefore fresh. -/
theorem canonicalSlot_fresh_of_used {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some control))
    (who : Player) (atTurn : OwnSubmissionsAtTurn setup leaks control.execution who)
    (valid : CanonicalSlotsUsed setup leaks control.execution who)
    (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (control.execution.recall who) event = false) :
    control.execution.application.candidates.lookup
      (who, .prepared (control.execution.application.publicView.bindingCount who)) = .fresh := by
  have noPending := not_pendingBinding_at_turn trace who atTurn event turn unrecorded
  have unused : control.execution.application.publicView.bindingCount who ∉
      (serviceRuntime setup mode deadline).submittedCandidateSlots leaks
      (control.execution.recall who) := by
    intro member
    rcases valid _ member with lower | ⟨_, pending⟩
    · exact Nat.lt_irrefl _ lower
    · exact noPending pending
  have rawTrace := trace
  rw [serviceInitialLaw_eq_inputs] at rawTrace
  have candidates : (serviceRuntime setup mode deadline).CandidateRecall leaks control.execution :=
    (serviceRuntime setup mode deadline).candidateRecall_history leaks _ horizon scheduler rawTrace
  exact candidates who _ unused

/-- A scheduler command keeps the used slots below the count. -/
theorem canonicalSlotsUsed_environment
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    {command : (serviceApplication setup mode deadline leaks).Command}
    (reached : next ∈
        (execution.environmentStep (serviceApplication setup mode deadline leaks) command).support)
    (who : Player) (valid : CanonicalSlotsUsed setup leaks execution who) :
    CanonicalSlotsUsed setup leaks next who := by
  have recallEq := (serviceApplication setup mode deadline leaks).environmentStep_recall execution
      next command reached
  intro serial used
  rw [recallEq] at used
  rcases environmentStep_configStep setup leaks execution next command reached with
    same | ⟨completed, ready, action, member⟩
  · have countEq : next.application.publicView.bindingCount who =
        execution.application.publicView.bindingCount who := by
      simp only [PublicView.bindingCount, State.publicView, same]
    rw [countEq]
    rcases valid serial used with lower | ⟨equal, other, payload, layout, unfinished, recorded⟩
    · exact Or.inl lower
    · refine Or.inr ⟨equal, other, payload, layout, ?_, ?_⟩
      · rw [same]
        exact unfinished
      · rw [recallEq]
        exact recorded
  · have history := execution.application.config.step_history completed ready action
      next.application.config member
    have countEq : next.application.publicView.bindingCount who =
        execution.application.publicView.bindingCount who +
          ([completed].countP fun event => match (serviceGraph setup mode).outputLayout event with
            | .binding owner _ => decide (owner = who)
            | .publicData _ | .privateInput _ _ | .publication _ => false) := by
      unfold PublicView.bindingCount
      change List.countP _ (next.application.config.history.map EventGraph.Completion.event) =
        List.countP _ (execution.application.config.history.map EventGraph.Completion.event) + _
      rw [history, List.map_append, List.countP_append]
      rfl
    rcases valid serial used with lower | ⟨equal, other, payload, layout, unfinished, recorded⟩
    · left
      rw [countEq]
      omega
    · by_cases same : other = completed
      · subst same
        left
        rw [countEq]
        have one :
            ([other].countP fun event => match (serviceGraph setup mode).outputLayout event with
            | .binding owner _ => decide (owner = who)
            | .publicData _ | .privateInput _ _ | .publication _ => false) = 1 := by
          simp only [List.countP_cons, List.countP_nil, layout, decide_true]
          rfl
        omega
      · have countGe : execution.application.publicView.bindingCount who ≤
            next.application.publicView.bindingCount who := by
          rw [countEq]
          omega
        rcases Nat.eq_or_lt_of_le countGe with countSame | countMore
        · refine Or.inr ⟨equal.trans countSame, other, payload, layout, ?_, ?_⟩
          · intro finished
            have listed := (next.application.config.history_exact other).mpr finished
            rw [history, List.map_append, List.mem_append] at listed
            rcases listed with old | new
            · exact unfinished ((execution.application.config.history_exact other).mp old)
            · simp only [List.map_cons, List.map_nil, List.mem_singleton] at new
              exact same new
          · rw [recallEq]
            exact recorded
        · left
          omega

/-- Another player's response leaves `who`'s used slots and their count. -/
theorem canonicalSlotsUsed_respond_other
    (execution : (serviceApplication setup mode deadline leaks).Execution) {who responder : Player}
    (different : who ≠ responder) (response : (serviceApplication setup mode deadline leaks).Action)
    (valid : CanonicalSlotsUsed setup leaks execution who) : CanonicalSlotsUsed setup leaks
      (execution.respond (serviceApplication setup mode deadline leaks) responder response)
      who := by
  have recallEq := (serviceApplication setup mode deadline leaks).respond_recall_other execution
      responder who different response
  have appEq := (serviceRuntime setup mode deadline).reactive_respond_application leaks execution
      responder response
  unfold CanonicalSlotsUsed PendingBinding at valid ⊢
  rw [recallEq, appEq.1, appEq.2]
  exact valid

/-- **One response of the turn-counted policy.** A fresh commitment of `who`
on the policy's support uses exactly the counted slot, and its binding stays
pending until it completes. -/
theorem canonicalSlotsUsed_respond {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {middle : (serviceApplication setup mode deadline leaks).Execution} {who : Player}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, some who, middle⟩))
    {policy : (serviceApplication setup mode deadline leaks).Policy}
    (canonical : SubmitsCanonically policy who)
    {response : (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈ (policy (middle.recall who)
      (middle.observe (serviceApplication setup mode deadline leaks) who)).support)
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (valid : CanonicalSlotsUsed setup leaks middle who) :
    CanonicalSlotsUsed setup leaks
        (middle.respond (serviceApplication setup mode deadline leaks) who response)
      who := by
  let app := serviceApplication setup mode deadline leaks
  have appEq := (serviceRuntime setup mode deadline).reactive_respond_application leaks middle
      who response
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
  have recordedMono : ∀ event,
      (serviceRuntime setup mode deadline).eventRecorded leaks (middle.recall who) event = true →
        (serviceRuntime setup mode deadline).eventRecorded leaks
        ((middle.respond app who response).recall who)
          event = true := by
    intro event recorded
    rw [recalled]
    unfold EventGraphRuntime.eventRecorded at recorded ⊢
    rw [List.any_append, recorded, Bool.true_or]
  intro serial used
  rw [(serviceRuntime setup mode deadline).submittedCandidateSlots_respond leaks middle who
          response] at used
  rw [appEq.2]
  rcases List.mem_append.mp used with old | new
  · rcases valid serial old with lower | ⟨equal, other, payload, layout, unfinished, recorded⟩
    · exact Or.inl lower
    · refine Or.inr ⟨equal, other, payload, layout, ?_, recordedMono other recorded⟩
      rw [appEq.1]
      exact unfinished
  · have slot : (serviceRuntime setup mode deadline).responseCandidateSlot leaks response = some
        serial := Option.mem_toList.mp new
    obtain ⟨material, submits⟩ : ∃ material, response.transmission = some material := by
      unfold EventGraphRuntime.responseCandidateSlot at slot
      split at slot
      · exact ⟨_, ‹_›⟩
      · cases slot
    obtain ⟨event, action, turn, unrecorded, rfl⟩ :=
      canonical _ _ response chosen material submits
    have owned := (PublicView.ownTurn?_spec _ who event turn).2
    have fresh := canonicalSlot_fresh_of_used trace who atTurn valid event turn unrecorded
    have canonical := canonicalFreshSlot_canonical who (middle.observe app who).application fresh
    obtain ⟨selected, ⟨payload, layout⟩, named⟩ := canonicalServiceDecision_candidateSlot who
      (middle.recall who) (middle.observe app who) event owned action serial slot
    rw [canonical] at selected
    cases Option.some.inj selected
    have ready := (middle.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
    refine Or.inr ⟨rfl, event, payload, layout, ?_, ?_⟩
    · rw [appEq.1]
      exact ready.1
    · rw [recalled]
      unfold EventGraphRuntime.eventRecorded
      rw [List.any_append]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      rw [named]
      simp

/-- One round keeps `who`'s submissions at its turns and its used slots below
the count, when `who` submits canonically and only at its turns. -/
theorem canonicalSlots_round {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {who : Player}
    (canonical : SubmitsCanonically (players who) who)
    (submitsAtTurn : SubmitsAtTurn setup leaks (players who) who)
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (valid : CanonicalSlotsUsed setup leaks execution who)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    OwnSubmissionsAtTurn setup leaks next who ∧ CanonicalSlotsUsed setup leaks next who := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have atMiddle : OwnSubmissionsAtTurn setup leaks middle who := by
    unfold OwnSubmissionsAtTurn
    rw [recallEq]
    exact atTurn
  have validMiddle := canonicalSlotsUsed_environment moved who valid
  rcases cases with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
  · exact ⟨atMiddle, validMiddle⟩
  · obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
        scheduler remaining execution middle command trace selected moved
    rw [active] at middleTrace
    by_cases same : responder = who
    · subst responder
      refine ⟨?_, canonicalSlotsUsed_respond middleTrace canonical chosen atMiddle validMiddle⟩
      obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
      intro entry member event submitted
      rw [recalled] at member
      rcases List.mem_append.mp member with old | new
      · exact atMiddle entry old event submitted
      · rw [List.mem_singleton] at new
        subst new
        exact submitsAtTurn _ _ response chosen event submitted
    · have different : who ≠ responder := fun equal => same equal.symm
      refine ⟨?_, canonicalSlotsUsed_respond_other middle different response validMiddle⟩
      unfold OwnSubmissionsAtTurn
      rw [app.respond_recall_other middle responder who different response]
      exact atMiddle

/-- On the support of rounds in which `who` follows the turn-counted policy,
`who`'s submissions are at its turns and its used slots lie below the count. -/
theorem canonicalSlots_roundsFrom
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (follows : players who = serviceTurnPolicy setup mode deadline leaks bound turns timing profile
        who) (count : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (reached : execution ∈
        ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler players count).support) : OwnSubmissionsAtTurn setup leaks execution who ∧
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
      rw [app.roundsFrom_succ] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨atTurn, valid⟩ := ih prior priorMem
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) (count + 1)
          scheduler players count (Nat.le_succ count) prior priorMem
      rw [show count + 1 - count = 0 + 1 by omega] at trace
      exact canonicalSlots_round
        (follows ▸ serviceTurnPolicy_submitsCanonically bound turns timing profile who)
        (follows ▸ sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns timing profile
          who) trace atTurn valid moved

/-- **Canonical slots stay fresh on the support of the turn-counted policy.**
Under every scheduler, in every profile in which `who` follows the
turn-counted policy, deferral trembles included, every prepared slot of `who`
at or above its public binding count is fresh, except the count slot itself
while a binding of `who` it has submitted for is unfinished. -/
theorem sourceServiceTurnPolicy_canonicalSlotsFresh
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
    (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program)
    (follows : players who = serviceTurnPolicy setup mode deadline leaks bound turns timing
        profile who)
    (count : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (reached : execution ∈
        ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler players count).support) :
    CanonicalSlotsFresh setup leaks execution who := by
  obtain ⟨_, valid⟩ := canonicalSlots_roundsFrom scheduler players who timing profile follows
    count execution reached
  obtain ⟨trace⟩ := (serviceApplication setup mode deadline leaks).raw_trace_roundsFrom
      (serviceInitialLaw setup mode) count scheduler players count le_rfl execution reached
  rw [serviceInitialLaw_eq_inputs] at trace
  have candidates : (serviceRuntime setup mode deadline).CandidateRecall leaks execution :=
    (serviceRuntime setup mode deadline).candidateRecall_history leaks _ count scheduler trace
  intro serial above
  by_cases used : serial ∈ (serviceRuntime setup mode deadline).submittedCandidateSlots leaks
      (execution.recall who)
  · rcases valid serial used with lower | pending
    · omega
    · exact Or.inr pending
  · exact Or.inl (candidates who serial used)

/-- At `who`'s turn at an event it has not submitted for, the counted slot is
fresh, so the canonical decision commits there. -/
theorem canonicalSlot_fresh_at_turn
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (follows : players who = serviceTurnPolicy setup mode deadline leaks bound turns timing profile
        who) (count : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (reached : execution ∈
        ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler players count).support) (event : (serviceGraph setup mode).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall who)
        event = false) : execution.application.candidates.lookup
      (who, .prepared (execution.application.publicView.bindingCount who)) = .fresh := by
  obtain ⟨atTurn, _⟩ := canonicalSlots_roundsFrom scheduler players who timing profile follows
    count execution reached
  obtain ⟨trace⟩ := (serviceApplication setup mode deadline leaks).raw_trace_roundsFrom
      (serviceInitialLaw setup mode) count scheduler players count le_rfl execution reached
  rcases sourceServiceTurnPolicy_canonicalSlotsFresh scheduler players who timing profile follows
      count execution reached _ le_rfl with fresh | ⟨_, pending⟩
  · exact fresh
  · exact (not_pendingBinding_at_turn trace who atTurn event turn unrecorded pending).elim

end Invariant

end Vegas
