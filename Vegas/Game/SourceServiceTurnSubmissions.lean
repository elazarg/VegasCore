/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnMixture
import Vegas.Game.SourceServiceAsyncTimeliness

/-! # Fresh submissions only at the author's own turn

The prescribed responses submit fresh packets only for the event that is the
responding player's own turn: the source decision is compiled at that event,
and every other response replays. This is a property of play on the support
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
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- One round: a scheduler command, its environment step, and the response of
the activated player, if any. -/
theorem round_cases {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    {execution next : (application setup leaks).Execution}
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    ∃ command ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment (application setup leaks))).support,
      ∃ middle ∈ (execution.environmentStep (application setup leaks) command).support,
        (command.actor? (application setup leaks) = none ∧ next = middle) ∨
          ∃ who, command.actor? (application setup leaks) = some who ∧
            ∃ response ∈ (players who (middle.recall who)
                (middle.observe (application setup leaks) who)).support,
              next = middle.respond (application setup leaks) who response := by
  let app := application setup leaks
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  refine ⟨command, selected, middle, moved, ?_⟩
  change next ∈ (app.resume players (command.actor? app) middle).support at resumed
  cases actor : command.actor? app with
  | none =>
      rw [actor] at resumed
      simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
      exact Or.inl ⟨rfl, resumed⟩
  | some who =>
      rw [actor] at resumed
      change next ∈ (app.invoke players who middle).support at resumed
      rw [ReactiveApplication.invoke, PMF.support_map] at resumed
      obtain ⟨response, chosen, rfl⟩ := resumed
      exact Or.inr ⟨who, rfl, response, chosen, rfl⟩

/-- A policy submits fresh packets only for the event that is its player's
own turn. -/
def SubmitsAtTurn (policy : (application setup leaks).Policy) (who : Player) : Prop :=
  ∀ past view response, response ∈ (policy past view).support →
    ∀ event, (runtime setup).submittedEvent? leaks response = some event →
      view.application.publicView.ownTurn? who = some event

/-- Every recorded fresh submission was for its author's own turn. -/
def SubmissionsAtTurn (execution : (application setup leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who, ∀ event,
    (runtime setup).submittedEvent? leaks entry.action = some event →
      entry.beforeView.application.publicView.ownTurn? who = some event

/-- Every recorded activation was answered by its player at the public view
the scheduler saw. -/
def ActivationsAnswered (execution : (application setup leaks).Execution) : Prop :=
  ∀ entry ∈ execution.environmentRecall, ∀ who, entry.command = .activate who →
    ∃ answer ∈ execution.recall who,
      answer.beforeView.application.publicView = entry.beforeView.application

theorem replayPolicy_submitsAtTurn (who : Player) :
    SubmitsAtTurn setup leaks (application setup leaks).replayPolicy who := by
  intro past view response chosen event submitted
  rw [ReactiveApplication.replayPolicy, PMF.support_map] at chosen
  obtain ⟨selected, _, rfl⟩ := chosen
  cases selected <;> simp [EventGraphRuntime.submittedEvent?] at submitted

/-- The packet a resolution decision prepares names its event. -/
private theorem reactiveResolutionPacket_event {owner : Player} (who : Player)
    (event : (graph setup).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (action : (graph setup).Action event) (view : ReactivePlayerView (graph setup)) :
    Payload.event? (graph setup)
      (reactiveResolutionPacket who event payload binding checks outputEq action view) =
        some event := by
  unfold reactiveResolutionPacket
  dsimp only
  repeat' split
  all_goals rfl

/-- The canonical native decision submits only for its own event. -/
private theorem submittedEvent_canonicalReactiveDecision (who : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event)
    (view : ReactivePlayerView (graph setup)) (other : (graph setup).EventId)
    (submitted : (runtime setup).submittedEvent? leaks
      ((runtime setup).canonicalReactiveDecision leaks who event action view) = some other) :
    other = event := by
  unfold EventGraphRuntime.submittedEvent? EventGraphRuntime.canonicalReactiveDecision
    at submitted
  revert submitted
  cases nodeView (graph setup) event with
  | sample => simp
  | bind owner payload outputEq codeEq =>
      cases canonicalFreshSlot who view with
      | none => simp
      | some serial =>
          simp only [Option.map_some, Payload.event?, Option.some.injEq]
          exact fun same => same.symm
  | resolve owner payload binding checks outputEq codeEq =>
      intro submitted
      change (reactiveResolutionPacket who event payload binding checks outputEq action
        view).event? (graph setup) = some other at submitted
      rw [reactiveResolutionPacket_event] at submitted
      exact (Option.some.inj submitted).symm

/-- A canonical compiled decision submits only for its own event. -/
theorem submittedEvent_canonicalServiceDecision (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (action : (graph setup).Action event) (other : (graph setup).EventId)
    (submitted : (runtime setup).submittedEvent? leaks
      ((runtime setup).canonicalServiceDecision leaks who past view event action) =
        some other) :
    other = event := by
  apply submittedEvent_canonicalReactiveDecision setup leaks who event action view.application
    other
  unfold EventGraphRuntime.canonicalServiceDecision at submitted
  dsimp only at submitted
  split at submitted
  · simp [EventGraphRuntime.submittedEvent?] at submitted
  · rename_i transmission _
    revert submitted
    rcases (runtime setup).canonicalReactiveDecision leaks who event action view.application
      with
      ⟨_ | (material | id)⟩
    · simp [EventGraphRuntime.submittedEvent?, ReactiveApplication.SubmissionNormalization.action]
    · intro submitted
      simpa [EventGraphRuntime.submittedEvent?,
        ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
        WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_packet]
        using submitted
    · intro submitted
      simp only [ReactiveApplication.SubmissionNormalization.action] at submitted
      split at submitted <;> simp [EventGraphRuntime.submittedEvent?] at submitted

theorem sourceServiceCanonicalPolicy_submitsAtTurn (profile : BehavioralProfile setup.program)
    (who : Player) :
    SubmitsAtTurn setup leaks (sourceServiceCanonicalPolicy setup leaks profile who) who := by
  intro past view response chosen event submitted
  unfold sourceServiceCanonicalPolicy at chosen
  split at chosen
  · rename_i identity
    split at chosen
    · rw [PMF.mem_support_pure_iff] at chosen
      subst chosen
      simp [EventGraphRuntime.submittedEvent?] at submitted
    · rename_i turn selected
      split at chosen
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

theorem sourceServiceCanonicalOpportunity_submitsAtTurn (bound : (graph setup).EventId → Nat)
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId) :
    SubmitsAtTurn setup leaks
      (sourceServiceCanonicalOpportunity setup leaks bound profile who event) who := by
  intro past view response chosen other submitted
  unfold sourceServiceCanonicalOpportunity at chosen
  split at chosen
  · exact replayPolicy_submitsAtTurn setup leaks who past view response chosen other submitted
  · split at chosen
    · rw [PMF.support_bind] at chosen
      obtain ⟨decided, decidedChosen, member⟩ := Set.mem_iUnion₂.mp chosen
      split at member
      · exact replayPolicy_submitsAtTurn setup leaks who past view response member other
          submitted
      · rw [PMF.mem_support_pure_iff] at member
        subst member
        exact sourceServiceCanonicalPolicy_submitsAtTurn setup leaks profile who past view
          response decidedChosen other submitted
    · exact replayPolicy_submitsAtTurn setup leaks who past view response chosen other
        submitted

theorem turnScheduledPolicy_submitsAtTurn
    (turn : List (application setup leaks).PlayerEntry →
      (application setup leaks).PlayerView → Option Nat)
    {slots : Nat} (selected : Option (Fin slots))
    (opening waiting : (application setup leaks).Policy) (who : Player)
    (openingAt : SubmitsAtTurn setup leaks opening who)
    (waitingAt : SubmitsAtTurn setup leaks waiting who) :
    SubmitsAtTurn setup leaks
      ((application setup leaks).turnScheduledPolicy turn selected opening waiting) who := by
  intro past view response chosen event submitted
  unfold ReactiveApplication.turnScheduledPolicy at chosen
  split at chosen
  · exact waitingAt past view response chosen event submitted
  · split at chosen
    · exact openingAt past view response chosen event submitted
    · exact waitingAt past view response chosen event submitted

theorem policyMixture_submitsAtTurn {Index : Type} (initial : PMF Index)
    (policies : Index → (application setup leaks).Policy) (who : Player)
    (each : ∀ index, SubmitsAtTurn setup leaks (policies index) who) :
    SubmitsAtTurn setup leaks
      ((application setup leaks).policyMixture initial policies).policy who := by
  intro past view response chosen event submitted
  rw [ReactiveApplication.policyMixture_policy, PMF.support_bind] at chosen
  obtain ⟨index, _, member⟩ := Set.mem_iUnion₂.mp chosen
  exact each index past view response member event submitted

theorem sourceServiceTurnPolicy_submitsAtTurn (bound : (graph setup).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player) :
    SubmitsAtTurn setup leaks (sourceServiceTurnPolicy setup leaks bound turns timing profile who)
      who := by
  intro past view response chosen event submitted
  unfold sourceServiceTurnPolicy at chosen
  split at chosen
  · exact replayPolicy_submitsAtTurn setup leaks who past view response chosen event submitted
  · split at chosen
    · rename_i turnEvent _ owned
      exact policyMixture_submitsAtTurn setup leaks _ _ who (fun slot =>
        turnScheduledPolicy_submitsAtTurn setup leaks _ _ _ _ who
          (sourceServiceCanonicalOpportunity_submitsAtTurn setup leaks bound profile who
            turnEvent)
          (replayPolicy_submitsAtTurn setup leaks who)) past view response chosen event submitted
    · exact replayPolicy_submitsAtTurn setup leaks who past view response chosen event
        submitted

/-- Deciding a fixed action at the first turn submits only for that event,
and only at an input where it is the owner's turn. -/
theorem decidedTurnPolicy_submitsAtTurn (bound : (graph setup).EventId → Nat) (owner : Player)
    (event : (graph setup).EventId)
    (action : (graph setup).Action event) :
    SubmitsAtTurn setup leaks (decidedTurnPolicy setup leaks bound owner event action) owner := by
  intro past view response chosen other submitted
  unfold decidedTurnPolicy ReactiveApplication.turnScheduledPolicy at chosen
  dsimp only at chosen
  split at chosen
  · rename_i first
    have turn : view.application.publicView.ownTurn? owner = some event := by
      unfold sourceServiceTurn at first
      split at first
      · assumption
      · cases first
    unfold decidedOpportunity at chosen
    split at chosen
    · exact replayPolicy_submitsAtTurn setup leaks owner past view response chosen other
        submitted
    · split at chosen
      · split at chosen
        · exact replayPolicy_submitsAtTurn setup leaks owner past view response chosen other
            submitted
        · rw [PMF.mem_support_pure_iff] at chosen
          subst chosen
          rw [submittedEvent_canonicalServiceDecision setup leaks owner past view event action
            other submitted]
          exact turn
      · exact replayPolicy_submitsAtTurn setup leaks owner past view response chosen other
          submitted
  · exact replayPolicy_submitsAtTurn setup leaks owner past view response chosen other submitted

/-- A round of players that submit only at their own turns keeps every
recorded submission at its author's turn. -/
theorem round_submissionsAtTurn {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    (atTurn : ∀ who, SubmitsAtTurn setup leaks (players who) who)
    {execution next : (application setup leaks).Execution}
    (valid : SubmissionsAtTurn setup leaks execution)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    SubmissionsAtTurn setup leaks next := by
  let app := application setup leaks
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  rcases cases with ⟨_, rfl⟩ | ⟨who, _, response, chosen, rfl⟩
  · intro player entry member
    rw [recallEq] at member
    exact valid player entry member
  · intro player entry member event submitted
    by_cases same : player = who
    · subst player
      obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
      rw [recalled] at member
      rcases List.mem_append.mp member with prior | fresh
      · rw [recallEq] at prior
        exact valid who entry prior event submitted
      · rw [List.mem_singleton] at fresh
        subst fresh
        exact atTurn who _ _ response chosen event submitted
    · rw [app.respond_recall_other middle who player same response, recallEq] at member
      exact valid player entry member event submitted

/-- Every round answers its activation at the scheduler's public view. -/
theorem round_activationsAnswered {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    {execution next : (application setup leaks).Execution}
    (valid : ActivationsAnswered setup leaks execution)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    ActivationsAnswered setup leaks next := by
  let app := application setup leaks
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have recorded := app.dispatch_environmentRecall players command execution next dispatched
  obtain ⟨middle', moved', resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have recallEq := app.environmentStep_recall execution middle' command moved'
  have grows : ∀ who, execution.recall who ⊆ next.recall who := by
    intro who
    change next ∈ (app.resume players (command.actor? app) middle').support at resumed
    cases actor : command.actor? app with
    | none =>
        rw [actor] at resumed
        simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
        subst resumed
        rw [recallEq]
    | some player =>
        rw [actor] at resumed
        change next ∈ (app.invoke players player middle').support at resumed
        rw [ReactiveApplication.invoke, PMF.support_map] at resumed
        obtain ⟨response, _, rfl⟩ := resumed
        rw [← recallEq]
        exact app.respond_recall_mono middle' player who response
  intro entry member who activated
  rw [recorded] at member
  rcases List.mem_append.mp member with prior | fresh
  · obtain ⟨answer, answered, viewEq⟩ := valid entry prior who activated
    exact ⟨answer, grows who answered, viewEq⟩
  · rw [List.mem_singleton] at fresh
    subst fresh
    change command = .activate who at activated
    subst activated
    have sameApp := activation_application setup leaks execution middle' who moved'
    change next ∈ (app.resume players (some who) middle').support at resumed
    change next ∈ (app.invoke players who middle').support at resumed
    rw [ReactiveApplication.invoke, PMF.support_map] at resumed
    obtain ⟨response, _, rfl⟩ := resumed
    obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle' who response
    refine ⟨⟨middle'.observe app who, response, emitted⟩, ?_, ?_⟩
    · rw [recalled]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · change middle'.application.publicView = execution.application.publicView
      rw [sameApp]

/-- Both facts hold along rounds of players that submit only at their own
turns, from initialization under every scheduler. -/
theorem roundsFrom_turnFacts {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    (atTurn : ∀ who, SubmitsAtTurn setup leaks (players who) who) (count : Nat)
    (execution : (application setup leaks).Execution)
    (supported : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    SubmissionsAtTurn setup leaks execution ∧ ActivationsAnswered setup leaks execution := by
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      cases (PMF.mem_support_pure_iff _ _).mp reached
      constructor
      · intro who entry member
        simp [ReactiveApplication.Execution.initial] at member
      · intro entry member
        simp [ReactiveApplication.Execution.initial] at member
  | succ count ih =>
      rw [ReactiveApplication.roundsFrom_succ] at supported
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨submissions, answered⟩ := ih prior priorMem
      exact ⟨round_submissionsAtTurn setup leaks atTurn submissions moved,
        round_activationsAnswered setup leaks answered moved⟩

/-- Rounds of players that submit only at their own turns keep both facts. -/
theorem runRounds_turnFacts {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    (atTurn : ∀ who, SubmitsAtTurn setup leaks (players who) who) (count : Nat)
    (execution next : (application setup leaks).Execution)
    (submissions : SubmissionsAtTurn setup leaks execution)
    (answered : ActivationsAnswered setup leaks execution)
    (reached : next ∈ ((application setup leaks).runRounds scheduler players count
      execution).support) :
    SubmissionsAtTurn setup leaks next ∧ ActivationsAnswered setup leaks next := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨submissions, answered⟩
  | succ count ih =>
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact ih middle (round_submissionsAtTurn setup leaks atTurn submissions moved)
        (round_activationsAnswered setup leaks answered moved) rest

/-- A response never changes a candidate whose meaning is fixed. -/
theorem respond_candidate_fixed (execution : (application setup leaks).Execution)
    (who : Player) (response : (application setup leaks).Action)
    (handle : Handle (graph setup))
    (fixed : execution.application.candidates.lookup handle ≠ .fresh) :
    (execution.respond (application setup leaks) who response).application.candidates.lookup
      handle = execution.application.candidates.lookup handle := by
  rcases response with ⟨_ | (material | id)⟩
  · rfl
  · change (submitStep (material.call.register execution.application who) who
      material.call.packet).candidates.lookup handle = _
    have registered : (material.call.register execution.application who).candidates.lookup
        handle = execution.application.candidates.lookup handle := by
      rcases material with ⟨⟨packet, opening⟩, evidence⟩
      cases packet with
      | commitment event candidate =>
          rcases candidate with ⟨owner, slot⟩
          cases slot <;> cases opening <;> simp only [Submission.register]
          by_cases same : owner = who
          · simp only [same, ↓reduceIte]
            exact CommitmentCandidates.lookup_prepare_eq_of_not_fresh _ _ _ _ _ fixed
          · simp only [same, ↓reduceIte]
      | opening | withhold | malformed => rfl
    rw [← registered] at fixed ⊢
    unfold submitStep
    split
    · split
      · exact CommitmentCandidates.lookup_freeze_eq_of_not_fresh _ _ _ fixed
      · rfl
    all_goals rfl
  · rfl

/-- An environment step never changes a candidate whose meaning is fixed. -/
theorem environmentStep_candidate_fixed (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (moved : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (handle : Handle (graph setup))
    (fixed : execution.application.candidates.lookup handle ≠ .fresh) :
    next.application.candidates.lookup handle =
      execution.application.candidates.lookup handle := by
  cases command with
  | activate who =>
      rw [activation_application setup leaks execution next who moved]
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => rfl
      | some message =>
          change (((application setup leaks).handle execution.application
            message).getD execution.application).candidates.lookup
              handle = _
          cases reactiveAccepted : (application setup leaks).handle execution.application
              message with
          | none => rfl
          | some state =>
              have accepted := reactiveHandle_call reactiveAccepted
              change state.candidates.lookup handle = _
              cases call : message.payload.call with
              | commitment event candidate =>
                  rw [call] at accepted
                  rw [(handle_commitment_tables (runtime setup) _ state _ event candidate
                    accepted).1]
                  exact CommitmentCandidates.lookup_freeze_eq_of_not_fresh _ _ _ fixed
              | opening event candidate raw =>
                  rw [call] at accepted
                  rw [(handle_resolution_tables (runtime setup) _ state _
                    (by intros; simp) accepted).2]
              | withhold event =>
                  rw [call] at accepted
                  rw [(handle_resolution_tables (runtime setup) _ state _
                    (by intros; simp) accepted).2]
              | malformed raw =>
                  rw [call] at accepted
                  simp [EventGraphRuntime.handle] at accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state.candidates.lookup handle = _
      rw [(environmentStep_tables (runtime setup) _ state command changed).2]

/-- A round never changes a candidate whose meaning is fixed. -/
theorem round_candidate_fixed {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    {execution next : (application setup leaks).Execution}
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support)
    (handle : Handle (graph setup))
    (fixed : execution.application.candidates.lookup handle ≠ .fresh) :
    next.application.candidates.lookup handle =
      execution.application.candidates.lookup handle := by
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
  have stepped := environmentStep_candidate_fixed setup leaks execution middle command moved
    handle fixed
  rcases cases with ⟨_, rfl⟩ | ⟨who, _, response, _, rfl⟩
  · exact stepped
  · rw [respond_candidate_fixed setup leaks middle who response handle (stepped ▸ fixed),
      stepped]

end Vegas
