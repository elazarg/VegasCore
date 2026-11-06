/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceFirstTurnOpportunity
import Vegas.Game.SourceServiceTurnSubmissions
import Vegas.Game.SourceServiceCanonicalAcceptance
import Vegas.Game.SourceServiceAcceptedContinuation
import Vegas.Game.SourceServiceSilentContinuation
import Vegas.Game.SourceServiceChanceContinuation
import Vegas.Game.SourceServiceSiteBridge
import Vegas.Compile.EventGraphCanonical
import Interaction.ReactiveMixtureRounds

/-! # First-turn source continuation

The first ready callback separates the source action mixture. Silent actions
and transmitting actions have their chosen whole graph continuation, including
automatic completion. Waiting before that callback preserves the configuration;
the reaction contract places the callback inside its protected inclusion window.
The first-callback mixture and fixed-action continuation hold with arbitrary
other player policies. Composing them with the source residual law gives the
full normalized source configuration law under the asynchronous service contract.
-/

noncomputable section

namespace Vegas

section RecordedDecisions
open SourceProgram EventGraphRuntime GameTheory.Math.Probability Interaction
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

private theorem firstTurn_noRepeatedEvent
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (event : (serviceGraph setup mode).EventId)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (member : response ∈ (serviceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) profile owner past view).support)
    (recorded : (serviceRuntime setup mode deadline).eventRecorded leaks past event = true) :
    (serviceRuntime setup mode deadline).submittedEvent? leaks response ≠ some event := by
  intro named
  have serving := sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns
    (firstTurnTiming setup turns mode) profile owner past view response member event named
  by_cases owned : (serviceGraph setup mode).actor? event = some owner
  · by_cases first : serviceTurn setup mode deadline leaks owner event past view = some 0
    · rw [sourceServiceTurnPolicy_firstTurn owned first] at member
      simp only [serviceCanonicalOpportunity, serviceReferenceOpportunity, recorded, ↓reduceIte,
        ReactiveApplication.silentPolicy_apply] at member
      cases (PMF.mem_support_pure_iff _ _).mp member
      cases named
    · rw [sourceServiceTurnPolicy_laterTurn owned serving first] at member
      cases (PMF.mem_support_pure_iff _ _).mp member
      cases named
  · simp only [serviceTurnPolicy, serviceReferenceTurnPolicy, serving, owned, ↓reduceDIte,
      ReactiveApplication.silentPolicy_apply] at member
    cases (PMF.mem_support_pure_iff _ _).mp member
    cases named

/-- The fixed-action member never resubmits an event already recorded in own recall. -/
private theorem fixedAction_noRepeatedEvent
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (event : (serviceGraph setup mode).EventId) (action : (serviceGraph setup mode).Action event)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (member : response ∈ (if serviceTurn setup mode deadline leaks owner event past view = some 0
      then decidedOpportunity setup leaks bound owner event action past view
      else serviceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) profile owner past view).support)
    (recorded : (serviceRuntime setup mode deadline).eventRecorded leaks past event = true) :
    (serviceRuntime setup mode deadline).submittedEvent? leaks response ≠ some event := by
  by_cases first : serviceTurn setup mode deadline leaks owner event past view = some 0
  · rw [ite_eq_left first] at member
    simp only [decidedOpportunity, recorded, ↓reduceIte,
      ReactiveApplication.silentPolicy_apply] at member
    cases (PMF.mem_support_pure_iff _ _).mp member
    intro impossible
    cases impossible
  · rw [ite_eq_right first] at member
    exact firstTurn_noRepeatedEvent setup mode deadline leaks bound turns profile owner event
      past view response member recorded

end RecordedDecisions

section Waiting
open SourceProgram EventGraphRuntime EventGraph GameTheory.Math.Probability Interaction
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

private theorem first_of_never
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup runtime leaks).Execution) (owner : Player)
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? owner = some event)
    (never : ∀ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event) :
    serviceTurn setup .sequential runtime.deadline leaks owner event (execution.logs owner)
      (execution.observe (application setup runtime leaks) owner) = some 0 := by
  change (if execution.application.publicView.ownTurn? owner = some event then
    some ((execution.logs owner).countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? owner = some event)) else none) =
        some 0
  simp only [turn, ↓reduceIte, Option.some.injEq]
  rw [List.countP_eq_zero]
  intro entry member
  simpa only [Bool.not_eq_true, decide_eq_false_iff_not] using never entry member

private theorem waiting_no_pending
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    (control : (application setup runtime leaks).Control)
    (trace : ((application setup runtime leaks).protocol (initialLaw setup)
      horizon scheduler).Trace (some control))
    (owner : Player) (event : (graph setup).EventId)
    (truthful : OwnSubmissionsAtTurn setup leaks control.execution owner)
    (never : ∀ entry ∈ control.execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event) :
    ∀ message ∈ control.execution.network.pending, message.sender = owner →
      message.payload.call.event? (graph setup) ≠ some event := by
  have facts := legalFacts setup leaks horizon scheduler control trace
  intro message pending sender named
  obtain ⟨entry, entryPresent, material, transmitted, _emitted, state, known, packet⟩ :=
    facts.provenance.pending message pending
  have old : entry ∈ control.execution.logs owner := sender ▸ entryPresent
  have call : material.call.packet = message.payload.call :=
    congrArg (fun value => value.call) packet
  have submitted : runtime.submittedEvent? leaks entry.action = some event := by
    simp only [EventGraphRuntime.submittedEvent?, transmitted]
    rw [call]
    exact named
  exact never entry old (truthful entry old event submitted)

private theorem first_callback_runUntil
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (delay bound : (graph setup).EventId → Nat)
    (reference : (graph setup).BehavioralProfile)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely runtime delay bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (action : (graph setup).Action event)
    (atResponse : ∀ remaining (execution : (application setup runtime leaks).Execution),
      ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩) →
      ∀ ready : execution.application.config.cut.Ready event,
      serviceTurn setup .sequential runtime.deadline leaks owner event (execution.logs owner)
        (execution.observe (application setup runtime leaks) owner) = some 0 →
      execution.application.publicView.InclusionFitsDeadline runtime bound event →
      OwnSubmissionsAtTurn setup leaks execution owner →
      (∀ entry ∈ execution.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event) →
      EffectiveAction execution.application.config event action →
      ∀ response ∈ (players owner (execution.logs owner)
          (execution.observe (application setup runtime leaks) owner)).support,
        (((application setup runtime leaks).runUntil scheduler players
          (fun final => event ∈ final.application.config.cut.completed) remaining
          (execution.respond (application setup runtime leaks) owner response)).bind fun final =>
          (graph setup).runPlan
            ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
            final.application.config.remaining final.application.config) =
        (execution.application.config.step event ready action).bind fun after =>
          (graph setup).runPlan
            ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
            after.remaining after) :
    ∀ remaining (execution : (application setup runtime leaks).Execution),
      ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining, none, execution⟩) →
      ∀ ready : execution.application.config.cut.Ready event,
      OwnSubmissionsAtTurn setup leaks execution owner →
      (∀ entry ∈ execution.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event) →
      ActivationsAnswered setup leaks execution →
      EffectiveAction execution.application.config event action →
      (((application setup runtime leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) remaining execution).bind
        fun final => (graph setup).runPlan
          ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
            final.application.config.remaining final.application.config) =
        (execution.application.config.step event ready action).bind fun after =>
          (graph setup).runPlan
            ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
            after.remaining after := by
  classical
  let app := application setup runtime leaks
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let continuation := fun config : (graph setup).Config =>
    (graph setup).runPlan
            ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
      config.remaining config
  have stepEq {before after : (graph setup).Config} (same : after = before)
      (readyBefore : before.cut.Ready event) (readyAfter : after.cut.Ready event) :
      (after.step event readyAfter action).bind continuation =
        (before.step event readyBefore action).bind continuation := by
    subst after
    rfl
  intro remaining
  induction remaining with
  | zero =>
      intro execution trace ready _ _ _ _
      have terminal := contract.completes _ trace (by exact ⟨rfl, rfl⟩)
      exact (ready.1 (by rw [terminal]; exact Finset.mem_univ _)).elim
  | succ remaining ih =>
      intro execution trace ready truthful never answered effective
      have turn := ownTurn?_of_ready setup execution.application ready owned
      have first := first_of_never runtime leaks execution owner event turn never
      have fits := firstTurn_inclusionFits contract timely trace answered owned ready first
      have facts := legalFacts setup leaks horizon scheduler _ trace
      have safe := waiting_no_pending runtime leaks _ trace owner event truthful never
      have pending : ¬ stop execution := ready.1
      change (app.runUntil scheduler players stop (remaining + 1) execution).bind
        (fun final => continuation final.application.config) = _
      rw [ReactiveApplication.runUntil, ite_eq_right pending, PMF.bind_bind]
      apply (bind_congr_on_support _ fun next reached => ?_).trans (PMF.bind_const _ _)
      obtain ⟨command, selected, middle, moved, cases⟩ := round_cases (setup := setup) leaks reached
      have sameMiddle := environment_waiting_config runtime leaks execution middle command event
        owner ready owned fits.withinDeadline facts.quiescent safe moved
      have recallEq := app.environmentStep_recall execution middle command moved
      have readyMiddle : middle.application.config.cut.Ready event := sameMiddle.symm ▸ ready
      obtain ⟨nextTrace⟩ := app.raw_trace_round (initialLaw setup) horizon scheduler players
        remaining execution next trace reached
      have truthfulMiddle : OwnSubmissionsAtTurn setup leaks middle owner := by
        intro entry present
        rw [recallEq] at present
        exact truthful entry present
      rcases cases with ⟨_, nextEq⟩ | ⟨who, active, response, member, nextEq⟩
      · subst next
        exact (ih middle nextTrace readyMiddle truthfulMiddle
          (by simpa only [recallEq] using never)
          (round_activationsAnswered setup leaks answered reached)
          (sameMiddle.symm ▸ effective)).trans (stepEq sameMiddle ready readyMiddle)
      · subst next
        by_cases same : who = owner
        · subst who
          have commandEq : command = .activate owner := by
            cases command <;> simp_all [ReactiveApplication.Command.actor?]
          have appEq := activation_application (setup := setup) leaks execution middle owner
            (commandEq ▸ moved)
          have firstMiddle := first_of_never runtime leaks middle owner event
            (ownTurn?_of_ready setup middle.application readyMiddle owned)
            (by simpa only [recallEq] using never)
          have fitsMiddle : middle.application.publicView.InclusionFitsDeadline runtime bound
              event := by rw [appEq]; exact fits
          obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
            remaining execution middle command trace selected moved
          rw [active] at middleTrace
          exact (atResponse remaining middle middleTrace readyMiddle firstMiddle fitsMiddle
            truthfulMiddle
            (by simpa only [recallEq] using never)
            (sameMiddle.symm ▸ effective) response member).trans
              (stepEq sameMiddle ready readyMiddle)
        · have sameNext : (middle.respond app who response).application.config =
              execution.application.config :=
            ((runtime.reactive_respond_application leaks middle who response).1).trans sameMiddle
          have ownerRecall := app.respond_recall_other middle who owner (Ne.symm same) response
          have nextRecall : (middle.respond app who response).logs owner =
              execution.logs owner := ownerRecall.trans (congrFun recallEq owner)
          have readyNext : (middle.respond app who response).application.config.cut.Ready event :=
            sameNext.symm ▸ ready
          exact (ih _ nextTrace readyNext (by
              intro entry present
              rw [nextRecall] at present
              exact truthful entry present)
            (by
              intro entry present
              rw [nextRecall] at present
              exact never entry present)
            (round_activationsAnswered setup leaks answered reached)
            (sameNext.symm ▸ effective)).trans (stepEq sameNext ready readyNext)

end Waiting

section ActionMixture
open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- An honest owner's first callback draws its fixed source action before
stopped native play, with arbitrary other player policies. -/
theorem sourceService_firstTurn_mixture
    {horizon turns : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (background : Player → (application setup runtime leaks).Policy)
    (follows : background owner = serviceTurnPolicy setup .sequential runtime.deadline leaks
      bound turns (firstTurnTiming setup turns) profile owner)
    (execution : (application setup runtime leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      background event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (law : PMF ((graph setup).Action event))
    (callback : ∀ current : (application setup runtime leaks).Execution,
      current.application.config = execution.application.config →
      sourceServiceCanonicalPolicy setup runtime leaks profile owner (current.logs owner)
          (current.observe (application setup runtime leaks) owner) =
        law.map (fun action => runtime.canonicalServiceDecision leaks owner (current.logs owner)
          (current.observe (application setup runtime leaks) owner) event action)) :
    let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
      (firstTurnTiming setup turns) profile
    ((application setup runtime leaks).runUntilHorizon scheduler background
      (fun final => event ∈ final.application.config.cut.completed) horizon execution) =
      law.bind (fun action => (application setup runtime leaks).runUntilHorizon scheduler
        (Function.update background owner (fun past view =>
          if serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0
          then decidedOpportunity setup leaks bound owner event action past view
          else players owner past view))
        (fun final => event ∈ final.application.config.cut.completed) horizon execution) := by
  classical
  let app := application setup runtime leaks
  let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
    (firstTurnTiming setup turns) profile
  let first := fun past view =>
    serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0
  let member := fun (action : (graph setup).Action event) past view =>
    if first past view then decidedOpportunity setup leaks bound owner event action past view
      else players owner past view
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let invariant := fun current : app.Execution =>
    event ∉ current.application.config.cut.completed →
      current.application.config = execution.application.config
  have ready : execution.application.config.cut.Ready event :=
    boundary.ordered.ready event.isLt
  have once : ∀ past view, first past view → ∀ before entry, before ++ [entry] <+: past →
      ¬ first before entry.beforeView := by
    intro past view selected before entry prefixed earlier
    have memberEntry : entry ∈ past := prefixed.subset (by simp)
    exact (sourceServiceTurn_first selected).2 entry memberEntry
      (sourceServiceTurn_first earlier).1
  have atFirst : ∀ remaining current,
      (app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining + 1, none, current⟩) →
      invariant current → ¬ stop current →
      ∀ command ∈ (scheduler current.environmentRecall (current.observeEnvironment app)).support,
      ∀ middle ∈ (current.environmentStep app command).support,
        command.actor? app = some owner → first (middle.logs owner) (middle.observe app owner) →
        players owner (middle.logs owner) (middle.observe app owner) =
          law.bind (fun action => member action (middle.logs owner)
            (middle.observe app owner)) := by
    intro remaining current _ valid unfinished command _ middle moved active firstNow
    have commandEq : command = .activate owner := by
      cases command <;> simp_all [ReactiveApplication.Command.actor?]
    subst command
    have sameApplication := activation_application (setup := setup) leaks current middle owner moved
    have sameConfig : middle.application.config = execution.application.config :=
      (congrArg EventGraphRuntime.State.config sameApplication).trans (valid unfinished)
    change serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) profile owner (middle.logs owner)
          (middle.observe app owner) = _
    rw [sourceServiceTurnPolicy_firstTurn owned firstNow]
    simp only [member, first, firstNow, ↓reduceIte]
    unfold serviceCanonicalOpportunity serviceReferenceOpportunity decidedOpportunity
    by_cases recorded : runtime.eventRecorded leaks (middle.logs owner) event = true
    · simp only [recorded, ↓reduceIte, PMF.bind_const]
    · have notRecorded := Bool.eq_false_of_not_eq_true recorded
      simp only [notRecorded, Bool.false_eq_true, ↓reduceIte]
      by_cases fits : (middle.observe app owner).application.publicView.InclusionFitsDeadline
          runtime bound event
      · simp only [fits, ↓reduceIte]
        have compiled := congrArg (fun responseLaw : PMF app.Action => responseLaw.bind
          (fun response => if response.transmission = none then
            app.silentPolicy (middle.logs owner) (middle.observe app owner)
          else PMF.pure response)) (callback middle sameConfig)
        exact compiled.trans (by rw [PMF.bind_map]; rfl)
      · simp only [fits, ↓reduceIte, PMF.bind_const]
  have preserved : ∀ remaining current,
      (app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining + 1, none, current⟩) →
      invariant current → ¬ stop current →
      ∀ next ∈ (app.round scheduler (Function.update background owner (players owner))
        current).support, invariant next := by
    intro remaining current _ valid unfinished next reached pending
    obtain ⟨command, _, middle, moved, cases⟩ := round_cases (setup := setup) leaks reached
    have path := (runtime.reactiveApplication_graphSteps leaks).environmentStep
      current middle command moved
    have nextPath : Relation.ReflTransGen EventGraph.Config.Step current.application.config
        next.application.config := by
      rcases cases with ⟨_, rfl⟩ | ⟨who, _, response, _, rfl⟩
      · exact path
      · rw [(runtime.reactive_respond_application leaks middle who response).1]
        exact path
    have readyCurrent : current.application.config.cut.Ready event :=
      (valid unfinished).symm ▸ ready
    have same := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
      (fun _ otherReady => setup.eventGraph.sequentialize_ready_unique _ otherReady readyCurrent)
      pending nextPath
    exact same.trans (valid unfinished)
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
    background
    execution.environmentRecall.length bounded execution boundary.supported
  have clean : ∀ before entry, before ++ [entry] <+: execution.logs owner →
      ¬ first before entry.beforeView := by
    intro before entry prefixed earlier
    have memberEntry : entry ∈ execution.logs owner := prefixed.subset (by simp)
    exact boundary.untouched event le_rfl owner entry memberEntry
      (PublicView.ownTurn?_spec _ owner event (sourceServiceTurn_first earlier).1).1
  have mixed := app.runUntil_mixture_at_first (initialLaw setup) horizon scheduler background owner
    (players owner) law member first once (by intro action past view away; simp [member, away])
    stop invariant atFirst preserved (horizon - execution.environmentRecall.length) 0 execution
    (by simpa only [Nat.zero_add] using trace) (fun _ => rfl) clean
  have restored : Function.update background owner (players owner) = background := by
    funext player
    by_cases same : player = owner
    · subst player
      exact (Function.update_self ..).trans follows.symm
    · exact Function.update_of_ne same _ _
  simpa only [ReactiveApplication.runUntilHorizon, restored] using mixed

end ActionMixture

section Silence
open SourceProgram EventGraphRuntime GameTheory.Math.Probability Interaction
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

private theorem fixed_silent_client_quiet
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event)
    (silent : SilentAction event action)
    (past : List (application setup runtime leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView)
    (serving : view.application.publicView.ownTurn? owner = some event) :
    (if serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0 then
      decidedOpportunity setup leaks bound owner event action past view
    else serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
      (firstTurnTiming setup turns) profile owner past view) = PMF.pure ⟨none⟩ := by
  by_cases first :
      serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0
  · rw [ite_eq_left first]
    exact decidedOpportunity_silent action past view
      (canonicalServiceDecision_silent owner past view event action silent)
  · rw [ite_eq_right first]
    by_cases owned : (graph setup).actor? event = some owner
    · exact sourceServiceTurnPolicy_laterTurn owned serving first
    · simp only [serviceTurnPolicy, serviceReferenceTurnPolicy, serving, owned, ↓reduceDIte,
        ReactiveApplication.silentPolicy_apply]

/-- Fixing a silent first-turn action has that action's full graph continuation
from the original source client's completion boundary. -/
private theorem firstTurn_fixed_silent_runUntil_bind_runPlan
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon turns : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat)
    (source : BehavioralProfile setup.program) (reference : (graph setup).BehavioralProfile)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (background : Player → (application setup runtime leaks).Policy)
    (follows : background owner = serviceTurnPolicy setup .sequential runtime.deadline leaks
      bound turns (firstTurnTiming setup turns) source owner)
    (action : (graph setup).Action event) (silent : SilentAction event action)
    (execution : (application setup runtime leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      background event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
      (firstTurnTiming setup turns) source
    let member := fun past view =>
      if serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0 then
        decidedOpportunity setup leaks bound owner event action past view
      else players owner past view
    (((application setup runtime leaks).runUntilHorizon scheduler
        (Function.update background owner member)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        (graph setup).runPlan ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
          stopped.application.config.remaining stopped.application.config) =
      (execution.application.config.step event (boundary.ordered.ready event.isLt) action).bind
        fun after => (graph setup).runPlan
          ((graph setup).policyPlan reference (graph setup).canonicalScheduler) after.remaining
            after := by
  classical
  let app := application setup runtime leaks
  let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
    (firstTurnTiming setup turns) source
  let member := fun past view =>
    if serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0 then
      decidedOpportunity setup leaks bound owner event action past view
    else players owner past view
  have atTurn : SubmitsAtTurn setup leaks (background owner) owner := by
    rw [follows]
    exact sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns (firstTurnTiming setup
      turns)
      source owner
  have truthful : OwnSubmissionsAtTurn setup leaks execution owner :=
    atTurn.roundsFrom setup leaks (initialLaw setup) execution.environmentRecall.length execution
      boundary.supported
  have safe := boundary.no_pending_of_ownSubmissions runtime leaks scheduler background event
    execution
    owner truthful
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
    background
    execution.environmentRecall.length bounded execution boundary.supported
  apply silent_runUntil_bind_runPlan runtime leaks reference scheduler
    (Function.update background owner member) horizon contract.completes event owner owned action
      silent execution (boundary.ordered.ready event.isLt) trace safe
  intro past view serving
  rw [Function.update_self]
  exact fixed_silent_client_quiet runtime leaks bound turns source owner event action silent past
    view serving

end Silence

section Acceptance
open SourceProgram EventGraphRuntime EventGraph GameTheory.Math.Probability Interaction
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- A supported transmitting fixed first callback has its chosen full continuation. -/
private theorem firstTurn_fixed_accepted_runUntil_bind_runPlan
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon remaining turns : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat)
    (source : BehavioralProfile setup.program) (reference : (graph setup).BehavioralProfile)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (background : Player → (application setup runtime leaks).Policy)
    (action : (graph setup).Action event)
    (execution : (application setup runtime leaks).Execution)
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (ready : execution.application.config.cut.Ready event)
    (turn : execution.application.publicView.ownTurn? owner = some event)
    (first : serviceTurn setup .sequential runtime.deadline leaks owner event
      (execution.logs owner) (execution.observe (application setup runtime leaks) owner) = some 0)
    (fits : execution.application.publicView.InclusionFitsDeadline runtime bound event)
    (truthful : OwnSubmissionsAtTurn setup leaks execution owner)
    (never : ∀ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event)
    (material : (application setup runtime leaks).Submission)
    (sends : (runtime.canonicalServiceDecision leaks owner (execution.logs owner)
      (execution.observe (application setup runtime leaks) owner) event action).transmission =
        some material)
    (response : (application setup runtime leaks).Action)
    (selected : response ∈ (if serviceTurn setup .sequential runtime.deadline leaks owner event
        (execution.logs owner)
          (execution.observe (application setup runtime leaks) owner) = some 0
      then decidedOpportunity setup leaks bound owner event action (execution.logs owner)
        (execution.observe (application setup runtime leaks) owner)
      else serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) source owner (execution.logs owner)
          (execution.observe (application setup runtime leaks) owner)).support) :
    let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
      (firstTurnTiming setup turns) source
    let member := fun past view =>
      if serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0 then
        decidedOpportunity setup leaks bound owner event action past view
      else players owner past view
    (((application setup runtime leaks).runUntil scheduler (Function.update background owner member)
        (fun final => event ∈ final.application.config.cut.completed) remaining
        (execution.respond (application setup runtime leaks) owner response)).bind fun stopped =>
      (graph setup).runPlan ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
        stopped.application.config.remaining stopped.application.config) =
      (execution.application.config.step event ready action).bind fun after =>
        (graph setup).runPlan ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
          after.remaining after := by
  classical
  let app := application setup runtime leaks
  let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
    (firstTurnTiming setup turns) source
  let member := fun past view =>
    if serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0 then
      decidedOpportunity setup leaks bound owner event action past view
    else players owner past view
  let canonical := runtime.canonicalServiceDecision leaks owner (execution.logs owner)
    (execution.observe app owner) event action
  have unsent : runtime.eventRecorded leaks (execution.logs owner) event = false := by
    cases recorded : runtime.eventRecorded leaks (execution.logs owner) event with
    | false => rfl
    | true =>
        obtain ⟨entry, remembered, submitted⟩ :=
          (runtime.eventRecorded_iff leaks _ event).mp recorded
        exact (never entry remembered (truthful entry remembered event submitted)).elim
  have loud : canonical.transmission ≠ none := by
    rw [sends]
    intro impossible
    cases impossible
  have chosen : response = canonical := by
    rw [ite_eq_left first] at selected
    change response ∈ (if runtime.eventRecorded leaks (execution.logs owner) event then
      app.silentPolicy (execution.logs owner) (execution.observe app owner) else
      if execution.application.publicView.InclusionFitsDeadline runtime bound event then
        if canonical.transmission = none then
          app.silentPolicy (execution.logs owner) (execution.observe app owner)
        else PMF.pure canonical else
          app.silentPolicy (execution.logs owner)
            (execution.observe app owner)).support at selected
    simpa only [unsent, Bool.false_eq_true, ↓reduceIte, ite_eq_left fits, ite_eq_right loud,
      PMF.mem_support_pure_iff] using selected
  subst response
  let after := execution.respond app owner canonical
  let entry := respondEntry setup runtime leaks execution owner canonical
  let message := sentEnvelope setup runtime leaks execution owner material
  have configEq : after.application.config = execution.application.config :=
    (runtime.reactive_respond_application leaks execution owner canonical).1
  have recalled : after.logs owner = execution.logs owner ++ [entry] := by
    rw [runtime.respond_recall leaks execution owner owner canonical, ite_eq_left rfl]
    rfl
  have recorded : entry ∈ after.logs owner := by
    rw [recalled]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have call : FreshCall setup leaks owner event bound entry message := by
    dsimp only [entry, message]
    rw [respondEntry_of_transmission execution owner canonical material sends]
    exact canonical_freshCall trace bound owner event turn fits action material sends
  have signed := signedCommitments_history runtime leaks (initialLaw setup)
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨_, rfl⟩) horizon scheduler trace
  have sole : ∀ other ∈ after.logs owner,
      ¬ EmitsOtherFor runtime leaks other event message.id := by
    intro other remembered emits
    rw [recalled] at remembered
    rcases List.mem_append.mp remembered with old | fresh
    · obtain ⟨packet, emitted, _sender, named, _different⟩ := emits
      obtain ⟨_sender, content, transmitted, packetEq⟩ :=
        signed.emissions owner other old packet emitted
      have submitted : runtime.submittedEvent? leaks other.action = some event := by
        simp only [EventGraphRuntime.submittedEvent?, transmitted]
        rw [← packetEq]
        exact named
      exact never other old (truthful other old event submitted)
    · obtain rfl := List.mem_singleton.mp fresh
      obtain ⟨packet, emitted, _sender, _named, different⟩ := emits
      have emittedEq : entry.emitted = some message := call.emitted
      have same : packet = message := Option.some.inj (emitted.symm.trans emittedEq)
      exact different (congrArg Message.id same)
  obtain ⟨output, witness⟩ := canonical_response_witness execution owner event turn action material
    sends
  have witnessAfter : AcceptanceWitness event message after.application.config action output
      after.application := by
    rw [configEq]
    have stateEq : after.application = app.submit execution.application owner material := by
      unfold after ReactiveApplication.Execution.respond
      rw [sends]
    rw [stateEq]
    exact witness
  obtain ⟨afterTrace⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler remaining
    execution owner canonical trace
  have noRepeat : ∀ past view response,
      response ∈ ((Function.update background owner member) owner past view).support →
      runtime.eventRecorded leaks past event = true →
      runtime.submittedEvent? leaks response ≠ some event := by
    intro past view response supported recorded
    rw [Function.update_self] at supported
    exact fixedAction_noRepeatedEvent setup .sequential runtime.deadline leaks bound turns source
      owner event action past view response supported recorded
  have accepted := FreshCall.accepted_runPlan runtime leaks reference scheduler
    (Function.update background owner member) bound contract.inclusion contract.completes
      event owner
      owned after afterTrace (configEq.symm ▸ ready) action output entry message recorded call sole
        witnessAfter noRepeat
  have accounted : execution.environmentRecall.length + remaining = horizon :=
    app.raw_trace_horizon (initialLaw setup) horizon scheduler trace
  have countEq : horizon - after.environmentRecall.length = remaining := by
    rw [ReactiveApplication.respond_environmentRecall]
    omega
  change (app.runUntil scheduler (Function.update background owner member)
    (fun final => event ∈ final.application.config.cut.completed)
    (horizon - after.environmentRecall.length) after).bind _ = _ at accepted
  rw [countEq] at accepted
  simpa only [configEq] using accepted

end Acceptance

section Compilation
open SourceProgram EventGraphRuntime GameTheory.Math.Probability Interaction
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

private theorem firstTurn_fixed_transmitting_runUntil_bind_runPlan
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon turns : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat)
    (source : BehavioralProfile setup.program) (reference : (graph setup).BehavioralProfile)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely runtime delay bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (background : Player → (application setup runtime leaks).Policy)
    (follows : background owner = serviceTurnPolicy setup .sequential runtime.deadline leaks
      bound turns (firstTurnTiming setup turns) source owner)
    (action : (graph setup).Action event)
    (execution : (application setup runtime leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      background event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (effective : EffectiveAction execution.application.config event action)
    (loud : ¬ SilentAction event action) :
    let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
      (firstTurnTiming setup turns) source
    let member := fun past view =>
      if serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0 then
        decidedOpportunity setup leaks bound owner event action past view
      else players owner past view
    (((application setup runtime leaks).runUntilHorizon scheduler
        (Function.update background owner member)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        (graph setup).runPlan ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
          stopped.application.config.remaining stopped.application.config) =
      (execution.application.config.step event (boundary.ordered.ready event.isLt) action).bind
        fun after => (graph setup).runPlan
          ((graph setup).policyPlan reference (graph setup).canonicalScheduler) after.remaining
            after := by
  classical
  let app := application setup runtime leaks
  let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
    (firstTurnTiming setup turns) source
  let member := fun past view =>
    if serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0 then
      decidedOpportunity setup leaks bound owner event action past view
    else players owner past view
  have atTurn : SubmitsAtTurn setup leaks (background owner) owner := by
    rw [follows]
    exact sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns (firstTurnTiming setup
      turns)
      source owner
  have truthful : OwnSubmissionsAtTurn setup leaks execution owner :=
    atTurn.roundsFrom setup leaks (initialLaw setup) execution.environmentRecall.length execution
      boundary.supported
  have never : ∀ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
    intro entry remembered turn
    exact boundary.untouched event le_rfl owner entry remembered
      (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
    background
    execution.environmentRecall.length bounded execution boundary.supported
  apply first_callback_runUntil runtime leaks scheduler (Function.update background owner member)
    delay bound reference contract timely owner event owned action ?_
      (horizon - execution.environmentRecall.length) execution trace
      (boundary.ordered.ready event.isLt) truthful never
      (roundsFrom_activationsAnswered _ execution boundary.supported) effective
  intro remaining current currentTrace ready first fits truthful never effective response selected
  rw [Function.update_self] at selected
  have turn := ownTurn?_of_ready setup current.application ready owned
  obtain ⟨material, sends⟩ := canonicalServiceDecision_transmits_of_effective runtime _ currentTrace
    owner event turn action effective loud
  exact firstTurn_fixed_accepted_runUntil_bind_runPlan runtime leaks scheduler delay bound source
    reference contract owner event owned background action current currentTrace ready turn first
    fits truthful
      never material sends response selected

/-- Fixing one owner's first source choice preserves its full canonical
continuation against arbitrary other players, including automatic completion. -/
theorem sourceService_fixedAction_continuation
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon turns : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat)
    (source : BehavioralProfile setup.program) (reference : (graph setup).BehavioralProfile)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely runtime delay bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (background : Player → (application setup runtime leaks).Policy)
    (follows : background owner = serviceTurnPolicy setup .sequential runtime.deadline leaks
      bound turns (firstTurnTiming setup turns) source owner)
    (action : (graph setup).Action event)
    (execution : (application setup runtime leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      background event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (effective : EffectiveAction execution.application.config event action) :
    let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
      (firstTurnTiming setup turns) source
    let member := fun past view =>
      if serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0 then
        decidedOpportunity setup leaks bound owner event action past view
      else players owner past view
    (((application setup runtime leaks).runUntilHorizon scheduler
        (Function.update background owner member)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        (graph setup).runPlan ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
          stopped.application.config.remaining stopped.application.config) =
      (execution.application.config.step event (boundary.ordered.ready event.isLt) action).bind
        fun after => (graph setup).runPlan
          ((graph setup).policyPlan reference (graph setup).canonicalScheduler) after.remaining
            after := by
  by_cases silent : SilentAction event action
  · exact firstTurn_fixed_silent_runUntil_bind_runPlan runtime leaks scheduler delay bound
      source reference contract owner event owned background follows action silent execution
      boundary bounded
  · exact firstTurn_fixed_transmitting_runUntil_bind_runPlan runtime leaks scheduler delay bound
      source reference contract timely owner event owned background follows action execution
      boundary bounded effective silent

variable [Finite Player]

private theorem firstTurn_completion_law
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon turns : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat)
    (source : BehavioralProfile setup.program)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely runtime delay bound)
    (authentic : ∀ who, (source who).AuthenticDisclosures setup.program)
    (event : (graph setup).EventId)
    (execution : (application setup runtime leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) source) event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
      (firstTurnTiming setup turns) source
    let plan := (graph setup).policyPlan (compileEventProfile setup.program source)
      (graph setup).canonicalScheduler
    let read := fun config : (graph setup).Config => decodeConfig? setup.program setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
      config.history
    ((application setup runtime leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
        (fun final => ((graph setup).runPlan plan final.application.config.remaining
          final.application.config).map read) =
      ((graph setup).runPlan plan execution.application.config.remaining
        execution.application.config).map read := by
  classical
  let app := application setup runtime leaks
  let players := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
    (firstTurnTiming setup turns) source
  let reference := compileEventProfile setup.program source
  let plan := (graph setup).policyPlan reference (graph setup).canonicalScheduler
  let read := fun config : (graph setup).Config => decodeConfig? setup.program setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
      config.history
  let continuation := fun config : (graph setup).Config =>
    (graph setup).runPlan plan config.remaining config
  have ready := boundary.ordered.ready event.isLt
  cases owned : (graph setup).actor? event with
  | none =>
      have chance := chance_runUntil_bind_runPlan runtime leaks reference scheduler players event
        owned (horizon - execution.environmentRecall.length) execution ready
      have projected := congrArg (PMF.map read) chance
      simpa only [ReactiveApplication.runUntilHorizon, PMF.map_bind] using projected
  | some owner =>
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
        execution.environmentRecall.length bounded execution boundary.supported
      obtain ⟨rank, ⟨residual⟩⟩ := SourceResidual.of_rawTrace source horizon scheduler trace
        ⟨horizon - execution.environmentRecall.length, none, execution⟩ rfl
      have sameRank := EventOrder.Cut.IsPrefix.unique residual.checkpoint.ordered boundary.ordered
      subst rank
      obtain ⟨law, head, callback, effective⟩ := residual.head_law runtime leaks event rfl ready
      have mixture := sourceService_firstTurn_mixture runtime leaks scheduler bound source
        owner event
        owned players rfl execution boundary bounded law (callback owner owned)
      have headContinuation : (continuation execution.application.config).map read =
          law.bind (fun action => (execution.application.config.step event ready action).bind
            (fun after => (continuation after).map read)) := by
        dsimp only [continuation, plan, reference]
        rw [residual.runPlan_readout_law, head]
        apply bind_congr_on_support _
        intro action _
        apply bind_congr_on_support _
        intro after supported
        obtain ⟨successor, _⟩ := residual.step event ready action after supported
        exact successor.runPlan_readout_law.symm
      change (app.runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
          (fun final => (continuation final.application.config).map read) = _
      rw [mixture, PMF.bind_bind]
      apply (bind_congr_on_support _ fun action member => ?_).trans headContinuation.symm
      have fixed :
          let member := fun past view =>
            if serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0
            then decidedOpportunity setup leaks bound owner event action past view
            else players owner past view
          (app.runUntilHorizon scheduler (Function.update players owner member)
            (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
              (fun final => continuation final.application.config) =
            (execution.application.config.step event ready action).bind continuation := by
        exact sourceService_fixedAction_continuation runtime leaks scheduler delay bound source
          reference contract timely owner event owned players rfl action execution boundary bounded
          (effective authentic action member)
      have projected := congrArg (PMF.map read) fixed
      simpa only [PMF.map_bind] using projected

/-- First-turn source clients preserve the full source configuration under the
asynchronous service contract and its reaction/inclusion timing budget. -/
theorem firstTurnSourceLaw_of_async
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon turns : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat)
    (source : BehavioralProfile setup.program)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely runtime delay bound)
    (authentic : ∀ who, (source who).AuthenticDisclosures setup.program) :
    FirstTurnSourceLaw setup .sequential runtime.deadline leaks horizon scheduler bound turns
      source := by
  apply firstTurnSourceLaw_of_completion_law setup runtime leaks turns source contract.completes
  dsimp only
  intro event execution boundary bounded
  exact firstTurn_completion_law runtime leaks scheduler delay bound source contract timely
    authentic event execution boundary bounded


/-- Actual first-turn clients preserve every observation of the original source's
full typed state and public default history. -/
theorem sourceServiceClientPolicy_outcome_law
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon turns : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat)
    (original : BehavioralProfile setup.program)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely runtime delay bound)
    {Outcome : Type*}
    (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    ((application setup runtime leaks).roundsFrom (initialLaw setup) scheduler
      (serviceClientPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) (normalizeDisclosureProfile setup.program original))
      horizon).map (fun execution =>
        (sourceReadout setup runtime leaks
          ((application setup runtime leaks).finished execution)).map
          (fun final => read (final.state, final.defaults))) =
      (setup.run original).map (fun final => some (read (final.state, final.defaults))) := by
  apply sourceServiceClientPolicy_outcome_law_of_firstTurn original ?_ read
  exact firstTurnSourceLaw_of_async runtime leaks scheduler delay bound
    (normalizeDisclosureProfile setup.program original) contract timely
      (fun who => BehavioralPolicy.normalizeDisclosures_authentic setup.program (original who))

/-- Actual clients and canonical compiled graph execution preserve the same
typed-state and public-default observations for every source profile. -/
theorem sourceServiceClientPolicy_graph_law
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon turns : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat)
    (original : BehavioralProfile setup.program)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely runtime delay bound)
    {Outcome : Type*}
    (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    ((application setup runtime leaks).roundsFrom (initialLaw setup) scheduler
      (serviceClientPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) (normalizeDisclosureProfile setup.program original))
      horizon).map (fun execution =>
        (sourceReadout setup runtime leaks
          ((application setup runtime leaks).finished execution)).map
          (fun final => read (final.state, final.defaults))) =
      ((setup.eventGraph.canonicalGame
          (setup.initialLaw.map setup.eventInputs)).play
        (compileEventProfile setup.program original)).map (fun terminal =>
          let final := terminalConfig setup.program terminal
          some (read (final.state, final.defaults))) := by
  rw [sourceServiceClientPolicy_outcome_law runtime leaks scheduler delay bound original contract
    timely read]
  have law := congrArg
    (PMF.map (fun final : Config Player L setup.program.terminalCtx =>
      some (read (final.state, final.defaults)))) (canonical_setup_law setup original)
  simpa only [PMF.map_comp, Function.comp_def] using law.symm

end Compilation

end Vegas
