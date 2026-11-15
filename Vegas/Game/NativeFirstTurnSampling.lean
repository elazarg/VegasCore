module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.BindingWindowTransport
public import Interaction.ReactiveMixtureRounds

@[expose] public section

/-! # Predrawing a first-turn decision in the native execution

A ready-independent owned decision can be sampled before the complete stopped native run,
with every background client active. The stopping predicate is arbitrary and unchanged
across sampled members.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

private theorem serviceReference_callback_of_pending_path
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent reference)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (origin current : (serviceApplication setup deps duration leaks).Execution)
    (ready : origin.application.config.cut.Ready event)
    (path : Relation.ReflTransGen Config.Step origin.application.config current.application.config)
    (unfinished : event ∉ current.application.config.cut.completed)
    {horizon remaining : Nat} {acting : Option Player}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨remaining, acting, current⟩)) :
    serviceReferencePolicy setup deps duration leaks reference owner (current.logs owner)
        (current.observe (serviceApplication setup deps duration leaks) owner) =
      (actionLaw reference origin.application.config event).map
        ((canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks owner
          (current.logs owner) (current.observe (serviceApplication setup deps duration leaks)
            owner) event) := by
  have currentReady := Config.Step.path_ready_of_not_completed path ready unfinished
  have turn := current.application.ownTurn?_of_ready (independent.actorSerial event)
    currentReady owned
  have active : owner ∉ current.application.config.defaulted :=
    current.application.active_of_ready_owned
      (legalFacts setup leaks horizon scheduler _ trace).quiescent currentReady owned
  rw [sourceServiceCanonicalPolicy_at_event_reference setup leaks reference owner current event
    turn owned, dite_eq_right active]
  have stable := independent.actionLaw_path_of_unfinished path ready unfinished
  rw [actionLaw_of_actor _ _ owned, dite_eq_right active] at stable
  exact congrArg (PMF.map _) stable

/-- A ready-independent owned decision can be drawn before any stopped native run. -/
theorem serviceReference_firstTurn_mixture_of_independent
    {horizon count remaining turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent reference)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (background : Player → (serviceApplication setup deps duration leaks).Policy)
    (follows : background owner = serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference owner)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop) [DecidablePred stop]
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨remaining + count, none, execution⟩))
    (untouched : Untouched setup leaks event execution) :
    let app := serviceApplication setup deps duration leaks
    let players := serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference
    app.runUntil scheduler background stop count execution =
      (actionLaw reference execution.application.config event).bind (fun action =>
        app.runUntil scheduler
          (Function.update background owner (fun past view =>
            if serviceTurn setup deps duration leaks owner event past view = some 0 then
              decidedOpportunity setup leaks bound owner event action past view
            else players owner past view)) stop count execution) := by
  classical
  intro app players
  let law := actionLaw reference execution.application.config event
  let first := fun past view => serviceTurn setup deps duration leaks owner event past view = some 0
  let member := fun (action : (serviceGraph setup deps).Action event) past view =>
    if first past view then decidedOpportunity setup leaks bound owner event action past view
    else players owner past view
  let invariant := fun current : app.Execution =>
    Relation.ReflTransGen Config.Step execution.application.config current.application.config
  have once : ∀ past view, first past view → ∀ before entry, before ++ [entry] <+: past →
      ¬ first before entry.beforeView := by
    intro past view selected before entry prefixed earlier
    have memberEntry : entry ∈ past := prefixed.subset (by simp)
    exact (sourceServiceTurn_first selected).2 entry memberEntry
      (sourceServiceTurn_first earlier).1
  have atFirst : ∀ remaining current,
      (app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨remaining + 1, none, current⟩) →
      invariant current → ¬ stop current →
      ∀ command ∈ (scheduler current.environmentRecall (current.observeEnvironment app)).support,
      ∀ middle ∈ (current.environmentStep app command).support,
        command.actor? app = some owner → first (middle.logs owner) (middle.observe app owner) →
        players owner (middle.logs owner) (middle.observe app owner) =
          law.bind (fun action => member action (middle.logs owner)
            (middle.observe app owner)) := by
    intro remaining current currentTrace valid unfinished command selected middle moved active
      firstNow
    have commandEq : command = .activate owner := by
      cases command <;> simp_all [ReactiveApplication.Command.actor?]
    subst command
    have sameApplication := activation_application (setup := setup) leaks current middle owner moved
    have middlePath : Relation.ReflTransGen Config.Step execution.application.config
        middle.application.config := by
      rw [sameApplication]
      exact valid
    have middlePending : event ∉ middle.application.config.cut.completed :=
      ((middle.application.publicView_eventReady event).mp
        (middle.application.publicView.ownTurn?_spec owner event
          (sourceServiceTurn_first firstNow).1).1).1
    obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup deps) horizon
      scheduler remaining current middle (.activate owner) currentTrace selected moved
    have callback := serviceReference_callback_of_pending_path reference independent owner event
      owned execution middle ready middlePath middlePending middleTrace
    change serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference owner (middle.logs owner)
        (middle.observe app owner) = _
    rw [sourceServiceTurnPolicy_firstTurn_reference owned firstNow]
    simp only [member, first, firstNow, ite_true]
    unfold serviceReferenceOpportunity decidedOpportunity
    by_cases recorded : (eventRecorded (serviceTimeouts setup deps duration)) leaks
        (middle.logs owner) event = true
    · simp only [recorded, ite_true, PMF.bind_const]
    · have notRecorded := Bool.eq_false_of_not_eq_true recorded
      simp only [notRecorded, Bool.false_eq_true, ite_false]
      by_cases fits : (middle.observe app owner).application.publicView.InclusionFitsDeadline
          (serviceTimeouts setup deps duration) bound event
      · simp only [fits, ite_true]
        have compiled := congrArg (fun responseLaw : PMF app.Action => responseLaw.bind
          (fun response => if response.transmission = none then
            app.silentPolicy (middle.logs owner) (middle.observe app owner)
          else PMF.pure response)) callback
        exact compiled.trans (by rw [PMF.bind_map]; rfl)
      · simp only [fits, ite_false, PMF.bind_const]
  have preserved : ∀ remaining current,
      (app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨remaining + 1, none, current⟩) →
      invariant current → ¬ stop current →
      ∀ next ∈ (app.round scheduler (Function.update background owner (players owner))
        current).support, invariant next := by
    intro remaining current _ valid _ next reached
    exact valid.trans (reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks
      scheduler (Function.update background owner (players owner)) current next reached)
  have clean : ∀ before entry, before ++ [entry] <+: execution.logs owner →
      ¬ first before entry.beforeView := by
    intro before entry prefixed earlier
    have memberEntry : entry ∈ execution.logs owner := prefixed.subset (by simp)
    exact untouched owner entry memberEntry
      (PublicView.ownTurn?_spec _ owner event (sourceServiceTurn_first earlier).1).1
  have mixed := app.runUntil_mixture_at_first
    (serviceInitialLaw setup deps) horizon scheduler background owner (players owner) law member
    first once (by intro action past view away; simp only [member, away, ite_false])
    stop invariant atFirst preserved count remaining execution trace .refl clean
  have restored : Function.update background owner (players owner) = background := by
    funext player
    by_cases same : player = owner
    · subst player
      exact (Function.update_self ..).trans follows.symm
    · exact Function.update_of_ne same _ _
  simpa only [restored] using mixed

end Vegas
