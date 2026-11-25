module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.TurnClient
public import Vegas.Pending.FixedOpportunity
public import Vegas.Pending.ReactiveGraphSteps
public import Interaction.ReactiveMessageReadout
public import Interaction.ReactiveMixtureRounds

@[expose] public section

/-! # Sampling an owned graph action before stopped native play -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  {initial : PMF (State graph)}

local notation "app" => (reactiveApplication timeouts) leaks

/-- An owner's first callback draws its graph action before native play stopped at
completion of the solitary event. The other players can use arbitrary policies. -/
theorem firstTurn_mixture
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (bound : graph.EventId → Nat) (client : graph.BehavioralProfile)
    (owner : Player) (event : graph.EventId)
    (owned : graph.actor? event = some owner)
    (background : Player → (app).Policy)
    (follows : background owner = turnPolicy timeouts leaks
      bound turns (EventGraphRuntime.firstTurnTiming graph turns) client owner)
    (execution : (app).Execution)
    (unique : ∀ other, execution.application.config.cut.Ready other → other = event)
    (supported : execution ∈ ((app).roundsFrom initial scheduler background
      execution.environmentRecall.length).support)
    (untouched : ∀ entry ∈ execution.logs owner,
      ¬ entry.beforeView.application.publicView.EventReady event)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (law : PMF (graph.Action event))
    (callback : ∀ current : (app).Execution,
      current.application.config = execution.application.config →
      current.application.publicView.ownTurn? owner = some event →
      referencePolicy timeouts leaks client owner (current.logs owner)
          (current.observe (app) owner) =
        law.map (fun action => (canonicalServiceDecision timeouts) leaks owner (current.logs owner)
          (current.observe (app) owner) event action)) :
    let players := turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) client
    ((app).runUntilHorizon scheduler background
      (fun final => event ∈ final.application.config.cut.completed) horizon execution) =
      law.bind (fun action => (app).runUntilHorizon scheduler
        (Function.update background owner (fun past view =>
          if turnIndex timeouts leaks owner event past view = some 0
          then fixedOpportunity timeouts leaks bound owner event action past view
          else players owner past view))
        (fun final => event ∈ final.application.config.cut.completed) horizon execution) := by
  classical
  let players := turnPolicy timeouts leaks bound turns
    (EventGraphRuntime.firstTurnTiming graph turns) client
  let first := fun past view =>
    turnIndex timeouts leaks owner event past view = some 0
  let member := fun (action : graph.Action event) past view =>
    if first past view then fixedOpportunity timeouts leaks bound owner event action past view
      else players owner past view
  let stop := fun final : (app).Execution => event ∈ final.application.config.cut.completed
  let invariant := fun current : (app).Execution =>
    event ∉ current.application.config.cut.completed →
      current.application.config = execution.application.config
  have once : ∀ past view, first past view → ∀ before entry, before ++ [entry] <+: past →
      ¬ first before entry.beforeView := by
    intro past view selected before entry prefixed earlier
    have memberEntry : entry ∈ past := prefixed.subset (by simp)
    exact (turnIndex_first selected).2 entry memberEntry
      (turnIndex_first earlier).1
  have atFirst : ∀ remaining current,
      ((app).protocol initial horizon scheduler).Trace
        (some ⟨remaining + 1, none, current⟩) →
      invariant current → ¬ stop current →
      ∀ command ∈ (scheduler current.environmentRecall (current.observeEnvironment (app))).support,
      ∀ middle ∈ (current.environmentStep (app) command).support,
        command.actor? (app) = some owner → first (middle.logs owner) (middle.observe (app) owner) →
        players owner (middle.logs owner) (middle.observe (app) owner) =
          law.bind (fun action => member action (middle.logs owner)
            (middle.observe (app) owner)) := by
    intro remaining current _ valid unfinished command _ middle moved active firstNow
    have commandEq : command = .activate owner := by
      cases command <;> simp_all [ReactiveApplication.Command.actor?]
    subst command
    have sameApplication : middle.application = current.application := by
      rw [ReactiveApplication.Execution.activation_samples (app), PMF.support_map] at moved
      obtain ⟨_, _, rfl⟩ := moved
      rfl
    have sameConfig : middle.application.config = execution.application.config :=
      (congrArg State.config sameApplication).trans (valid unfinished)
    change turnPolicy timeouts leaks bound turns
        (EventGraphRuntime.firstTurnTiming graph turns) client owner (middle.logs owner)
          (middle.observe (app) owner) = _
    rw [turnPolicy_first owned firstNow]
    simp only [member, first, firstNow, ↓reduceIte]
    unfold referenceOpportunity fixedOpportunity
    by_cases recorded : (eventRecorded timeouts) leaks (middle.logs owner) event = true
    · simp only [recorded, ↓reduceIte, PMF.bind_const]
    · have notRecorded := Bool.eq_false_of_not_eq_true recorded
      simp only [notRecorded, Bool.false_eq_true, ↓reduceIte]
      by_cases fits : (middle.observe (app) owner).application.publicView.InclusionFitsDeadline
          timeouts bound event
      · simp only [fits, ↓reduceIte]
        have compiled := congrArg (fun responseLaw : PMF (app).Action => responseLaw.bind
          (fun response => if response.transmission = none then
            (app).silentPolicy (middle.logs owner) (middle.observe (app) owner)
          else PMF.pure response)) (callback middle sameConfig
            (turnIndex_first firstNow).1)
        exact compiled.trans (by rw [PMF.bind_map]; rfl)
      · simp only [fits, ↓reduceIte, PMF.bind_const]
  have preserved : ∀ remaining current,
      ((app).protocol initial horizon scheduler).Trace
        (some ⟨remaining + 1, none, current⟩) →
      invariant current → ¬ stop current →
      ∀ next ∈ ((app).round scheduler (Function.update background owner (players owner))
        current).support, invariant next := by
    intro remaining current _ valid unfinished next reached pending
    have same := reactive_round_config_eq_of_pending timeouts leaks scheduler _ event current next
      (fun other otherReady => unique other ((valid unfinished) ▸ otherReady)) pending reached
    exact same.trans (valid unfinished)
  obtain ⟨trace⟩ := (app).raw_trace_roundsFrom initial horizon scheduler
    background
    execution.environmentRecall.length bounded execution supported
  have clean : ∀ before entry, before ++ [entry] <+: execution.logs owner →
      ¬ first before entry.beforeView := by
    intro before entry prefixed earlier
    have memberEntry : entry ∈ execution.logs owner := prefixed.subset (by simp)
    exact untouched entry memberEntry
      (PublicView.ownTurn?_spec _ owner event (turnIndex_first earlier).1).1
  have mixed := (app).runUntil_mixture_at_first
    initial horizon scheduler background owner
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

end Vegas.EventGraphRuntime
