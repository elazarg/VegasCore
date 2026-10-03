/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingPublicRounds
import Vegas.Game.SourceServiceRecordedResolutionTraffic

/-! # Binding selection independent of its canonical private value

The physical owner's recorded turn policy is silent until its current event
completes. Foreign policies remain arbitrary. The actual public scheduler and
passive observation therefore preserve the same joint public and foreign
traffic after distinct private values of one canonical binding submission.
The stop includes expiry and finite-budget exhaustion; no inclusion fairness
or source equilibrium premise is used.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem completed_of_publicTraffic_eq
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player) (event : (graph setup).EventId)
    {left right : (application setup leaks).Execution}
    (same : (runtime setup).bindingPublicTraffic leaks owner left =
      (runtime setup).bindingPublicTraffic leaks owner right) :
    event ∈ left.application.config.cut.completed ↔
      event ∈ right.application.config.cut.completed := by
  have publics := congrArg (fun read => read.2.2.2.1) same
  dsimp only [bindingPublicTraffic] at publics
  rw [← left.application.config.history_exact event,
    ← right.application.config.history_exact event]
  change event ∈ left.application.publicView.observation.completionOrder ↔
    event ∈ right.application.publicView.observation.completionOrder
  rw [publics]

private theorem ready_after_round
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    {execution next : (application setup leaks).Execution} {event : (graph setup).EventId}
    (ready : execution.application.config.cut.Ready event)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support)
    (unfinished : event ∉ next.application.config.cut.completed) :
    next.application.config.cut.Ready event := by
  rcases round_configStep setup leaks scheduler players execution next reached with
    same | ⟨target, targetReady, action, supported⟩
  · rw [same]
    exact ready
  · rw [execution.application.config.step_cut target targetReady action
      next.application.config supported] at unfinished ⊢
    apply ready.after_complete targetReady
    intro equal
    exact unfinished ((EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl equal))

/-- Once its current event is recorded, the actual turn policy is silent until
that event completes, for every timing lottery and every foreign policy. -/
theorem sourceServiceTurnPolicy_runUntil_owner_silent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (count : Nat) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true) :
    (application setup leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      (application setup leaks).runUntil scheduler
        (Function.update players owner (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  let app := application setup leaks
  let invariant := fun current : app.Execution =>
    (current.application.config.cut.Ready event ∨
      event ∈ current.application.config.cut.completed) ∧
      (runtime setup).eventRecorded leaks (current.recall owner) event = true
  have readyOf (current : app.Execution) (holds : invariant current)
      (running : event ∉ current.application.config.cut.completed) :
      current.application.config.cut.Ready event := holds.1.resolve_right running
  apply app.runUntil_congr_of_agree scheduler _ _ _ invariant
  · intro current holds running command _ middle moved who active
    by_cases foreign : who ≠ owner
    · simp only [Function.update_of_ne foreign]
    · have own : who = owner := not_ne_iff.mp foreign
      subst who
      rw [Function.update_self, follows]
      cases command with
      | activate actor =>
          have applicationEq := activation_application setup leaks current middle actor moved
          have recallEq := app.environmentStep_recall current middle (.activate actor) moved
          exact sourceServiceTurnPolicy_input_of_recorded setup leaks bound turns timing profile
            middle owner event (by rw [applicationEq]; exact readyOf current holds running)
            owned (by rw [recallEq]; exact holds.2) owner
      | «include» _ | application _ | wait => cases active
  · intro current holds running next reached
    have currentReady := readyOf current holds running
    refine ⟨?_, ?_⟩
    · by_cases finished : event ∈ next.application.config.cut.completed
      · exact Or.inr finished
      · exact Or.inl (ready_after_round setup leaks scheduler players currentReady reached finished)
    · obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
      have middleRecorded : (runtime setup).eventRecorded leaks (middle.recall owner) event =
          true := by
        rw [app.environmentStep_recall current middle command moved]
        exact holds.2
      rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, _, rfl⟩
      · exact middleRecorded
      · exact (runtime setup).eventRecorded_respond_of_recorded leaks middle responder owner
          response event middleRecorded
  · exact ⟨Or.inl ready, recorded⟩

private theorem public_runUntil
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (owner : Player) (left right : (application setup leaks).Execution)
    (same : (runtime setup).bindingPublicTraffic leaks owner left =
      (runtime setup).bindingPublicTraffic leaks owner right)
    (event : (graph setup).EventId) (ready : left.application.config.cut.Ready event)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (count : Nat) :
    ((application setup leaks).runUntil scheduler
        (Function.update players owner (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count left).map
          ((runtime setup).bindingPublicTraffic leaks owner) =
      ((application setup leaks).runUntil scheduler
        (Function.update players owner (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count right).map
          ((runtime setup).bindingPublicTraffic leaks owner) := by
  let app := application setup leaks
  induction count generalizing left right with
  | zero =>
      simpa only [ReactiveApplication.runUntil, PMF.pure_map] using congrArg PMF.pure same
  | succ count ih =>
      have leftRunning : event ∉ left.application.config.cut.completed := ready.1
      have rightRunning : event ∉ right.application.config.cut.completed := by
        intro completed
        exact leftRunning
          ((completed_of_publicTraffic_eq setup leaks owner event same).mpr completed)
      have rounds := (runtime setup).bindingPublicTraffic_round leaks scheduler players owner
        left right same event payload outputEq codeEq node (soleReady_of_ready setup _ ready)
      simp only [ReactiveApplication.runUntil, leftRunning, rightRunning, ↓reduceIte,
        PMF.map_bind]
      apply bind_eq_of_map_eq _ _ _ _ rounds
      intro first firstMove second _secondMove nextSame
      by_cases finished : event ∈ first.application.config.cut.completed
      · have rightFinished := (completed_of_publicTraffic_eq setup leaks owner event nextSame).mp
          finished
        rw [app.runUntil_of_stop scheduler _ _ count first finished,
          app.runUntil_of_stop scheduler _ _ count second rightFinished]
        simpa only [PMF.pure_map] using congrArg PMF.pure nextSame
      · exact ih first second nextSame
          (ready_after_round setup leaks scheduler _ ready firstMove finished)

/-- The actual recorded turn policy preserves public selection and every
foreign input jointly through binding completion. Foreign policies may be raw. -/
theorem sourceServiceTurnPolicy_recorded_binding_public_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (horizon : Nat) (left right : (application setup leaks).Execution)
    (same : (runtime setup).bindingPublicTraffic leaks owner left =
      (runtime setup).bindingPublicTraffic leaks owner right)
    (event : (graph setup).EventId) (ready : left.application.config.cut.Ready event)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (leftRecorded : (runtime setup).eventRecorded leaks (left.recall owner) event = true)
    (rightRecorded : (runtime setup).eventRecorded leaks (right.recall owner) event = true) :
    ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon left).map
          ((runtime setup).bindingPublicTraffic leaks owner) =
      ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon right).map
          ((runtime setup).bindingPublicTraffic leaks owner) := by
  have publics := congrArg (fun read => read.2.2.2.1) same
  have recalled := congrArg (fun read => read.2.2.1) same
  dsimp only [bindingPublicTraffic] at publics recalled
  have rightReady : right.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← publics, State.publicView_eventReady]
    exact ready
  have owned := nodeView_bind_actor outputEq codeEq
  unfold ReactiveApplication.runUntilHorizon
  rw [← recalled,
    sourceServiceTurnPolicy_runUntil_owner_silent setup leaks scheduler players bound turns timing
      profile owner follows _ left event ready owned leftRecorded,
    sourceServiceTurnPolicy_runUntil_owner_silent setup leaks scheduler players bound turns timing
      profile owner follows _ right event rightReady owned rightRecorded]
  exact public_runUntil setup leaks scheduler players owner left right same event ready payload
    outputEq codeEq node _

/-- The actual public selection, misses and foreign traffic through the
binding stop do not depend on this packet's typed private value. -/
theorem sourceService_binding_selection_independent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (horizon : Nat) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution.respond (application setup leaks) owner
          ((runtime setup).reactiveBinding leaks owner event payload first serial))).map
          ((runtime setup).bindingPublicTraffic leaks owner) =
      ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution.respond (application setup leaks) owner
          ((runtime setup).reactiveBinding leaks owner event payload second serial))).map
          ((runtime setup).bindingPublicTraffic leaks owner) := by
  let app := application setup leaks
  let firstResponse := (runtime setup).reactiveBinding leaks owner event payload first serial
  let afterFirst := execution.respond app owner firstResponse
  have afterReady : afterFirst.application.config.cut.Ready event := by
    dsimp only [afterFirst]
    rw [((runtime setup).reactive_respond_application leaks execution owner _).1]
    exact ready
  apply sourceServiceTurnPolicy_recorded_binding_public_law setup leaks scheduler players bound
    turns timing profile owner follows horizon _ _
    ((runtime setup).bindingPublicTraffic_binding_response leaks owner execution execution rfl
      event payload first second serial) event afterReady payload outputEq codeEq node
  · exact (runtime setup).eventRecorded_respond leaks execution owner _ event rfl
  · exact (runtime setup).eventRecorded_respond leaks execution owner _ event rfl

/-- The same correlated prefix parameter is retained jointly with actual
public selection and every foreign input. The two values may depend on the
same prefix draw; no independence of the initial parameter is assumed. -/
theorem sourceService_binding_selection_joint_independent
    {Seed Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (horizon : Nat) (prior : PMF Seed) (parameter : Seed → Parameter)
    (execution : Seed → (application setup leaks).Execution)
    (event : (graph setup).EventId)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (first second : Seed → PublicationResult (L.Val payload)) (serial : Seed → Nat) :
    (prior.bind fun seed => ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon
      ((execution seed).respond (application setup leaks) owner
        ((runtime setup).reactiveBinding leaks owner event payload
          (first seed) (serial seed)))).map fun final =>
            (parameter seed, (runtime setup).bindingPublicTraffic leaks owner final)) =
    (prior.bind fun seed => ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon
      ((execution seed).respond (application setup leaks) owner
        ((runtime setup).reactiveBinding leaks owner event payload
          (second seed) (serial seed)))).map fun final =>
            (parameter seed, (runtime setup).bindingPublicTraffic leaks owner final)) := by
  apply bind_congr_on_support prior
  intro seed supported
  have law := sourceService_binding_selection_independent setup leaks scheduler players bound
    turns timing profile owner follows horizon (execution seed) event (ready seed supported)
    payload outputEq codeEq node (first seed) (second seed) (serial seed)
  simpa only [PMF.map_comp, Function.comp_def] using
    congrArg (fun law => law.map (fun traffic => (parameter seed, traffic))) law

end Vegas
