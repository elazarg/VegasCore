/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationPolicies
import Interaction.SealedCandidateResolution
import GameTheoryExtensions.Math.Probability.SequentialDecisionObservation

/-! # Two-site logical-commitment policy experiment

An unchanged second binding publishes an authenticated opening before the focal
owner's opening decision.  The finite runner law retains the public event
prefix at that decision together with focal publication and timeout
attribution. Sequential conditioning gives logical focal policies using public
events, delivered claims without message identifiers, and private action recall.
The environment is scripted and the two decision kernels are the only arbitrary
focal choices. This is a bounded two-site test, not a graph-wide refinement.
-/

noncomputable section

namespace InteractionTests.LogicalCommitmentCrossSite

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

private def runtime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩, ⟨.reveal false 0, [0]⟩,
      ⟨.commit true, []⟩, ⟨.reveal true 2, [2]⟩]⟩, none, 1⟩

private abbrev app := runtime.candidateApplication

private def initial : app.State := State.initial app runtime.candidateInitial

private def initialExecution : app.PolicyExecution :=
  PolicyExecution.initial app initial

private def commitment (node : Nat) (handle : Bool × Nat) : app.Payload :=
  .commitment node handle

private def opening (node : Nat) (handle : Bool × Nat) (value : Bool) : app.Payload :=
  .opening node handle (some value)

private def recalledValue? : List app.PlayerEntry → Option Bool
  | ⟨_, .privateCommand ⟨(_, some value)⟩⟩ :: _ => some value
  | _ => none

/-- The focal wrapper has two arbitrary kernels.  Its commitment command is
fixed and its opening decision uses its actual private-command recall. -/
private def focalPolicy (info : Fin 2)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 → Bool → app.View → FinDist (Option Bool)) : app.PlayerPolicy :=
  fun history view => match history with
  | [] => (first info).map fun value => .privateCommand ⟨(0, some value)⟩
  | [_] => FinDist.pure (.submit (commitment 0 (false, 0)))
  | _ => match recalledValue? history with
      | some value => (second info value view).map fun response => match response with
          | some claimed => .submit (opening 1 (false, 0) claimed)
          | none => .wait
      | none => FinDist.pure .wait

/-- The other binding's only random choice is fixed before either focal
kernel.  Later commands recover it solely from that owner's command history. -/
private def otherPolicy (other : FinDist Bool) : app.PlayerPolicy :=
  fun history _ => match history with
  | [] => other.map fun value => .privateCommand ⟨(0, some value)⟩
  | [_] => FinDist.pure (.submit (commitment 2 (true, 0)))
  | _ => FinDist.pure <| match recalledValue? history with
      | some value => .submit (opening 3 (true, 0) value)
      | none => .wait

private def players (info : Fin 2) (other : FinDist Bool)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 → Bool → app.View → FinDist (Option Bool)) :
    Bool → app.PlayerPolicy
  | false => focalPolicy info first second
  | true => otherPolicy other

/-- Inclusion mode is fixed independently of the focal kernels. -/
private def environment (includeOtherOpening : Bool) : app.EnvironmentPolicy :=
  fun history _ => FinDist.pure <| match history.length with
  | 0 => .include (false, 0)
  | 1 => .include (true, 0)
  | 2 => .deliver false (true, 1)
  | 3 => if includeOtherOpening then .include (true, 1) else .wait
  | 4 => .include (false, 1)
  | _ => .application ⟨()⟩

private def schedule : List (@Invocation Bool) :=
  [.player false, .player false, .environment,
    .player true, .player true, .environment, .player true,
    .environment, .environment, .player false, .environment, .environment]

private def focalSchedule : List (@Invocation Bool) :=
  [.player false, .player false, .environment]

private def otherSchedule : List (@Invocation Bool) :=
  [.player true, .player true, .environment, .player true, .environment, .environment]

private def finishSchedule : List (@Invocation Bool) :=
  [.player false, .environment, .environment]

private def registered (who : Bool) (value : Bool) (state : app.State) : app.State :=
  { state with application := app.privateStep state.application who ⟨(0, some value)⟩ }

private def submit (who : Bool) (payload : app.Payload) (state : app.State) : app.State :=
  { state with pool := (state.pool.submit who payload).2 }

private def focalCommitted (focal : Bool) : app.State :=
  app.includePending
    (submit false (commitment 0 (false, 0)) (registered false focal initial)) (false, 0)

private def focalRegistered (focal : Bool) : app.State :=
  registered false focal initial

private def focalSubmitted (focal : Bool) : app.State :=
  submit false (commitment 0 (false, 0)) (focalRegistered focal)

private def otherCommitted (focal other : Bool) : app.State :=
  app.includePending
    (submit true (commitment 2 (true, 0))
      (registered true other (focalCommitted focal))) (true, 0)

private def otherRegistered (focal other : Bool) : app.State :=
  registered true other (focalCommitted focal)

private def otherCommitmentSubmitted (focal other : Bool) : app.State :=
  submit true (commitment 2 (true, 0)) (otherRegistered focal other)

private def otherSubmitted (focal other : Bool) : app.State :=
  submit true (opening 3 (true, 0) other) (otherCommitted focal other)

private def otherDelivered (focal other : Bool) : app.State :=
  let state := otherSubmitted focal other
  { state with pool := (state.pool.deliver false (true, 1)).state }

private def beforeFocalDecision (includeOtherOpening : Bool)
    (focal other : Bool) : app.State :=
  if includeOtherOpening then
    app.includePending (otherDelivered focal other) (true, 1)
  else otherDelivered focal other

private def focalEntries (focal : Bool) : List app.PlayerEntry :=
  [⟨State.observe app initial false, .privateCommand ⟨(0, some focal)⟩⟩,
    ⟨State.observe app (focalRegistered focal) false,
      .submit (commitment 0 (false, 0))⟩]

private def afterFocalCommitment (focal : Bool) : app.PolicyExecution :=
  { native := focalCommitted focal
    principalHistory := fun who => if who = false then focalEntries focal else []
    environmentHistory :=
      [⟨State.environmentView app (focalSubmitted focal), .include (false, 0)⟩]
    nativeTrace :=
      [.privateCommand false ⟨(0, some focal)⟩,
        .submit false (commitment 0 (false, 0)), .include (false, 0)] }

private def otherEntries (focal other : Bool) : List app.PlayerEntry :=
  [⟨State.observe app (focalCommitted focal) true,
      .privateCommand ⟨(0, some other)⟩⟩,
    ⟨State.observe app (otherRegistered focal other) true,
      .submit (commitment 2 (true, 0))⟩,
    ⟨State.observe app (otherCommitted focal other) true,
      .submit (opening 3 (true, 0) other)⟩]

private def beforeFocalExecution (includeOtherOpening : Bool)
    (focal other : Bool) : app.PolicyExecution :=
  { native := beforeFocalDecision includeOtherOpening focal other
    principalHistory := fun who =>
      if who = false then focalEntries focal
      else if who = true then otherEntries focal other else []
    environmentHistory :=
      (afterFocalCommitment focal).environmentHistory ++
        [⟨State.environmentView app (otherCommitmentSubmitted focal other),
            .include (true, 0)⟩,
          ⟨State.environmentView app (otherSubmitted focal other),
            .deliver false (true, 1)⟩,
          ⟨State.environmentView app (otherDelivered focal other),
            if includeOtherOpening then .include (true, 1) else .wait⟩]
    nativeTrace := (afterFocalCommitment focal).nativeTrace ++
      [.privateCommand true ⟨(0, some other)⟩,
        .submit true (commitment 2 (true, 0)), .include (true, 0),
        .submit true (opening 3 (true, 0) other), .deliver false (true, 1)] ++
      if includeOtherOpening then [.include (true, 1)] else [] }

private theorem beforeFocalExecution_native (included focal other : Bool) :
    (beforeFocalExecution included focal other).native =
      beforeFocalDecision included focal other := rfl

private theorem beforeFocalExecution_focalHistory (included focal other : Bool) :
    (beforeFocalExecution included focal other).principalHistory false = focalEntries focal := rfl

private theorem include_absent_response (included focal other : Bool) :
    app.includePending (beforeFocalDecision included focal other) (false, 1) =
      beforeFocalDecision included focal other := by
  cases included <;> cases focal <;> cases other <;> rfl

private theorem beforeFocalExecution_environmentHistory_length
    (includeOtherOpening focal other : Bool) :
    (beforeFocalExecution includeOtherOpening focal other).environmentHistory.length = 4 := by
  cases includeOtherOpening <;> rfl

private def afterFocalResponse (includeOtherOpening : Bool)
    (focal other : Bool) : Option Bool → app.State
  | none => beforeFocalDecision includeOtherOpening focal other
  | some claimed => app.includePending
      (submit false (opening 1 (false, 0) claimed)
        (beforeFocalDecision includeOtherOpening focal other)) (false, 1)

private def settled (includeOtherOpening : Bool)
    (focal other : Bool) (response : Option Bool) : app.State :=
  let state := afterFocalResponse includeOtherOpening focal other response
  { state with application := runtime.tick state.application }

private abbrev PublicPrefix := List (SealedProgram.Event Bool (Option Bool))

private structure StoppedOutcome where
  publicPrefix : PublicPrefix
  published : Option (Option Bool)
  timedOut : Bool

private def statePrefix (state : app.State) : PublicPrefix :=
  state.application.visible.events

private def expected (includeOtherOpening : Bool) (focal other : Bool)
    (response : Option Bool) : StoppedOutcome :=
  let before := beforeFocalDecision includeOtherOpening focal other
  let final := settled includeOtherOpening focal other response
  ⟨statePrefix before, final.application.visible.published? 1,
    final.application.visible.timeouts.contains 1⟩

private def eventSite : SealedProgram.Event Bool (Option Bool) → Nat
  | .accepted node _ | .opened node _ => node

private def stateStoppedOutcome (state : app.State) : StoppedOutcome :=
  ⟨state.application.visible.events.takeWhile fun event => eventSite event != 1,
    state.application.visible.published? 1,
    state.application.visible.timeouts.contains 1⟩

private def stoppedOutcome (execution : app.PolicyExecution) : StoppedOutcome :=
  stateStoppedOutcome execution.native

/-- In this fixed suffix, recovering the event prefix before the first focal
settlement event gives exactly the public events present at the focal decision.
This is a property of the fixture's event order, not a general equivalence
between terminal and decision prefixes. -/
private theorem settled_stoppedOutcome (includeOtherOpening : Bool)
    (focal other : Bool) (response : Option Bool) :
    stateStoppedOutcome (settled includeOtherOpening focal other response) =
      expected includeOtherOpening focal other response := by
  cases includeOtherOpening <;> cases focal <;> cases other <;> cases response with
  | none => rfl
  | some response => cases response <;> rfl

private theorem environmentStep_clock (state : app.Application) :
    app.environmentStep state ⟨()⟩ = FinDist.pure (runtime.tick state) := rfl

private theorem focalSchedule_run
    (info : Fin 2) (other : FinDist Bool) (includeOtherOpening : Bool)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 → Bool → app.View → FinDist (Option Bool)) :
    app.runPolicies (players info other first second) (environment includeOtherOpening)
      focalSchedule initialExecution = (first info).map afterFocalCommitment := by
  simp only [focalSchedule, MessageApplication.runPolicies, MessageApplication.invoke,
    players, focalPolicy, environment, initialExecution,
    MessageApplication.PolicyExecution.initial, MessageApplication.playerStep,
    MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.bind_map, FinDist.bind_bind, FinDist.pure_bind, FinDist.bind_pure,
    List.length_nil, if_true, List.nil_append]
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro focal _
  congr 1
  unfold afterFocalCommitment focalEntries
  congr 1
  funext who
  cases who <;> rfl

private theorem otherSchedule_run
    (info : Fin 2) (other : FinDist Bool) (includeOtherOpening : Bool)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 → Bool → app.View → FinDist (Option Bool))
    (focal : Bool) :
    app.runPolicies (players info other first second) (environment includeOtherOpening)
      otherSchedule (afterFocalCommitment focal) =
        other.map (beforeFocalExecution includeOtherOpening focal) := by
  cases includeOtherOpening <;>
    simp only [otherSchedule, MessageApplication.runPolicies, MessageApplication.invoke,
      players, otherPolicy, environment, recalledValue?, afterFocalCommitment,
      MessageApplication.playerStep,
      MessageApplication.environmentPolicyStep, MessageApplication.advance,
      MessageApplication.PlayerCommand.toAction,
      MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
      FinDist.bind_map, FinDist.bind_bind, FinDist.pure_bind, FinDist.bind_pure,
      List.length_nil, List.length_cons, Bool.true_eq_false, Bool.false_eq_true, if_true, if_false,
      List.nil_append, List.cons_append, List.length_append, Nat.reduceAdd] <;>
    rw [FinDist.map_eq_bind]
  all_goals
    apply FinDist.bind_congr
    intro otherValue _
    apply congrArg FinDist.pure
    dsimp only [beforeFocalExecution, beforeFocalDecision, otherDelivered, otherSubmitted,
      otherCommitted, otherEntries, otherRegistered, otherCommitmentSubmitted,
      registered, submit, afterFocalCommitment]
    congr 1
    funext who
    cases who <;> rfl

private theorem finishSchedule_run
    (info : Fin 2) (other : FinDist Bool) (includeOtherOpening : Bool)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 → Bool → app.View → FinDist (Option Bool))
    (focal otherValue : Bool) :
    (app.runPolicies (players info other first second) (environment includeOtherOpening)
      finishSchedule (beforeFocalExecution includeOtherOpening focal otherValue)).map
        stoppedOutcome =
      (second info focal
        (State.observe app
          (beforeFocalDecision includeOtherOpening focal otherValue) false)).bind
        fun response => FinDist.pure
          (expected includeOtherOpening focal otherValue response) := by
  simp only [finishSchedule, MessageApplication.runPolicies, MessageApplication.invoke,
      players, focalPolicy, environment, recalledValue?,
      beforeFocalExecution_native, beforeFocalExecution_focalHistory,
      focalEntries, MessageApplication.playerStep,
      beforeFocalExecution_environmentHistory_length,
      MessageApplication.environmentPolicyStep, MessageApplication.advance,
      MessageApplication.PlayerCommand.toAction,
      MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
      FinDist.bind_map, FinDist.map_bind, FinDist.pure_bind, FinDist.bind_pure,
      FinDist.bind_bind, FinDist.map_pure, List.nil_append,
      List.length_nil, List.length_cons,
      List.length_append, List.cons_append, Nat.reduceAdd]
  apply FinDist.bind_congr
  intro response _
  cases response with
  | none =>
      simp only [FinDist.pure_bind, environmentStep_clock, include_absent_response]
      simpa only [settled, afterFocalResponse, stoppedOutcome] using
        congrArg FinDist.pure
          (settled_stoppedOutcome includeOtherOpening focal otherValue none)
  | some claimed =>
      simp only [FinDist.pure_bind, environmentStep_clock]
      simpa only [settled, afterFocalResponse, submit, stoppedOutcome] using
        congrArg FinDist.pure
          (settled_stoppedOutcome includeOtherOpening focal otherValue (some claimed))

/-- For arbitrary focal choice kernels, the actual policy runner factors
through the sampled other-binding value, the actual cross-site owner view and
the stopped public prefix.  The other policy, environment and schedule do not
depend on either focal kernel. -/
theorem runPolicies_crossSite_stoppedOutcome
    (info : Fin 2) (other : FinDist Bool) (includeOtherOpening : Bool)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 → Bool → app.View → FinDist (Option Bool)) :
    (app.runPolicies (players info other first second)
      (environment includeOtherOpening) schedule initialExecution).map stoppedOutcome =
    (first info).bind fun focal => other.bind fun otherValue =>
      (second info focal
        (State.observe app
          (beforeFocalDecision includeOtherOpening focal otherValue) false)).bind
        fun response => FinDist.pure
          (expected includeOtherOpening focal otherValue response) := by
  rw [show schedule = focalSchedule ++ (otherSchedule ++ finishSchedule) by rfl,
    app.runPolicies_append, focalSchedule_run]
  simp only [FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro focal _
  rw [app.runPolicies_append, otherSchedule_run]
  simp only [FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro otherValue _
  exact finishSchedule_run info other includeOtherOpening first second focal otherValue

private abbrev LogicalObservation := PublicPrefix × List app.Payload

/-- Retain public events and delivered claims, but no envelope identifiers,
clock, receipts, or unrelated native state. Private action recall is separate. -/
private def observeLogical (view : app.View) : LogicalObservation :=
  (view.application.events, view.messages.inbox.map fun envelope => envelope.payload)

private def logicalNext (other : FinDist Bool) (included : Bool)
    (_initial : Unit) (_focal : Bool) : FinDist LogicalObservation :=
  other.map fun value =>
    observeLogical (State.observe app (beforeFocalDecision included false value) false)

private def logicalFinish (history : Unit × Bool × LogicalObservation)
    (response : Option Bool) : FinDist StoppedOutcome :=
  FinDist.pure ⟨history.2.2.1, some (if response = some history.2.1 then response else none),
    decide (response ≠ some history.2.1)⟩

private theorem logical_observation_hides_focal (included focal other : Bool) :
    observeLogical (State.observe app (beforeFocalDecision included focal other) false) =
      observeLogical (State.observe app (beforeFocalDecision included false other) false) := by
  cases included <;> cases focal <;> cases other <;> rfl

private theorem expected_logicalFinish (included focal other : Bool) (response : Option Bool) :
    FinDist.pure (expected included focal other response) =
      logicalFinish ((), focal,
        observeLogical (State.observe app (beforeFocalDecision included focal other) false))
        response := by
  cases included <;> cases focal <;> cases other <;> cases response with
  | none => rfl
  | some claimed => cases claimed <;> rfl

/-- In this fixed two-site context, every pair of randomized focal kernels
has logical kernels with the same joint opening-decision-prefix and settlement
law. The second logical kernel retains the first action and cross-site claims;
it receives neither the full native view nor auxiliary preparation metadata.
Both surrounding policies and both logical continuation kernels remain fixed. -/
theorem runPolicies_crossSite_logical_law
    (metadata : FinDist (Fin 2)) (other : FinDist Bool) (included : Bool)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 → Bool → app.View → FinDist (Option Bool)) :
    ∃ logicalFirst : Unit → FinDist Bool,
      ∃ logicalSecond : Unit × Bool × LogicalObservation → FinDist (Option Bool),
        (metadata.bind fun info =>
          (app.runPolicies (players info other first second) (environment included)
            schedule initialExecution).map stoppedOutcome) =
        ((metadata.map fun _ => ()).bind fun start =>
          (logicalFirst start).bind fun focal =>
            (logicalNext other included start focal).bind fun later =>
              (logicalSecond (start, focal, later)).bind
                (logicalFinish (start, focal, later))) := by
  let next : Fin 2 → Bool → FinDist app.View := fun _ focal =>
    other.map fun value => State.observe app (beforeFocalDecision included focal value) false
  let finish : Fin 2 × Bool × app.View → Option Bool → FinDist StoppedOutcome :=
    fun history response =>
      logicalFinish ((), history.2.1, observeLogical history.2.2) response
  obtain ⟨logicalFirst, logicalSecond, hlaw⟩ :=
    FinDist.exists_two_decision_policy_law metadata (fun _ => ()) observeLogical next
      (logicalNext other included)
      (by
        intro info _ focal
        simp only [next, logicalNext, FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind]
        apply FinDist.bind_congr
        intro value _
        exact congrArg FinDist.pure (logical_observation_hides_focal included focal value))
      finish logicalFinish (by intros; rfl) first
      (fun history => second history.1 history.2.1 history.2.2)
  refine ⟨logicalFirst, logicalSecond, ?_⟩
  rw [← hlaw]
  apply FinDist.bind_congr
  intro info _
  rw [runPolicies_crossSite_stoppedOutcome]
  simp only [next, FinDist.bind_map]
  apply FinDist.bind_congr
  intro focal _
  apply FinDist.bind_congr
  intro value _
  apply FinDist.bind_congr
  intro response _
  exact expected_logicalFinish included focal value response

end InteractionTests.LogicalCommitmentCrossSite

/-- info: 'InteractionTests.LogicalCommitmentCrossSite.runPolicies_crossSite_logical_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractionTests.LogicalCommitmentCrossSite.runPolicies_crossSite_logical_law
