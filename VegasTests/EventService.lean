/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.EventService
import Vegas.Pending.EventPolicies

/-! # Event service regressions

The shared pending-message service schedules two independent binding events in
both orders. These tests cover epoch plans, deadline feasibility, the reserved
selector, and prescribed binding staging. Successful and failed choices use
the same public packet and store their exact selected result on inclusion.
-/

namespace VegasTests.EventService

open GameTheory.Math.Probability Interaction Vegas

noncomputable section

private abbrev pairOrder : EventOrder where
  eventCount := 2
  predecessors _ := ∅
  predecessor_lt := by simp

private abbrev pairInputs : Fin 0 → Vegas.EventGraph.EventField Bool simpleExpr := Fin.elim0

private abbrev pairOutputs : Fin 2 → Vegas.EventGraph.EventField Bool simpleExpr :=
  fun event => .binding (event.val == 1) .bool

private abbrev pairLayout := Vegas.EventGraph.fieldLayout pairInputs pairOutputs

private abbrev pairGraph : Vegas.EventGraph Bool simpleExpr where
  inputCount := 0
  order := pairOrder
  inputLayout := pairInputs
  outputLayout := pairOutputs
  nodes event := Vegas.EventGraph.EventCode.bind (layout := pairLayout)
    (event.val == 1) .bool
  reads_available := by
    intro event field member
    exact False.elim (Finset.notMem_empty field member)
  payoffs := []

private def runtime : EventGraphRuntime pairGraph where
  deadline _ := 2

private def firstPacket : Message Bool (EventGraphRuntime.Payload pairGraph) :=
  ⟨(false, 0), .commitment 0 (false, .prepared 0)⟩

private def unrelatedLater : Message Bool (EventGraphRuntime.Payload pairGraph) :=
  ⟨(false, 1), .commitment 1 (false, .prepared 1)⟩

private def firstPending : MessagePool Bool (EventGraphRuntime.Payload pairGraph) :=
  { MessagePool.empty Bool (EventGraphRuntime.Payload pairGraph) with
    pending := [firstPacket] }

/-- A newer packet by the same author but addressed to another event does not
consume the first event's reserved inclusion. -/
example :
    EventGraphRuntime.latestEventSubmission?
        { firstPending with pending := firstPending.pending ++ [unrelatedLater] }
        0 false =
      some firstPacket := by
  rw [EventGraphRuntime.latestEventSubmission?_append_nonmatching]
  · rfl
  · intro matching
    have addresses := matching.2
    change some (1 : Fin 2) = some 0 at addresses
    have same : (1 : Fin 2) = 0 := Option.some.inj addresses
    omega

/-- The shared epoch planner offers both independent bindings in increasing
order before the single clock tick and expiry pass. -/
example : EventGraphRuntime.epochPlan
    (EventGraphRuntime.ServiceOrder.increasing pairGraph) [] 0 =
    [.grant 0, .player false, .player false, .player false,
     .includeLatest 0 false, .sample 0,
     .grant 1, .player true, .player true, .player true,
     .includeLatest 1 true, .sample 1,
     .tick, .expire 0, .expire 1] := rfl

/-- The decreasing public service order offers the same events in the other
order without changing the expiry pass. -/
example : EventGraphRuntime.epochPlan
    (EventGraphRuntime.ServiceOrder.decreasing pairGraph) [] 0 =
    [.grant 1, .player true, .player true, .player true,
     .includeLatest 1 true, .sample 1,
     .grant 0, .player false, .player false, .player false,
     .includeLatest 0 false, .sample 0,
     .tick, .expire 0, .expire 1] := rfl

/-- The concrete deadline meets the service contract's one-following-epoch
grace requirement. -/
example : runtime.ServiceFeasible := by
  intro event
  rfl

private def fixedPolicy (choice : PublicationResult Bool) : pairGraph.BehavioralPolicy false :=
  fun _ _ _ => FinDist.pure choice

private def granted : EventGraphRuntime.State pairGraph :=
  { EventGraphRuntime.State.initial (graph := pairGraph) (fun input => nomatch input) with
    serviceGrant := some 0 }

private def observed (state : EventGraphRuntime.State pairGraph) : runtime.application.View :=
  Interaction.MessageApplication.State.observe runtime.application
    (Interaction.MessageApplication.State.initial runtime.application state) false

private def remembered (choice : PublicationResult Bool) : EventGraphRuntime.State pairGraph :=
  EventGraphRuntime.privateStep granted false (.remember 0 choice)

private def firstEntry (choice : PublicationResult Bool) : runtime.application.PlayerEntry :=
  ⟨observed granted, .privateCommand (.remember 0 choice)⟩

private def preparation (choice : PublicationResult Bool) :
    EventGraphRuntime.PrivateCommand pairGraph :=
  match choice with
  | .failure => .remember 0 choice
  | .success value => .prepare 0 ⟨.bool, value⟩

private def staged (choice : PublicationResult Bool) : EventGraphRuntime.State pairGraph :=
  EventGraphRuntime.privateStep (remembered choice) false (preparation choice)

private def stagedHistory (choice : PublicationResult Bool) :
    List runtime.application.PlayerEntry :=
  [firstEntry choice,
   ⟨observed (remembered choice), .privateCommand (preparation choice)⟩]

/-- Both payload success and binding failure first use an entirely private
sampling operation. Neither emits a packet in the first owner opportunity. -/
example (choice : PublicationResult Bool) :
    runtime.compilePlayerPolicy false (fixedPolicy choice) [] (observed granted) =
      FinDist.pure (.privateCommand (.remember 0 choice)) := by
  have actor : pairGraph.actor? 0 = some false := rfl
  simp [EventGraphRuntime.compilePlayerPolicy, EventGraphRuntime.submittedAt,
    EventGraphRuntime.stagingCount, observed, granted,
    Interaction.MessageApplication.State.observe,
    Interaction.MessageApplication.State.initial,
    EventGraphRuntime.application, EventGraphRuntime.State.playerView,
    EventGraphRuntime.State.publicView, EventGraphRuntime.PublicView.EventReady,
    Vegas.EventGraph.publicObserve, Vegas.EventGraph.Config.initial,
    EventGraphRuntime.State.initial, EventGraphRuntime.nodeView,
    Vegas.EventGraph.normalizePolicy, fixedPolicy, actor]

/-- Uniform private staging leaves the same public application state for
every selected value, including failure. -/
example (left right : PublicationResult Bool) :
    (staged left).publicView = (staged right).publicView := by
  cases left <;> cases right <;> rfl

/-- The common packet's private candidate meaning is exactly the chosen
binding action, including genuine failure rather than an in-domain default. -/
private theorem staged_result (choice : PublicationResult Bool) :
    (staged choice).bindingResult (false, .prepared 0) .bool = choice := by
  cases choice <;> rfl

/-- The third opportunity publishes the same opaque handle for every
selected value. Failure is not a cleartext alternative to commitment. -/
example (choice : PublicationResult Bool) :
    runtime.compilePlayerPolicy false (fixedPolicy choice)
        (stagedHistory choice) (observed (staged choice)) =
      FinDist.pure (.submit (.commitment 0 (false, .prepared 0))) := by
  have actor : pairGraph.actor? 0 = some false := rfl
  cases choice <;>
    simp [EventGraphRuntime.compilePlayerPolicy, EventGraphRuntime.submittedAt,
      EventGraphRuntime.stagingCount, EventGraphRuntime.stagesEvent,
      EventGraphRuntime.eventSlot, stagedHistory, firstEntry, preparation,
      staged, remembered, observed, granted,
      Interaction.MessageApplication.State.observe,
      Interaction.MessageApplication.State.initial,
      EventGraphRuntime.application, EventGraphRuntime.privateStep,
      EventGraphRuntime.State.playerView, EventGraphRuntime.State.publicView,
      EventGraphRuntime.PublicView.EventReady, Vegas.EventGraph.publicObserve,
      Vegas.EventGraph.Config.initial, EventGraphRuntime.State.initial,
      EventGraphRuntime.nodeView, actor, Function.update]

/-- Inclusion of the staged opaque packet really stores the selected value;
the common failure packet is accepted as a failed binding. -/
example (choice : PublicationResult Bool) :
    (EventGraphRuntime.handle runtime (staged choice)
      ⟨(false, 0), .commitment 0 (false, .prepared 0)⟩).map
        (fun state => state.config.outputs 0) = some (some choice) := by
  have ready : (staged choice).config.cut.Ready 0 := by
    cases choice <;> change (EventOrder.Cut.empty pairOrder).Ready 0 <;> decide
  have timely : (staged choice).WithinDeadline runtime 0 := by
    cases choice <;> change 0 < 2 <;> decide
  have vacant : (staged choice).accepted (.inr 0) = none := by
    cases choice <;> rfl
  have unused : (staged choice).HandleUnused (false, .prepared 0) := by
    intro field
    cases field with
    | inl input => nomatch input
    | inr event =>
        cases choice <;>
          change (none : Option (EventGraphRuntime.Handle pairGraph)) ≠
            some (false, .prepared 0)
        all_goals simp
  rw [EventGraphRuntime.handle_commitment_eq runtime (staged choice) (false, 0)
    0 (false, .prepared 0) false .bool rfl rfl rfl ready timely rfl rfl vacant unused]
  simpa [EventGraphRuntime.State.complete, staged_result] using
    congrArg (fun result => some (some result)) (staged_result choice)

end

end VegasTests.EventService
