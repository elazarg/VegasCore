/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceDecidedBinding
import Vegas.Game.SourceServiceFirstTurnBinding

/-! # First-turn clients with decisions drawn in advance

A first-turn client makes the source decision of each of its events at its
first turn there. Its decisions at some events may instead be fixed in advance
(`Vegas.assignedTurnPolicy`): at the first turn at such an event it transmits
the compiled commitment of the fixed action, and it behaves as the client
everywhere else.

Drawing one decision in advance changes nothing in law
(`Vegas.assignedTurnPolicy_runUntil_mixture`): if, whenever the owner's first
turn at the event comes, the source decision there is a fixed law compiled to
native responses, then the client runs as the mixture, over that law, of the
clients with the action fixed. This holds against arbitrary other players, for
every stopping rule, in every dependency mode.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- Decisions fixed in advance at some events. -/
abbrev Assignment (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode) :
    Type :=
  (event : (serviceGraph setup mode).EventId) → Option ((serviceGraph setup mode).Action event)

/-- The first-turn client of `owner` whose decisions at the assigned events
are the assigned actions. -/
def assignedTurnPolicy (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (assignment : Assignment setup mode) :
    (serviceApplication setup mode deadline leaks).Policy := fun past view =>
  match view.application.publicView.ownTurn? owner with
  | some event =>
      match assignment event with
      | some action => decidedTurnPolicy setup leaks bound owner event action past view
      | none => serviceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) profile owner past view
  | none => serviceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) profile owner past view

/-- With nothing assigned, the assigned client is the first-turn client. -/
theorem assignedTurnPolicy_empty (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (owner : Player) :
    assignedTurnPolicy (deadline := deadline) (leaks := leaks) bound turns profile owner
        (fun _ => none) =
      serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile owner := by
  funext past view
  unfold assignedTurnPolicy
  split <;> rfl

theorem assignedTurnPolicy_assigned {bound : (serviceGraph setup mode).EventId → Nat}
    {turns : Nat} {profile : BehavioralProfile setup.program} {owner : Player}
    {assignment : Assignment setup mode}
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    {event : (serviceGraph setup mode).EventId} {action : (serviceGraph setup mode).Action event}
    (turn : view.application.publicView.ownTurn? owner = some event)
    (assigned : assignment event = some action) :
    assignedTurnPolicy bound turns profile owner assignment past view =
      decidedTurnPolicy setup leaks bound owner event action past view := by
  simp only [assignedTurnPolicy, turn, assigned]

theorem assignedTurnPolicy_unassigned {bound : (serviceGraph setup mode).EventId → Nat}
    {turns : Nat} {profile : BehavioralProfile setup.program} {owner : Player}
    {assignment : Assignment setup mode}
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    {event : (serviceGraph setup mode).EventId}
    (turn : view.application.publicView.ownTurn? owner = some event)
    (unassigned : assignment event = none) :
    assignedTurnPolicy bound turns profile owner assignment past view =
      serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile owner past view := by
  simp only [assignedTurnPolicy, turn, unassigned]

/-- Assigning an event changes no response away from the owner's turns there. -/
theorem assignedTurnPolicy_update_of_not_turn (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (profile : BehavioralProfile setup.program) (owner : Player)
    (assignment : Assignment setup mode) (event : (serviceGraph setup mode).EventId)
    (value : Option ((serviceGraph setup mode).Action event))
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (other : view.application.publicView.ownTurn? owner ≠ some event) :
    assignedTurnPolicy bound turns profile owner (Function.update assignment event value) past
        view =
      assignedTurnPolicy bound turns profile owner assignment past view := by
  unfold assignedTurnPolicy
  split
  · rename_i current turn
    have different : current ≠ event := fun same => other (by rw [turn, same])
    rw [Function.update_of_ne different]
  · rfl

/-- At its own turn at an owned event, the first-turn client is the event's
first-turn family. -/
theorem firstTurnPolicy_eq_family {bound : (serviceGraph setup mode).EventId → Nat}
    {turns : Nat} {profile : BehavioralProfile setup.program} {owner : Player}
    {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    (turn : view.application.publicView.ownTurn? owner = some event) :
    serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile owner past view =
      serviceTurnFamily setup mode deadline leaks bound profile owner event turns 0 past view := by
  let app := serviceApplication setup mode deadline leaks
  let family := serviceTurnFamily setup mode deadline leaks bound profile owner event turns
  have pin : (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).posterior past =
      PMF.pure 0 := by
    simpa only [List.nil_append] using app.policyMixture_posterior_pure_append
      (PMF.pure (0 : Fin (turns + 1))) family [] past 0 rfl
  rw [sourceServiceTurnPolicy_turn setup leaks bound turns _ profile owner past view event owned
    turn]
  change (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).policy past view = _
  rw [app.policyMixture_policy, pin, PMF.pure_bind]

/-- The assigned client submits only for its own turn. -/
theorem assignedTurnPolicy_submitsAtTurn (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (profile : BehavioralProfile setup.program) (owner : Player)
    (assignment : Assignment setup mode) :
    SubmitsAtTurn setup leaks
      (assignedTurnPolicy (deadline := deadline) bound turns profile owner assignment) owner := by
  intro past view response chosen other submitted
  unfold assignedTurnPolicy at chosen
  split at chosen
  · split at chosen
    · exact decidedTurnPolicy_submitsAtTurn setup leaks bound owner _ _ past view response chosen
        other submitted
    · exact sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns _ profile owner past view
        response chosen other submitted
  · exact sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns _ profile owner past view
      response chosen other submitted

/-- Deciding at the first turn submits canonically. -/
theorem decidedTurnPolicy_submitsCanonically (bound : (serviceGraph setup mode).EventId → Nat)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (action : (serviceGraph setup mode).Action event) :
    SubmitsCanonically
      (decidedTurnPolicy (deadline := deadline) setup leaks bound owner event action) owner := by
  intro past view response chosen material submits
  have silenced : ∀ response ∈
      ((serviceApplication setup mode deadline leaks).silentPolicy past view).support,
      response.transmission = none := by
    intro response member
    obtain rfl := (serviceApplication setup mode deadline leaks).silentPolicy_cases past view
        response member
    rfl
  unfold decidedTurnPolicy ReactiveApplication.turnScheduledPolicy at chosen
  dsimp only at chosen
  split at chosen
  · rename_i first
    unfold decidedOpportunity at chosen
    split at chosen
    · rw [silenced response chosen] at submits
      cases submits
    · rename_i unrecorded
      split at chosen
      · split at chosen
        · rw [silenced response chosen] at submits
          cases submits
        · rw [PMF.mem_support_pure_iff] at chosen
          exact ⟨event, action, (sourceServiceTurn_first first).1, by simpa using unrecorded,
            chosen⟩
      · rw [silenced response chosen] at submits
        cases submits
  · rw [silenced response chosen] at submits
    cases submits

/-- The assigned client submits canonically. -/
theorem assignedTurnPolicy_submitsCanonically (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (profile : BehavioralProfile setup.program) (owner : Player)
    (assignment : Assignment setup mode) :
    SubmitsCanonically
      (assignedTurnPolicy (deadline := deadline) (leaks := leaks) bound turns profile owner
        assignment) owner := by
  intro past view response chosen material submits
  unfold assignedTurnPolicy at chosen
  split at chosen
  · split at chosen
    · exact decidedTurnPolicy_submitsCanonically bound owner _ _ past view response chosen
        material submits
    · exact serviceTurnPolicy_submitsCanonically bound turns _ profile owner past view response
        chosen material submits
  · exact serviceTurnPolicy_submitsCanonically bound turns _ profile owner past view response
      chosen material submits

/-- The assigned client decides each assigned action. -/
theorem assignedTurnPolicy_decidesAt (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (profile : BehavioralProfile setup.program) (owner : Player)
    (assignment : Assignment setup mode) (event : (serviceGraph setup mode).EventId)
    (action : (serviceGraph setup mode).Action event) (assigned : assignment event = some action) :
    DecidesAt (assignedTurnPolicy (deadline := deadline) (leaks := leaks) bound turns profile owner
      assignment) bound owner event action where
  first past view first unrecorded fits loud := by
    rw [assignedTurnPolicy_assigned (sourceServiceTurn_first first).1 assigned]
    exact (decidedTurnPolicy_decidesAt bound owner event action).first past view first
      unrecorded fits loud
  only past view response chosen submitted := by
    have turn := assignedTurnPolicy_submitsAtTurn bound turns profile owner assignment past view
      response chosen event submitted
    rw [assignedTurnPolicy_assigned turn assigned] at chosen
    exact (decidedTurnPolicy_decidesAt bound owner event action).only past view response chosen
      submitted

/-- **One decision drawn in advance.** Suppose that whenever the owner's first
turn at an unassigned owned event comes, along runs keeping an invariant, the
source decision there is `law` compiled to native responses. Then, from a legal
history where the owner has had no turn at the event, its assigned client runs,
whatever the other players do, as the `law`-mixture of the clients that also
assign the event. -/
theorem assignedTurnPolicy_runUntil_mixture
    (initial : PMF (EventGraphRuntime.State (serviceGraph setup mode))) (horizon : Nat)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (others : Player → (serviceApplication setup mode deadline leaks).Policy)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (assignment : Assignment setup mode) (event : (serviceGraph setup mode).EventId)
    (unassigned : assignment event = none)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (law : PMF ((serviceGraph setup mode).Action event))
    (stop : (serviceApplication setup mode deadline leaks).Execution → Prop) [DecidablePred stop]
    (invariant : (serviceApplication setup mode deadline leaks).Execution → Prop)
    (policy : ∀ remaining execution,
      ((serviceApplication setup mode deadline leaks).protocol initial horizon scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩) →
      invariant execution → ¬ stop execution →
      ∀ command ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment (serviceApplication setup mode deadline leaks))).support,
      ∀ middle ∈ (execution.environmentStep (serviceApplication setup mode deadline leaks)
        command).support,
        command.actor? (serviceApplication setup mode deadline leaks) = some owner →
        serviceTurn setup mode deadline leaks owner event (middle.recall owner)
          (middle.observe (serviceApplication setup mode deadline leaks) owner) = some 0 →
        serviceCanonicalPolicy setup mode deadline leaks profile owner (middle.recall owner)
            (middle.observe (serviceApplication setup mode deadline leaks) owner) =
          law.map fun action => (serviceRuntime setup mode deadline).canonicalServiceDecision leaks
            owner (middle.recall owner)
            (middle.observe (serviceApplication setup mode deadline leaks) owner) event action)
    (preserved : ∀ remaining execution,
      ((serviceApplication setup mode deadline leaks).protocol initial horizon scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩) →
      invariant execution → ¬ stop execution →
      ∀ next ∈ ((serviceApplication setup mode deadline leaks).round scheduler
        (Function.update others owner (assignedTurnPolicy bound turns profile owner assignment))
        execution).support, invariant next)
    (count remaining : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((serviceApplication setup mode deadline leaks).protocol initial horizon
      scheduler).Trace
        (some ⟨remaining + count, none, execution⟩))
    (holds : invariant execution)
    (clean : ∀ entry ∈ execution.recall owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event) :
    (serviceApplication setup mode deadline leaks).runUntil scheduler
        (Function.update others owner (assignedTurnPolicy bound turns profile owner assignment))
        stop count execution =
      law.bind fun action => (serviceApplication setup mode deadline leaks).runUntil scheduler
        (Function.update others owner (assignedTurnPolicy bound turns profile owner
          (Function.update assignment event (some action)))) stop count execution := by
  let app := serviceApplication setup mode deadline leaks
  let first := fun (past : List app.PlayerEntry) (view : app.PlayerView) =>
    serviceTurn setup mode deadline leaks owner event past view = some 0
  apply app.runUntil_mixture_at_first initial horizon scheduler others owner _ law _ first
  · intro past view firstNow before entry prefixed firstThen
    exact (sourceServiceTurn_first firstNow).2 entry
      (prefixed.subset (List.mem_append_right _ (List.mem_singleton_self _)))
      (sourceServiceTurn_first firstThen).1
  · intro action past view notFirst
    change ¬ serviceTurn setup mode deadline leaks owner event past view = some 0 at notFirst
    by_cases turn : view.application.publicView.ownTurn? owner = some event
    · rw [assignedTurnPolicy_assigned turn (Function.update_self ..),
        assignedTurnPolicy_unassigned turn unassigned, firstTurnPolicy_eq_family owned turn]
      rw [show decidedTurnPolicy setup leaks bound owner event action past view =
          app.silentPolicy past view from app.turnScheduledPolicy_unselected _ _ _ _ _ _
            fun slot _ equal => notFirst (by rw [equal, Fin.val_eq_zero slot])]
      exact (app.turnScheduledPolicy_unselected _ _ _ _ _ _
        fun slot chosen equal => notFirst (by
          rw [equal, ← Option.some.inj chosen]; rfl)).symm
    · exact assignedTurnPolicy_update_of_not_turn bound turns profile owner assignment event _ past
        view turn
  · intro remaining current currentTrace currentHolds running command selected middle moved
      active firstNow
    have turn := (sourceServiceTurn_first firstNow).1
    rw [assignedTurnPolicy_unassigned turn unassigned,
      sourceServiceTurnPolicy_firstTurn owned firstNow]
    have members : ∀ action, assignedTurnPolicy bound turns profile owner
        (Function.update assignment event (some action)) (middle.recall owner)
          (middle.observe app owner) =
        decidedOpportunity setup leaks bound owner event action (middle.recall owner)
          (middle.observe app owner) := by
      intro action
      rw [assignedTurnPolicy_assigned turn (Function.update_self ..)]
      exact app.turnScheduledPolicy_selected _ (0 : Fin 1) _ _ _ _ firstNow
    simp only [members]
    unfold serviceCanonicalOpportunity decidedOpportunity
    by_cases recorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (middle.recall owner) event
    · simp only [recorded, ↓reduceIte, PMF.bind_const]
    · by_cases fits : PublicView.InclusionFitsDeadline (serviceRuntime setup mode deadline) bound
          (middle.observe app owner).application.publicView event
      · simp only [recorded, fits, Bool.false_eq_true, ↓reduceIte]
        rw [policy remaining current currentTrace currentHolds running command selected middle
          moved active firstNow, PMF.bind_map]
        rfl
      · simp only [recorded, fits, Bool.false_eq_true, ↓reduceIte, PMF.bind_const]
  · exact preserved
  · exact trace
  · exact holds
  · intro before entry prefixed firstThen
    exact clean entry (prefixed.subset (List.mem_append_right _ (List.mem_singleton_self _)))
      (sourceServiceTurn_first firstThen).1

end Vegas
