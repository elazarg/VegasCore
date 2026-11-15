module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceFirstTurnMixture
public import Vegas.Game.SourceServiceTurnSubmissions
public import Vegas.EventGraph.PolicyPatch
public import Vegas.EventGraph.BindingSubmission
public import Vegas.EventGraph.PrefixPolicy
public import Interaction.ReactiveMixtureRounds

@[expose] public section

/-! # Fixed first-turn actions and graph policy patches

A pure graph-policy patch compiles to the fixed native first-turn response on actual
raw traces. Other events retain their existing clients and full stopped execution law.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

def fixedTurnPolicy (bound : (serviceGraph setup deps).EventId → Nat)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (action : (serviceGraph setup deps).Action event)
    (fallback : (serviceApplication setup deps duration leaks).Policy) :
    (serviceApplication setup deps duration leaks).Policy := fun past view =>
  if serviceTurn setup deps duration leaks owner event past view = some 0 then
    decidedOpportunity setup leaks bound owner event action past view
  else fallback past view

private theorem serviceTurn_first_ne_of_ne
    (owner : Player) (event other : (serviceGraph setup deps).EventId)
    (different : other ≠ event)
    (past : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (view : (serviceApplication setup deps duration leaks).PlayerView)
    (first : serviceTurn setup deps duration leaks owner event past view = some 0) :
    serviceTurn setup deps duration leaks owner other past view ≠ some 0 := by
  intro otherFirst
  exact different (Option.some.inj
    ((sourceServiceTurn_first otherFirst).1.symm.trans (sourceServiceTurn_first first).1))

theorem fixedTurnPolicy_at_other
    (bound : (serviceGraph setup deps).EventId → Nat)
    (owner : Player) (event other : (serviceGraph setup deps).EventId)
    (action : (serviceGraph setup deps).Action event)
    (fallback : (serviceApplication setup deps duration leaks).Policy)
    (different : event ≠ other)
    (past : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (view : (serviceApplication setup deps duration leaks).PlayerView)
    (first : serviceTurn setup deps duration leaks owner other past view = some 0) :
    fixedTurnPolicy bound owner event action fallback past view = fallback past view := by
  exact ite_eq_right (serviceTurn_first_ne_of_ne owner other event different past view first)

theorem fixedTurnPolicy_comm
    (bound : (serviceGraph setup deps).EventId → Nat)
    (owner : Player) (event other : (serviceGraph setup deps).EventId)
    (action : (serviceGraph setup deps).Action event)
    (otherAction : (serviceGraph setup deps).Action other)
    (fallback : (serviceApplication setup deps duration leaks).Policy)
    (different : event ≠ other) :
    fixedTurnPolicy bound owner event action
        (fixedTurnPolicy bound owner other otherAction fallback) =
      fixedTurnPolicy bound owner other otherAction
        (fixedTurnPolicy bound owner event action fallback) := by
  funext past view
  by_cases first : serviceTurn setup deps duration leaks owner event past view = some 0
  · have otherNotFirst :=
      serviceTurn_first_ne_of_ne owner event other different.symm past view first
    simp only [fixedTurnPolicy, first, otherNotFirst, ite_true, ite_false]
  · simp only [fixedTurnPolicy, first, ite_false]

theorem fixedTurnPolicy_submitsAtTurn
    (bound : (serviceGraph setup deps).EventId → Nat)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (action : (serviceGraph setup deps).Action event)
    (fallback : (serviceApplication setup deps duration leaks).Policy)
    (atTurn : SubmitsAtTurn setup leaks fallback owner) :
    SubmitsAtTurn setup leaks (fixedTurnPolicy bound owner event action fallback) owner := by
  intro past view response member other submitted
  by_cases first : serviceTurn setup deps duration leaks owner event past view = some 0
  · have chosen : response ∈
        (decidedTurnPolicy setup leaks bound owner event action past view).support := by
      simpa only [fixedTurnPolicy, decidedTurnPolicy, ReactiveApplication.turnScheduledPolicy,
        first, Fin.val_zero, ite_true] using member
    exact decidedTurnPolicy_submitsAtTurn setup leaks bound owner event action past view
      response chosen other submitted
  · exact atTurn past view response (by simpa only [fixedTurnPolicy, first, ite_false] using member)
      other submitted

theorem fixedTurnPolicy_noRepeatedEvent
    (bound : (serviceGraph setup deps).EventId → Nat)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (action : (serviceGraph setup deps).Action event)
    (fallback : (serviceApplication setup deps duration leaks).Policy)
    (noRepeat : ∀ past view response, response ∈ (fallback past view).support →
      ∀ other, (eventRecorded (serviceTimeouts setup deps duration)) leaks past other = true →
        (submittedEvent? (serviceTimeouts setup deps duration)) leaks response ≠ some other) :
    ∀ past view response,
      response ∈ (fixedTurnPolicy bound owner event action fallback past view).support →
      ∀ other, (eventRecorded (serviceTimeouts setup deps duration)) leaks past other = true →
        (submittedEvent? (serviceTimeouts setup deps duration)) leaks response ≠ some other := by
  intro past view response member other recorded submitted
  by_cases first : serviceTurn setup deps duration leaks owner event past view = some 0
  · have chosen : response ∈
        (decidedTurnPolicy setup leaks bound owner event action past view).support := by
      simpa only [fixedTurnPolicy, decidedTurnPolicy, ReactiveApplication.turnScheduledPolicy,
        first, Fin.val_zero, ite_true] using member
    have serving := decidedTurnPolicy_submitsAtTurn setup leaks bound owner event action past view
      response chosen other submitted
    have same : other = event :=
      Option.some.inj (serving.symm.trans (sourceServiceTurn_first first).1)
    subst other
    simp only [fixedTurnPolicy, first, ite_true, decidedOpportunity, recorded,
      ReactiveApplication.silentPolicy_apply] at member
    cases (PMF.mem_support_pure_iff _ _).mp member
    cases submitted
  · exact noRepeat past view response
      (by simpa only [fixedTurnPolicy, first, ite_false] using member) other recorded submitted

theorem serviceReferenceTurnPolicy_patch_at_execution
    {turns : Nat}
    (bound : (serviceGraph setup deps).EventId → Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (action : (serviceGraph setup deps).Action event)
    (head : (serviceGraph setup deps).BehavioralPolicy owner)
    (fixed : ∀ observation active, head event owned observation active = PMF.pure action)
    (current : (serviceApplication setup deps duration leaks).Execution) :
    let committed := Function.update reference owner
      (EventGraph.patchPolicy event head (reference owner))
    serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) committed owner (current.logs owner)
        (current.observe (serviceApplication setup deps duration leaks) owner) =
      fixedTurnPolicy bound owner event action
        (serviceReferenceTurnPolicy setup deps duration leaks bound turns
          (firstTurnTiming setup turns deps) reference owner) (current.logs owner)
        (current.observe (serviceApplication setup deps duration leaks) owner) := by
  classical
  intro committed
  let app := serviceApplication setup deps duration leaks
  let past := current.logs owner
  let view := current.observe app owner
  change serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) committed owner past view =
    fixedTurnPolicy bound owner event action
      (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) reference owner) past view
  have atEvent (serving : view.application.publicView.ownTurn? owner = some event) :
      serviceReferencePolicy setup deps duration leaks committed owner past view =
        PMF.pure ((canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks owner
          past view event action) := by
    rw [sourceServiceCanonicalPolicy_at_event_reference setup leaks committed owner current event
      serving owned]
    by_cases inactive : owner ∈ current.application.config.defaulted
    · rw [dite_eq_left inactive,
        (canonicalServiceDecision_defaulted (serviceTimeouts setup deps duration)) leaks owner
          past view event action inactive]
    · rw [dite_eq_right inactive]
      simp only [committed, Function.update_self, EventGraph.patchPolicy, ite_true, fixed,
        PMF.pure_map]
      rfl
  have atOther (selected : (serviceGraph setup deps).EventId)
      (serving : view.application.publicView.ownTurn? owner = some selected)
      (actor : (serviceGraph setup deps).actor? selected = some owner)
      (different : selected ≠ event) :
      serviceReferencePolicy setup deps duration leaks committed owner past view =
        serviceReferencePolicy setup deps duration leaks reference owner past view := by
    rw [sourceServiceCanonicalPolicy_at_event_reference setup leaks committed owner current
      selected serving actor, sourceServiceCanonicalPolicy_at_event_reference setup leaks
      reference owner current selected serving actor]
    simp only [committed, Function.update_self, EventGraph.patchPolicy, ite_eq_right different]
  have targetOnly {selected : (serviceGraph setup deps).EventId}
      (serving : view.application.publicView.ownTurn? owner = some selected)
      (different : selected ≠ event) :
      serviceTurn setup deps duration leaks owner event past view ≠ some 0 := by
    intro first
    exact different (Option.some.inj (serving.symm.trans (sourceServiceTurn_first first).1))
  cases serving : view.application.publicView.ownTurn? owner with
  | none =>
      have notFirst : serviceTurn setup deps duration leaks owner event past view ≠ some 0 := by
        intro first
        have turn := (sourceServiceTurn_first first).1
        rw [serving] at turn
        cases turn
      simp only [fixedTurnPolicy, notFirst, ite_false, serviceReferenceTurnPolicy, serving]
  | some selected =>
      by_cases actor : (serviceGraph setup deps).actor? selected = some owner
      · by_cases first : serviceTurn setup deps duration leaks owner selected past view = some 0
        · rw [sourceServiceTurnPolicy_firstTurn_reference actor first]
          by_cases same : selected = event
          · subst selected
            simp only [fixedTurnPolicy, first, ite_true]
            unfold serviceReferenceOpportunity decidedOpportunity
            rw [atEvent serving]
            simp only [PMF.pure_bind]
          · rw [fixedTurnPolicy, ite_eq_right (targetOnly serving same),
              sourceServiceTurnPolicy_firstTurn_reference actor first]
            unfold serviceReferenceOpportunity
            rw [atOther selected serving actor same]
        · have noTarget : serviceTurn setup deps duration leaks owner event past view ≠ some 0 := by
            by_cases same : selected = event
            · simpa only [same] using first
            · exact targetOnly serving same
          rw [fixedTurnPolicy, ite_eq_right noTarget,
            sourceServiceTurnPolicy_laterTurn_reference actor serving first,
            sourceServiceTurnPolicy_laterTurn_reference actor serving first]
      · have noTarget : serviceTurn setup deps duration leaks owner event past view ≠ some 0 := by
          by_cases same : selected = event
          · exact (actor (same.symm ▸ owned)).elim
          · exact targetOnly serving same
        simp only [fixedTurnPolicy, noTarget, ite_false, serviceReferenceTurnPolicy, serving,
          actor, dite_false]
theorem serviceReferenceTurnPolicy_patch_runUntil
    {count turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (action : (serviceGraph setup deps).Action event)
    (head : (serviceGraph setup deps).BehavioralPolicy owner)
    (fixed : ∀ observation active, head event owned observation active = PMF.pure action)
    (background : Player → (serviceApplication setup deps duration leaks).Policy)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop) [DecidablePred stop]
    (current : (serviceApplication setup deps duration leaks).Execution) :
    let committed := Function.update reference owner
      (EventGraph.patchPolicy event head (reference owner))
    let client := fun profile => serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) profile owner
    (serviceApplication setup deps duration leaks).runUntil scheduler
        (Function.update background owner (client committed)) stop count current =
      (serviceApplication setup deps duration leaks).runUntil scheduler
        (Function.update background owner
          (fixedTurnPolicy bound owner event action (client reference))) stop count current := by
  intro committed client
  let app := serviceApplication setup deps duration leaks
  apply app.runUntil_congr_of_agree scheduler _ _ stop (fun _ => True) _ _ count current
    True.intro
  · intro current _ _ command _ middle _ who _
    by_cases isOwner : who = owner
    · subst who
      simp only [Function.update_self]
      exact serviceReferenceTurnPolicy_patch_at_execution bound reference owner event owned
        action head fixed middle
    · simp only [Function.update_of_ne isOwner]
  · intro _ _ _ _ _
    trivial

end Vegas
