/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.EventPolicies

/-! # Prescribed graph decisions in one activation

The policy samples once, remembers its original intention, and submits in the
same action. Failed disclosures use withholding packets. Source intentions are
reconstructed from own response memory when later graph policies are invoked.
Whole-service correctness additionally requires protected service and a proof
that these local observations agree with the source observations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

open Classical in
def reactiveFreshSlot (view : ReactivePlayerView graph) : Option Nat :=
  if fresh : ∃ serial, view.candidates (.prepared serial) = .fresh then
    some (Nat.find fresh) else none

omit [DecidableEq Player] in
theorem reactiveFreshSlot_spec (view : ReactivePlayerView graph) (serial : Nat)
    (selected : reactiveFreshSlot view = some serial) :
    view.candidates (.prepared serial) = .fresh := by
  classical
  unfold reactiveFreshSlot at selected
  split at selected
  · rename_i fresh
    cases Option.some.inj selected
    exact Nat.find_spec fresh
  · contradiction

def reactiveOriginal (runtime : EventGraphRuntime graph)
    (history : List runtime.reactiveApplication.PlayerEntry) (completion : graph.Completion) :
    graph.Completion :=
  ((history.filterMap fun entry => entry.action.memory.intention).find?
    (fun remembered => remembered.event = completion.event)).getD completion

def reactiveAlreadySubmitted (runtime : EventGraphRuntime graph)
    (history : List runtime.reactiveApplication.PlayerEntry) (event : graph.EventId) : Bool :=
  history.any fun entry => entry.emitted.any (fun message =>
    message.payload.event? graph = some event)

def reactiveResolutionPacket {owner : Player} (who : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : ReactivePlayerView graph) : Payload graph :=
  let disclose : Bool := cast (congrArg EventField.Action outputEq) action
  if disclose then
    match EventCode.resolveOutput? binding checks true view.observation.store with
    | some (.success value) => match view.publicView.accepted binding.field with
      | some handle => if handle.1 = who then .opening event handle ⟨payload, value⟩
          else .withhold event
      | none => .withhold event
    | some .failure | none => .withhold event
  else .withhold event

def reactiveDecision (runtime : EventGraphRuntime graph) (who : Player) (event : graph.EventId)
    (action : graph.Action event) (view : ReactivePlayerView graph) :
    runtime.reactiveApplication.Action where
  memory := ⟨some ⟨event, action⟩, []⟩
  transmission := match nodeView graph event with
    | .sample .. => none
    | .bind _owner payload outputEq _codeEq =>
        (reactiveFreshSlot view).map fun serial => .submit
          ⟨.commitment event (who, .prepared serial),
            match (cast (congrArg EventField.Action outputEq) action :
                PublicationResult (L.Val payload)) with
            | .failure => none
            | .success value => some ⟨payload, value⟩⟩
    | .resolve _owner payload binding checks outputEq _codeEq =>
        some (.submit ⟨reactiveResolutionPacket who event payload binding checks
          outputEq action view, none⟩)

/-- One ready owned event takes one activation, with no staging instructions.
The policy waits outside its grant or after its event packet has been sent. -/
def compileReactivePolicy (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who) : runtime.reactiveApplication.Policy :=
  fun history view => match view.application.publicView.serviceGrant with
  | none => FinDist.pure ⟨default, none⟩
  | some event =>
      if runtime.reactiveAlreadySubmitted history event then FinDist.pure ⟨default, none⟩
      else if owner : view.application.who = who then
        if view.application.publicView.EventReady event then
          if actor : graph.actor? event = some who then
            let observation : graph.PlayerObservation who :=
              owner ▸ view.application.observation
            let recalled : graph.PlayerObservation who :=
              { observation with
                ownActions := observation.ownActions.map (runtime.reactiveOriginal history) }
            (graph.normalizePolicy who policy event actor recalled).map
              (fun action => runtime.reactiveDecision who event action view.application)
          else FinDist.pure ⟨default, none⟩
        else FinDist.pure ⟨default, none⟩
      else FinDist.pure ⟨default, none⟩

end Vegas.EventGraphRuntime

-- OPEN OBLIGATION: Reactive graph-policy compiler correctness
-- Prove source observation reconstruction and realization of each sampled
-- decision throughout protected service, then compose the compiler and deviation laws.
-- The command-service theorem does not supply this edge.
