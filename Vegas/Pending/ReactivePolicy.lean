/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.EventPolicies
import Interaction.ReactiveRecovery
import Interaction.ReactiveImplementation

/-! # Prescribed graph decisions in one activation

The prescribed policy samples once, remembers its original intention, and
submits in the same action. A recovery continuation can submit again after an
earlier deviation, reusing a supported remembered choice. Openable disclosures
send their evidence even when guards reject publication. Only accepted packets
can restore their intentions.
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

def reactiveAlreadySubmitted (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) : Bool :=
  history.any fun entry => entry.emitted.any (fun message =>
    message.payload.event? graph = some event)

def reactiveResolutionPacket {owner : Player} (who : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : ReactivePlayerView graph) : Payload graph :=
  let disclose : Bool := cast (congrArg EventField.Action outputEq) action
  if disclose then
    match binding.get? view.observation.store with
    | some (.success value) => match view.publicView.accepted binding.field with
      | some handle => if handle.1 = who then .opening event handle ⟨payload, value⟩
          else .withhold event
      | none => .withhold event
    | some .failure | none => .withhold event
  else .withhold event

def reactiveDecision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player) (event : graph.EventId)
    (action : graph.Action event) (view : ReactivePlayerView graph) :
    (runtime.reactiveApplication leaks).Action where
  transmission := match nodeView graph event with
    | .sample .. => none
    | .bind _owner payload outputEq _codeEq =>
        (reactiveFreshSlot view).map fun serial => .submit
          ⟨.commitment event (who, .prepared serial),
            match (cast (congrArg EventField.Action outputEq) action :
                PublicationResult (L.Val payload)) with
            | .failure => none
            | .success value => some ⟨payload, value⟩⟩
    | .resolve _owner payload binding _checks outputEq _codeEq =>
        some (.submit ⟨reactiveResolutionPacket who event payload binding
          outputEq action view, none⟩)

open Classical in
/-- Binding recall uses the value that actually took effect. A failed
disclosure can retain its original intention only when the corresponding
response generated an accepted packet. A mismatched internal intention is insufficient. -/
def reactiveOriginal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (receipts : List (MessageId Player × Bool)) (completion : graph.Completion) :
    graph.Completion :=
  match nodeView graph completion.event with
  | .sample .. | .bind .. => completion
  | .resolve .. =>
      (((history.zip intentions).filterMap fun (entry, intention) => do
        let remembered ← intention
        let message ← entry.emitted
        if remembered.event = completion.event ∧
            message.payload.event? graph = some completion.event ∧
            (message.id, true) ∈ receipts ∧
            entry.action = runtime.reactiveDecision leaks who remembered.event
              remembered.action entry.beforeView.application then some remembered
        else none).head?).getD completion

/-- One ready owned event takes one activation, with no staging instructions.
On consistent own histories this policy sends at most one packet per event. -/
def prescribedReactiveResponse (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    FinDist ((runtime.reactiveApplication leaks).Action × Option graph.Completion) :=
  match view.application.publicView.serviceGrant with
  | none => FinDist.pure (⟨none⟩, none)
  | some event =>
      if runtime.reactiveAlreadySubmitted leaks history event then FinDist.pure (⟨none⟩, none)
      else if owner : view.application.who = who then
        if view.application.publicView.EventReady event then
          if actor : graph.actor? event = some who then
            let observation : graph.PlayerObservation who :=
              owner ▸ view.application.observation
            let recalled : graph.PlayerObservation who :=
              { observation with
                ownActions := observation.ownActions.map (runtime.reactiveOriginal leaks who
                  history intentions view.receipts) }
            (graph.normalizePolicy who policy event actor recalled).map
              (fun action => (runtime.reactiveDecision leaks who event action view.application,
                some ⟨event, action⟩))
          else FinDist.pure (⟨none⟩, none)
        else FinDist.pure (⟨none⟩, none)
      else FinDist.pure (⟨none⟩, none)

/-- The compiler's source intentions are internal state, not game actions. -/
def prescribedReactiveImplementation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (runtime.reactiveApplication leaks).Implementation (List (Option graph.Completion)) where
  initial := FinDist.pure []
  respond intentions input :=
    (runtime.prescribedReactiveResponse leaks who policy input.1 intentions input.2).map
      fun response => (response.1, intentions ++ [response.2])

def prescribedReactivePolicy (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (runtime.reactiveApplication leaks).Policy :=
  (runtime.prescribedReactiveImplementation leaks who policy).policy

theorem prescribedReactivePolicy_apply (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    runtime.prescribedReactivePolicy leaks who policy history view =
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).bind
        (fun intentions => (runtime.prescribedReactiveResponse leaks who policy history
          intentions view).map Prod.fst) := by
  rw [prescribedReactivePolicy, ReactiveApplication.Implementation.policy_eq]
  simp only [prescribedReactiveImplementation, FinDist.map_bind, FinDist.map_comp,
    Function.comp_def]

open Classical in
/-- Reuse a supported remembered choice, or sample the source policy when no
such choice exists. An unsupported internal choice cannot suppress recovery. -/
def reactiveRecoveryLaw (intentions : List (Option graph.Completion))
    (event : graph.EventId) (law : FinDist (graph.Action event)) : FinDist (graph.Action event) :=
  let remembered := intentions.reverse.filterMap fun saved => do
    let intention ← saved
    if same : intention.event = event then some (same ▸ intention.action) else none
  match remembered.find? (fun action => action ∈ law.support) with
  | some action => FinDist.pure action
  | none => law

/-- Recovery still consumes one activation per response. It sends a fresh
candidate while the event is ready; it cannot erase old packets, change a
submitted meaning, or extend a deadline. -/
def recoverReactiveResponse (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    FinDist ((runtime.reactiveApplication leaks).Action × Option graph.Completion) :=
  match view.application.publicView.serviceGrant with
  | none => FinDist.pure (⟨none⟩, none)
  | some event =>
      if owner : view.application.who = who then
        if view.application.publicView.EventReady event then
          if actor : graph.actor? event = some who then
            let observation : graph.PlayerObservation who :=
              owner ▸ view.application.observation
            let recalled : graph.PlayerObservation who :=
              { observation with
                ownActions := observation.ownActions.map (runtime.reactiveOriginal leaks who
                  history intentions view.receipts) }
            (reactiveRecoveryLaw intentions event
              (graph.normalizePolicy who policy event actor recalled)).map
                (fun action => (runtime.reactiveDecision leaks who event action view.application,
                  some ⟨event, action⟩))
          else FinDist.pure (⟨none⟩, none)
        else FinDist.pure (⟨none⟩, none)
      else FinDist.pure (⟨none⟩, none)

def recoverReactiveImplementation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (runtime.reactiveApplication leaks).Implementation (List (Option graph.Completion)) where
  initial := FinDist.pure []
  respond intentions input :=
    (runtime.recoverReactiveResponse leaks who policy input.1 intentions input.2).map
      fun response => (response.1, intentions ++ [response.2])

def recoverReactivePolicy (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (runtime.reactiveApplication leaks).Policy :=
  (runtime.recoverReactiveImplementation leaks who policy).policy

theorem recoverReactivePolicy_apply (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    runtime.recoverReactivePolicy leaks who policy history view =
      ((runtime.recoverReactiveImplementation leaks who policy).posterior history).bind
        (fun intentions => (runtime.recoverReactiveResponse leaks who policy history
          intentions view).map Prod.fst) := by
  rw [recoverReactivePolicy, ReactiveApplication.Implementation.policy_eq]
  simp only [recoverReactiveImplementation, FinDist.map_bind, FinDist.map_comp,
    Function.comp_def]

/-- The compiler completes prescribed play at histories containing the owner's
own deviations. Recovery optimality is a separate continuation obligation. -/
def compileReactivePolicy (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (runtime.reactiveApplication leaks).Policy :=
  (runtime.prescribedReactivePolicy leaks who policy).recover
    (runtime.recoverReactivePolicy leaks who policy)

end Vegas.EventGraphRuntime

-- OPEN OBLIGATION: Reactive graph-policy compiler correctness
-- Prove source observation reconstruction and realization of each sampled
-- decision throughout protected service, then compose the compiler and deviation laws.
-- The command-service theorem does not supply this edge.
