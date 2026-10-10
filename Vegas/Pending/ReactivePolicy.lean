/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveNormalization
import Vegas.EventGraph.NormalizedPolicy
import Vegas.Pending.EventPublicState
import Interaction.ReactiveRecovery
import Interaction.ReactiveImplementation

/-! # Prescribed graph decisions in one activation

The prescribed policy samples once, remembers its original intention, and
submits in the same action. A recovery continuation can submit again after an
earlier deviation, reusing a supported remembered choice. Disclosures open only
when owner-local validation predicts successful publication; every failed result
withholds. Accepted packets and matching silent decisions restore their original
intentions; a silent sampled decision also prevents a later redraw.
Whole-service correctness additionally requires protected service and a proof
that these local observations agree with the source observations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

open Classical in
def reactiveFreshSlot (view : PlayerView graph) : Option Nat :=
  if fresh : ∃ serial, view.candidates (.prepared serial) = .fresh then
    some (Nat.find fresh) else none

omit [DecidableEq Player] in
theorem reactiveFreshSlot_spec (view : PlayerView graph) (serial : Nat)
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
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) : Bool :=
  history.any fun entry => entry.emitted.any (fun message =>
    message.payload.call.event? graph = some event)

def reactiveResolutionPacket {owner : Player} (who : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : PlayerView graph) : Option (Payload graph) :=
  let disclose : Bool := cast (congrArg EventField.Action outputEq) action
  if disclose then
    match EventCode.resolveOutput? binding checks true view.observation.store with
    | some (.success value) => match view.publicView.accepted binding.field with
      | some handle => if handle.1 = who then some (.opening event handle ⟨payload, value⟩)
          else none
      | none => none
    | some .failure | none => none
  else none

/-- Request the owned opening witness carried by a disclosure. Other packets
supply no evidence; a false opening claim still fails certificate issuance. -/
def disclosureSubmission (packet : Payload graph) : WitnessedSubmission graph :=
  ⟨⟨packet, none⟩, match packet with
    | .opening _ candidate raw => .owned ⟨candidate, raw⟩
    | .commitment .. | .malformed .. => .none⟩

/-- Normalization retains the authentic certificate of an owned opening. -/
theorem disclosureSubmission_normalize_opening (who : Player) (view : PlayerView graph)
    (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) (owned : candidate.1 = who)
    (verified : view.candidates candidate.2 = .openable raw) :
    (disclosureSubmission (.opening event candidate raw)).normalizeReactive who view [] =
      disclosureSubmission (.opening event candidate raw) := by
  simp only [disclosureSubmission, WitnessedSubmission.normalizeReactive,
    Submission.normalizeReactive_none, Submission.candidateAfter,
    EvidenceRequest.normalize_owned_nil,
    owned, verified, and_self, ↓reduceIte]

def reactiveDecision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId)
    (action : graph.Action event) (view : PlayerView graph) :
    (runtime.reactiveApplication leaks).Action where
  transmission := match nodeView graph event with
    | .sample .. => none
    | .bind _owner payload outputEq _codeEq =>
        (reactiveFreshSlot view).map fun serial =>
          ⟨⟨.commitment event (who, .prepared serial),
            match (cast (congrArg EventField.Action outputEq) action :
                PublicationResult (L.Val payload)) with
            | .failure => none
            | .success value => some ⟨payload, value⟩⟩, .none⟩
    | .resolve _owner payload binding checks outputEq _codeEq =>
        (reactiveResolutionPacket who event payload binding checks outputEq action view).map
          fun packet => (disclosureSubmission packet).normalizeReactive who view []

/-- A remembered silent decision matches the actual response at a ready
owned input. Silence without this observation and response evidence cannot
restore a private intention. Supported implementation memory supplies the
sampled intention; this predicate validates its recorded physical response. -/
def ReactiveSilentDecision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (remembered : graph.Completion) : Prop :=
  entry.emitted = none ∧ entry.action.transmission = none ∧
    entry.beforeView.application.who = who ∧
    entry.beforeView.application.publicView.ownTurn? who = some remembered.event ∧
    entry.beforeView.application.publicView.EventReady remembered.event ∧
    graph.actor? remembered.event = some who ∧
    entry.action = runtime.reactiveDecision leaks who remembered.event remembered.action
      entry.beforeView.application

open Classical in
/-- A sampled silent decision is already made, even though it emitted no
packet. Internal memory must match the actual ready owned response. -/
def reactiveAlreadyDecided (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion)) (event : graph.EventId) : Bool :=
  decide (∃ entry remembered, (entry, some remembered) ∈ history.zip intentions ∧
    remembered.event = event ∧ runtime.ReactiveSilentDecision leaks who entry remembered)

open Classical in
/-- Binding recall uses the value that actually took effect. Resolution recall
retains a sampled intention when its response either produced an accepted
packet or was a matching silent decision at a ready owned input. -/
def reactiveOriginal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (receipts : List (MessageId Player × Bool)) (completion : graph.Completion) :
    graph.Completion :=
  match nodeView graph completion.event with
  | .sample .. | .bind .. => completion
  | .resolve .. =>
      (((history.zip intentions).filterMap fun (entry, intention) => do
        let remembered ← intention
        if remembered.event = completion.event ∧
            runtime.ReactiveSilentDecision leaks who entry remembered then some remembered
        else do
          let message ← entry.emitted
          if remembered.event = completion.event ∧
              message.payload.call.event? graph = some completion.event ∧
              (message.id, true) ∈ receipts ∧
              entry.action = runtime.reactiveDecision leaks who remembered.event
                remembered.action entry.beforeView.application then some remembered
          else none).head?).getD completion

/-- One ready owned event takes one activation, with no staging instructions.
On consistent own histories this policy sends at most one packet per event.
The client serves its own turn (`PublicView.ownTurn?`), so it acts as soon as
its event is ready. -/
def prescribedReactiveResponse (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    PMF ((runtime.reactiveApplication leaks).Action × Option graph.Completion) :=
  match view.application.publicView.ownTurn? who with
  | none => PMF.pure (⟨none⟩, none)
  | some event =>
      if runtime.reactiveAlreadySubmitted leaks history event ||
          runtime.reactiveAlreadyDecided leaks who history intentions event then
        PMF.pure (⟨none⟩, none)
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
          else PMF.pure (⟨none⟩, none)
        else PMF.pure (⟨none⟩, none)
      else PMF.pure (⟨none⟩, none)

/-- The compiler's source intentions are internal state, not game actions. -/
def prescribedReactiveImplementation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (runtime.reactiveApplication leaks).Implementation (List (Option graph.Completion)) where
  initial := PMF.pure []
  respond intentions input :=
    (runtime.prescribedReactiveResponse leaks who policy input.1 intentions input.2).map
      fun response => (response.1, intentions ++ [response.2])

def prescribedReactivePolicy (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (runtime.reactiveApplication leaks).Policy :=
  (runtime.prescribedReactiveImplementation leaks who policy).policy

theorem prescribedReactivePolicy_apply (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    runtime.prescribedReactivePolicy leaks who policy history view =
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).bind
        (fun intentions => (runtime.prescribedReactiveResponse leaks who policy history
          intentions view).map Prod.fst) := by
  rw [prescribedReactivePolicy, ReactiveApplication.Implementation.policy_eq]
  simp only [prescribedReactiveImplementation, PMF.map_bind, PMF.map_comp,
    Function.comp_def]

open Classical in
/-- Reuse a supported remembered choice, or sample the source policy when no
such choice exists. An unsupported internal choice cannot suppress recovery. -/
def reactiveRecoveryLaw (intentions : List (Option graph.Completion))
    (event : graph.EventId) (law : PMF (graph.Action event)) : PMF (graph.Action event) :=
  let remembered := intentions.reverse.filterMap fun saved => do
    let intention ← saved
    if same : intention.event = event then some (same ▸ intention.action) else none
  match remembered.find? (fun action => action ∈ law.support) with
  | some action => PMF.pure action
  | none => law

/-- Recovery still consumes one activation per response. It sends a fresh
candidate while the event is ready; it cannot erase old packets, change a
submitted meaning, or extend a deadline. -/
def recoverReactiveResponse (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    PMF ((runtime.reactiveApplication leaks).Action × Option graph.Completion) :=
  match view.application.publicView.ownTurn? who with
  | none => PMF.pure (⟨none⟩, none)
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
          else PMF.pure (⟨none⟩, none)
        else PMF.pure (⟨none⟩, none)
      else PMF.pure (⟨none⟩, none)

def recoverReactiveImplementation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (runtime.reactiveApplication leaks).Implementation (List (Option graph.Completion)) where
  initial := PMF.pure []
  respond intentions input :=
    (runtime.recoverReactiveResponse leaks who policy input.1 intentions input.2).map
      fun response => (response.1, intentions ++ [response.2])

def recoverReactivePolicy (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (runtime.reactiveApplication leaks).Policy :=
  (runtime.recoverReactiveImplementation leaks who policy).policy

theorem recoverReactivePolicy_apply (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    runtime.recoverReactivePolicy leaks who policy history view =
      ((runtime.recoverReactiveImplementation leaks who policy).posterior history).bind
        (fun intentions => (runtime.recoverReactiveResponse leaks who policy history
          intentions view).map Prod.fst) := by
  rw [recoverReactivePolicy, ReactiveApplication.Implementation.policy_eq]
  simp only [recoverReactiveImplementation, PMF.map_bind, PMF.map_comp,
    Function.comp_def]

/-- The compiler completes prescribed play at histories containing the owner's
own deviations. Recovery optimality is a separate continuation obligation. -/
def compileReactivePolicy (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (runtime.reactiveApplication leaks).Policy :=
  (runtime.prescribedReactivePolicy leaks who policy).recover
    (runtime.recoverReactivePolicy leaks who policy)

end Vegas.EventGraphRuntime

-- OPEN OBLIGATION: Reactive graph-policy compiler correctness
-- Prove source observation reconstruction and realization of each sampled
-- decision throughout protected service, then compose the compiler and deviation laws.
-- The command-service theorem does not supply this edge.
