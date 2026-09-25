/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSchedule
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveDisclosure
import Vegas.Pending.ReactiveBoundedHandles
import Vegas.Pending.ReactiveStateInvariant

/-! # Available ordinary openings in the native selective-association game

Fresh opening envelopes require no new commitment candidate. Their full raw
responses are admitted by the existing bounded menu, and immediate reserved
inclusion overrides earlier pending traffic from the same owner. Acceptance
still uses the actual compiled graph's ordinary disclosure handler.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

variable {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}

def nativeOpeningSubmission (event : nativeGraph.EventId) (candidate : Handle nativeGraph)
    (bit : Bool) : WitnessedSubmission nativeGraph :=
  disclosureSubmission (.opening event candidate ⟨.bool, bit⟩)

def nativeOpeningAction (event : nativeGraph.EventId) (candidate : Handle nativeGraph)
    (bit : Bool) : (serviceApp observation).Action :=
  ⟨some (.submit (nativeOpeningSubmission event candidate bit))⟩

theorem native_opening_available (who : Player) (event : nativeGraph.EventId)
    (candidate : Handle nativeGraph) (bit : Bool)
    (allowed : nativeBounds.AllowsHandle candidate)
    (past : List (serviceApp observation).PlayerEntry) (view : (serviceApp observation).PlayerView)
      :
    nativeOpeningAction event candidate bit ∈ (serviceMenu observation).actions who past view := by
  change nativeOpeningAction event candidate bit ∈
    (nativeBounds.rawMenu nativeRuntime observation).actions who past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change nativeOpeningSubmission event candidate bit ∈ nativeBounds.submissions _
  rw [MessageBounds.submissions_mem]
  have value : (⟨.bool, bit⟩ : Raw simpleExpr) ∈ nativeBounds.values := by cases bit <;> decide
  exact ⟨⟨⟨allowed, value⟩, trivial⟩, allowed, value⟩

theorem native_opening_selected (execution : (serviceApp observation).Execution) (who : Player)
    (event : nativeGraph.EventId) (candidate : Handle nativeGraph) (bit : Bool)
    (serials : execution.network.SerialsBeforeNext) :
    nativeRuntime.reactiveLatest observation event who
      ((execution.respond (serviceApp observation) who
        (nativeOpeningAction event candidate bit)).observeEnvironment (serviceApp observation)) =
        .include (who, execution.network.nextSerial who) :=
  nativeRuntime.reactiveLatest_after_submit observation who event execution serials
    (nativeOpeningSubmission event candidate bit) rfl

theorem native_opening_respond_state (execution : (serviceApp observation).Execution) (who : Player)
    (event : nativeGraph.EventId) (candidate : Handle nativeGraph) (bit : Bool) :
    (execution.respond (serviceApp observation) who (nativeOpeningAction event candidate
      bit)).application =
      execution.application := rfl

theorem native_opening_lookup (execution : (serviceApp observation).Execution) (who : Player)
    (event : nativeGraph.EventId) (candidate : Handle nativeGraph) (bit : Bool)
    (serials : execution.network.SerialsBeforeNext) :
    (execution.respond (serviceApp observation) who (nativeOpeningAction event candidate
      bit)).network.lookup
      (who, execution.network.nextSerial who) =
        some ⟨(who, execution.network.nextSerial who),
          (nativeOpeningSubmission event candidate bit).emit execution.application who
            (execution.network.known who)⟩ :=
  serials.lookup_submit who _

/-- Exact application law after the real response and its reserved inclusion.
The handler premise will be discharged by the compiled publication rule. -/
theorem native_opening_inclusion (players : Player → (serviceApp observation).Policy)
    (execution : (serviceApp observation).Execution) (who : Player) (event : nativeGraph.EventId)
    (candidate : Handle nativeGraph) (bit : Bool) (state : State nativeGraph)
    (serials : execution.network.SerialsBeforeNext)
    (accepted : handle nativeRuntime execution.application
      ⟨(who, execution.network.nextSerial who), .opening event candidate ⟨.bool, bit⟩⟩ =
        some state) :
    (nativeRuntime.interactionStep observation players (serviceNetwork observation) (.includeLatest
      event who)
      (execution.respond (serviceApp observation) who (nativeOpeningAction event candidate
        bit))).map
        (fun next => next.application) = FinDist.pure state := by
  simp only [interactionStep, interactionInstruction, native_opening_selected execution who
    event candidate bit serials, FinDist.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, FinDist.map_pure, FinDist.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, FinDist.map_pure]
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [native_opening_lookup execution who event candidate bit serials]
  change FinDist.pure ((handle nativeRuntime execution.application
    ⟨(who, execution.network.nextSerial who), .opening event candidate ⟨.bool, bit⟩⟩).getD
      execution.application) = _
  rw [accepted]
  rfl

def nativePublicationEvent (who : Player) : nativeGraph.EventId :=
  if who = alice then alicePublication else if who = bob then bobPublication else carolPublication

def nativeBindingRef (who : Player) :
    EventGraph.FieldRef nativeGraph.layout (.binding who .bool) := by
  refine Fin.cases ?_ (fun next => Fin.cases ?_ (fun last => Fin.cases ?_ ?_ last) next) who
  · exact aliceBindingRef
  · exact bobBindingRef
  · exact carolBindingRef
  · intro impossible
    exact impossible.elim0

theorem native_binding_ref_eq (who : Player) :
    nativeBindingRef who = ⟨.inr (nativeBindingEvent who), native_binding_output who⟩ := by
  fin_cases who <;> rfl

theorem native_publication_output (who : Player) :
    nativeGraph.outputLayout (nativePublicationEvent who) = .publication BaseTy.bool := by
  fin_cases who <;> rfl

def nativePublicationRef (who : Player) :
    EventGraph.FieldRef nativeGraph.layout (.publication .bool) :=
  ⟨.inr (nativePublicationEvent who), native_publication_output who⟩

theorem native_publication_rule (who : Player) :
    ∃ checks : List (EventGraph.GuardCheck nativeGraph.layout .bool),
      ∃ codeEq : cast (congrArg (EventGraph.EventCode nativeGraph.layout)
        (native_publication_output who)) (nativeGraph.nodes (nativePublicationEvent who)) =
        EventGraph.EventCode.resolve (L := simpleExpr) who BaseTy.bool
          (nativeBindingRef who) checks,
      nodeView nativeGraph (nativePublicationEvent who) =
        .resolve who BaseTy.bool (nativeBindingRef who) checks (native_publication_output who)
          codeEq ∧
      ∀ (store : EventGraph.Store nativeGraph.layout) (bit : Bool),
        (nativeBindingRef who).get? store = some (.success bit) →
        EventGraph.EventCode.resolveOutput? (nativeBindingRef who) checks true store =
          some (.success bit) := by
  fin_cases who <;> refine ⟨_, rfl, rfl, ?_⟩ <;> intro store bit stored <;>
    simp only [EventGraph.EventCode.resolveOutput?, stored] <;> rfl

theorem native_opening_accepted (state : State nativeGraph) (who : Player) (bit : Bool)
    (candidate : Handle nativeGraph)
    (ready : state.config.cut.Ready (nativePublicationEvent who))
    (timely : state.WithinDeadline nativeRuntime (nativePublicationEvent who))
    (owned : candidate.1 = who)
    (associated : state.accepted (nativeBindingRef who).field = some candidate)
    (verified : state.candidates.lookup candidate = .openable ⟨.bool, bit⟩)
    (stored : (nativeBindingRef who).get? state.config.store = some (.success bit))
    (serial : Nat) :
    ∃ next, handle nativeRuntime state
        ⟨(who, serial), .opening (nativePublicationEvent who) candidate ⟨.bool, bit⟩⟩ =
          some next ∧
      (nativePublicationRef who).get? next.config.store = some (.success bit) := by
  obtain ⟨checks, codeEq, node, resolves⟩ := native_publication_rule who
  refine ⟨_, handle_opening_eq nativeRuntime state (who, serial) (nativePublicationEvent who)
    candidate who .bool (nativeBindingRef who) checks (native_publication_output who)
    codeEq node ready timely rfl owned associated bit verified stored (.success bit)
    (resolves state.config.store bit stored), ?_⟩
  fin_cases who <;> simp [nativePublicationRef, nativePublicationEvent, State.complete,
    EventGraph.Config.store, EventGraph.FieldRef.get?]

open Classical in
/-- Ordinary opening is chosen from the player's own value and the public
accepted association. The fallback keeps this a legal response at every input. -/
def nativeOpeningResponse (who : Player) (view : (serviceApp observation).PlayerView) : (serviceApp
  observation).Action :=
  match (nativeBindingRef who).get? view.application.observation.store,
      view.application.publicView.accepted (nativeBindingRef who).field with
  | some (.success bit), some candidate =>
      if nativeBounds.AllowsHandle candidate then
        nativeOpeningAction (nativePublicationEvent who) candidate bit
      else ⟨none⟩
  | _, _ => ⟨none⟩

theorem native_opening_response_available (who : Player)
    (past : List (serviceApp observation).PlayerEntry) (view : (serviceApp observation).PlayerView)
      :
    nativeOpeningResponse who view ∈ (serviceMenu observation).actions who past view := by
  have silent : (⟨none⟩ : (serviceApp observation).Action) ∈ (serviceMenu observation).actions who
    past view := by
    change (⟨none⟩ : (serviceApp observation).Action) ∈
      (nativeBounds.rawMenu nativeRuntime observation).actions who past view
    rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    trivial
  unfold nativeOpeningResponse
  split
  · split
    · exact native_opening_available who _ _ _ ‹_› past view
    · exact silent
  · exact silent

def nativeOpenPolicy (who : Player) : (serviceApp observation).Policy :=
  fun _ view => FinDist.pure (nativeOpeningResponse who view)

theorem native_opening_response_eq (execution : (serviceApp observation).Execution) (who : Player)
    (candidate : Handle nativeGraph) (bit : Bool)
    (allowed : nativeBounds.AllowsHandle candidate)
    (associated : execution.application.accepted (nativeBindingRef who).field = some candidate)
    (stored : (nativeBindingRef who).get? execution.application.config.store =
      some (.success bit)) :
    nativeOpeningResponse who (execution.observe (serviceApp observation) who) =
      nativeOpeningAction (nativePublicationEvent who) candidate bit := by
  classical
  have observed : (nativeBindingRef who).get?
      (execution.observe (serviceApp observation) who).application.observation.store = some
        (.success bit) := by
    change (nativeBindingRef who).get?
      (nativeGraph.playerStore who execution.application.config.store) = _
    rw [(nativeBindingRef who).get?_playerStore who _ rfl, stored]
  have associatedObserved : (execution.observe (serviceApp observation)
    who).application.publicView.accepted
      (nativeBindingRef who).field = some candidate := associated
  simp only [nativeOpeningResponse, observed, associatedObserved, ite_eq_left allowed]

/-- Every successful owned binding admits the same observation-based response.
No premise restricts earlier messages, prior mistakes, or other players. -/
theorem native_opening_response_realizes (players : Player → (serviceApp observation).Policy)
    (execution : (serviceApp observation).Execution) (who : Player) (bit : Bool)
    (valid : execution.application.BindingInvariant)
    (bounded : nativeBounds.AcceptedHandles execution.application)
    (serials : execution.network.SerialsBeforeNext)
    (ready : execution.application.config.cut.Ready (nativePublicationEvent who))
    (timely : execution.application.WithinDeadline nativeRuntime (nativePublicationEvent who))
    (stored : (nativeBindingRef who).get? execution.application.config.store =
      some (.success bit)) :
    ∃ next, (nativePublicationRef who).get? next.config.store = some (.success bit) ∧
      (nativeRuntime.interactionStep observation players (serviceNetwork observation)
        (.includeLatest (nativePublicationEvent who) who)
        (execution.respond (serviceApp observation) who
          (nativeOpeningResponse who (execution.observe (serviceApp observation) who)))).map
            (fun result => result.application) = FinDist.pure next := by
  obtain ⟨candidate, associated, owned, verified⟩ :=
    valid.success_provenance (nativeBindingRef who) bit stored
  have allowed := bounded _ candidate associated
  obtain ⟨next, accepted, published⟩ := native_opening_accepted execution.application who
    bit candidate ready timely owned associated verified stored (execution.network.nextSerial who)
  refine ⟨next, published, ?_⟩
  rw [native_opening_response_eq execution who candidate bit allowed associated stored]
  exact native_opening_inclusion players execution who (nativePublicationEvent who) candidate bit
    next serials accepted

end VegasTests.SelectiveAssociation
