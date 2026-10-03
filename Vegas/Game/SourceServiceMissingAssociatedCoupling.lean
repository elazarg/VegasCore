/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceMissingStoppedCoupling
import Vegas.Game.SourceServiceUnusableProtectedCall
import Interaction.ReactiveRecovery

/-! # A missing binding's actual protected association supports later fixed reuse

At an actual clear risk-menu input, an absent-opening canonical binding sends
the same publicly acceptable protected packet as a usable binding. If its real
identifier stays sole until completion, the actual accepted association makes
every later commitment of that handle publicly inert.

One owner-input-local continuation waits only when this persistent association
is absent. The association invariant proves its entire original evaluator law
is unchanged on the actual associated continuation. This supplies the global
support needed by the existing fixed-reuse coupling, with no second evaluator
induction or hidden-history policy choice. The result still stops at an actual
signed-content breach and does not assert terminal payoff domination.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

open Classical in
private def associatedPlayers (owner : Player) (field : (graph setup).Field)
    (slot : CandidateSlot (graph setup))
    (players : Player → (application setup leaks).Policy) :
    Player → (application setup leaks).Policy :=
  Function.update players owner (fun past view =>
    if view.application.publicView.accepted field = some (owner, slot) then
      players owner past view else PMF.pure ⟨none⟩)

private theorem associatedPlayers_owner_support
    (owner : Player) (field : (graph setup).Field) (slot : CandidateSlot (graph setup))
    (players : Player → (application setup leaks).Policy)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (response : (application setup leaks).Action)
    (chosen : response ∈ (associatedPlayers owner field slot players owner past view).support) :
    (response ∈ (players owner past view).support ∧
      view.application.publicView.accepted field = some (owner, slot)) ∨
      response = ⟨none⟩ := by
  classical
  simp only [associatedPlayers, Function.update_self] at chosen
  split at chosen
  · exact Or.inl ⟨chosen, ‹_›⟩
  · exact Or.inr ((PMF.mem_support_pure_iff _ _).mp chosen)

private theorem associatedPlayers_runRounds
    (owner : Player) (field : (graph setup).Field) (slot : CandidateSlot (graph setup))
    (players : Player → (application setup leaks).Policy)
    (scheduler : (application setup leaks).Scheduler) (count : Nat)
    (execution : (application setup leaks).Execution)
    (binding : execution.application.BindingInvariant)
    (associated : execution.application.accepted field = some (owner, slot)) :
    (application setup leaks).runRounds scheduler players count execution =
      (application setup leaks).runRounds scheduler (associatedPlayers owner field slot players)
        count execution := by
  classical
  let invariant := (((runtime setup).reactiveAssociationInvariant leaks field
    (owner, slot)).policyInvariant (application setup leaks)) players
  apply invariant.runRounds_congr (associatedPlayers owner field slot players) ?_
    scheduler count execution ⟨binding, associated⟩
  intro next valid actor
  by_cases same : actor = owner
  · subst actor
    simp only [associatedPlayers, Function.update_self]
    change players owner (next.recall owner) (next.observe (application setup leaks) owner) =
      if next.application.accepted field = some (owner, slot) then
        players owner (next.recall owner) (next.observe (application setup leaks) owner)
      else PMF.pure ⟨none⟩
    simp only [valid.2, ↓reduceIte]
  · simp only [associatedPlayers, Function.update_of_ne same]

private theorem associatedPlayers_risk_supported [Fintype Player]
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (owner : Player) (field : (graph setup).Field) (slot : CandidateSlot (graph setup))
    (players : Player → (application setup leaks).Policy)
    (supported : ∀ past view response, response ∈ (players owner past view).support →
      response ∈ bounds.riskActions (runtime setup) leaks bound owner past view) :
    ∀ past view response,
      response ∈ (associatedPlayers owner field slot players owner past view).support →
        response ∈ bounds.riskActions (runtime setup) leaks bound owner past view := by
  intro past view response chosen
  rcases associatedPlayers_owner_support owner field slot players past view response chosen with
    ⟨chosen, _⟩ | rfl
  · exact supported past view response chosen
  · exact bounds.canonicalActions_subset_risk (runtime setup) leaks bound owner past view
      (bounds.silence_canonical (runtime setup) leaks owner past view)

private theorem associatedPlayers_copied
    (owner : Player) (field : (graph setup).Field) (changedSlot : CandidateSlot (graph setup))
    (players : Player → (application setup leaks).Policy)
    (copied : ∀ past view response, response ∈ (players owner past view).support →
      (∀ material, response.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
        FreshOwnedBindingResponse (runtime setup) leaks owner view.application response ∨
        ∃ event slot opening, view.application.candidates slot ≠ .fresh ∧
          response = ⟨some ⟨⟨.commitment event (owner, slot), opening⟩, .none⟩⟩) :
    ∀ past view response,
      response ∈ (associatedPlayers owner field changedSlot players owner past view).support →
        (∀ material, response.transmission = some material →
            ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
          FreshOwnedBindingResponse (runtime setup) leaks owner view.application response ∨
          ∃ event slot opening, view.application.candidates slot ≠ .fresh ∧
            (slot ≠ changedSlot ∨
              ∃ field, view.application.publicView.accepted field = some (owner, slot)) ∧
            response = ⟨some ⟨⟨.commitment event (owner, slot), opening⟩, .none⟩⟩ := by
  intro past view response chosen
  rcases associatedPlayers_owner_support owner field changedSlot players past view response
      chosen with ⟨chosen, associated⟩ | rfl
  · rcases copied past view response chosen with noncommitment | fresh | fixed
    · exact Or.inl noncommitment
    · exact Or.inr (Or.inl fresh)
    · obtain ⟨event, slot, opening, fixed, actual⟩ := fixed
      refine Or.inr (Or.inr ⟨event, slot, opening, fixed, ?_, actual⟩)
      by_cases same : slot = changedSlot
      · subst slot
        exact Or.inr ⟨field, associated⟩
      · exact Or.inl same
  · exact Or.inl (by simp)

variable [Fintype Player]

/-- An actual protected, sole missing-opening call removes the changed-slot
restriction on later bare owned fixed reuse. The implementable continuation
checks the persistent public association and waits off that invariant. Its
original law equals the full ungated law from this actual associated boundary;
the same existing finite coupling supplies the repaired risk-menu evaluator.
The actual signed-breach stop and the terminal-payoff boundary remain explicit. -/
theorem sourceService_missing_risk_associated_stopped_coupling
    (bounds : MessageBounds (graph setup))
    (bound : (graph setup).EventId → Nat) (owner : Player)
    (execution : (application setup leaks).Execution) (remaining : Nat)
    (current : (graph setup).EventId)
    (players : Player → (application setup leaks).Policy)
    (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (inclusion : ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler
      bound)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (clear : (runtime setup).serviceRisk leaks bound owner (execution.recall owner)
      (execution.observe (application setup leaks) owner) = false)
    (unusable : unusableServiceBindingResponse setup leaks owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)
      ⟨some ⟨⟨.commitment current
        (owner, .prepared (execution.application.publicView.bindingCount owner)), none⟩, .none⟩⟩)
    (supported : ∀ past view response, response ∈ (players owner past view).support →
      response ∈ bounds.riskActions (runtime setup) leaks bound owner past view)
    (copied : ∀ past view response, response ∈ (players owner past view).support →
      (∀ material, response.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
        FreshOwnedBindingResponse (runtime setup) leaks owner view.application response ∨
        ∃ event slot opening, view.application.candidates slot ≠ .fresh ∧
          response = ⟨some ⟨⟨.commitment event (owner, slot), opening⟩, .none⟩⟩)
    (prefixPlayers : Player → (application setup leaks).Policy)
    (prefixNoncommitment : ∀ past view response,
      response ∈ (prefixPlayers owner past view).support →
        ∀ material, response.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate)
    (rightPrefixPlayers : Player → (application setup leaks).Policy)
    (rightPrefixNoncommitment : ∀ past view response,
      response ∈ (rightPrefixPlayers owner past view).support →
        ∀ material, response.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate)
    (original repaired : (application setup leaks).Control)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some original))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some repaired))
    (rightOpening : Option (Raw L)) (preparation : Nat)
    (arrival : original.execution ∈ ((application setup leaks).runRounds scheduler prefixPlayers
      preparation (execution.respond (application setup leaks) owner
        ⟨some ⟨⟨.commitment current
          (owner, .prepared (execution.application.publicView.bindingCount owner)), none⟩,
          .none⟩⟩)).support)
    (rightArrival : repaired.execution ∈ ((application setup leaks).runRounds scheduler
      rightPrefixPlayers preparation (execution.respond (application setup leaks) owner
        ⟨some ⟨⟨.commitment current
          (owner, .prepared (execution.application.publicView.bindingCount owner)), rightOpening⟩,
          .none⟩⟩)).support)
    (completed : current ∈ original.execution.application.config.cut.completed)
    (later : List (application setup leaks).PlayerEntry)
    (continued : original.execution.recall owner =
      (execution.respond (application setup leaks) owner
        ⟨some ⟨⟨.commitment current
          (owner, .prepared (execution.application.publicView.bindingCount owner)), none⟩,
          .none⟩⟩).recall owner ++ later)
    (sole : ∀ other ∈ execution.recall owner ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other current
        (owner, execution.network.nextSerial owner))
    (memory : BindingMemory (runtime setup) leaks)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original.execution
      repaired.execution)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.execution.application.config)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.execution.recall owner).length)
    (count : Nat) :
    let app := application setup leaks
    let continuation : app.Policy := fun past view =>
      if view.application.publicView.accepted (.inr current) =
          some (owner, .prepared (execution.application.publicView.bindingCount owner)) then
        players owner past view else PMF.pure ⟨none⟩
    let guardedPlayers := Function.update players owner continuation
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) owner reference continuation
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.runRounds scheduler players count original.execution ∧
      coupling.map Prod.snd = strategy.runJoint owner guardedPlayers scheduler count
        repaired.execution
        memory ∧
      ∀ next ∈ coupling.support,
        (BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings owner ∧
          next.2.2.shadow.CompletedAt next.1.application.config ∧
          OwnerCommitmentsInertOrMatching owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          (next.1.recall owner).map ((runtime setup).submissionRiskRecord leaks) =
            (next.2.1.recall owner).map ((runtime setup).submissionRiskRecord leaks) ∧
          next.1.InputRecall app ∧ next.2.1.InputRecall app ∧
          (∀ slot raw, next.1.application.candidates.lookup (owner, slot) = .openable raw →
            next.2.1.application.candidates.lookup (owner, slot) = .openable raw) ∧
          (∀ bound, (runtime setup).serviceRisk leaks bound owner (next.1.recall owner)
              (next.1.observe app owner) =
            (runtime setup).serviceRisk leaks bound owner (next.2.1.recall owner)
              (next.2.1.observe app owner)) ∧
          ∀ slot, original.execution.application.candidates.lookup (owner, slot) =
              repaired.execution.application.candidates.lookup (owner, slot) →
            next.1.application.candidates.lookup (owner, slot) =
              next.2.1.application.candidates.lookup (owner, slot)) ∨
          ∃ message, message.sender = owner ∧ SignedContentBreach message ∧
            message ∈ next.1.network.inputs ∧ message ∈ next.2.1.network.inputs := by
  classical
  let app := application setup leaks
  let slot : CandidateSlot (graph setup) :=
    .prepared (execution.application.publicView.bindingCount owner)
  let response : app.Action := ⟨some ⟨⟨.commitment current (owner, slot), none⟩, .none⟩⟩
  let before : app.Control := ⟨remaining, some owner, execution⟩
  let guardedPlayers := associatedPlayers owner (.inr current) slot players
  obtain ⟨_payload, _opening, _owned, _output, ready, _unrecorded, _fresh, _fits, _response,
    _missing, _packet, _recalled, _call⟩ :=
    unusableServiceBindingResponse_protected_call bounds bound execution owner trace clear response
      unusable current rfl
  have settled := unusableServiceBindingResponse_completed_association bounds bound inclusion
    execution owner trace clear response unusable current rfl original leftTrace later continued
      sole completed
  have facts := legalFacts setup leaks horizon scheduler original leftTrace
  have same := associatedPlayers_runRounds owner (.inr current) slot players scheduler count
    original.execution facts.binding settled.2.1
  have beforeTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace (initialLaw setup)
    horizon scheduler trace
  obtain ⟨coupling, left, right, valid⟩ := sourceService_missing_risk_fixed_stopped_coupling
    bounds bound owner slot guardedPlayers scheduler horizon
      (associatedPlayers_risk_supported bounds bound owner (.inr current) slot players supported)
      (associatedPlayers_copied owner (.inr current) slot players copied)
      prefixPlayers prefixNoncommitment rightPrefixPlayers rightPrefixNoncommitment
      before original repaired beforeTrace leftTrace rightTrace current ready rightOpening
      preparation arrival rightArrival completed memory frame onlyBindings past reference started
      count
  refine ⟨coupling, left.trans same.symm, ?_, valid⟩
  simpa only [guardedPlayers, associatedPlayers, Function.update_self] using right

end Vegas
