/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestricted
import VegasTests.SelectiveAssociationOpeningService
import Vegas.Pending.ReactiveCandidateBudget
import Interaction.ReactiveMenuPolicy
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # A complete prescribed profile for the restricted native service

Prelude responses are silent. Each binding response chooses a still fresh
bounded candidate, so the prescription repairs arbitrary earlier owner
submissions. Alice binds false; the guessers use a public certificate of the
accepted Alice binding when available and otherwise guess false. Each owner
opens its actual accepted value at its publication response.

All responses are members of the original full raw menu. The consistent
completion below supplies beliefs only; optimality of these responses is a
separate obligation.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

theorem silence_available (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView) :
    (⟨none⟩ : app.Action) ∈ menu.actions who past view := by
  change (⟨none⟩ : app.Action) ∈ (nativeBounds.rawMenu nativeRuntime leaks).actions who past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  trivial

def bindingResponse (who : Player) (event : nativeGraph.EventId) (serial : Fin 2)
    (bit : Bool) : app.Action :=
  nativeRuntime.reactiveBinding leaks who event .bool (.success bit) serial.val

theorem bindingResponse_available (who : Player) (event : nativeGraph.EventId)
    (serial : Fin 2) (bit : Bool) (past : List app.PlayerEntry) (view : app.PlayerView) :
    bindingResponse who event serial bit ∈ menu.actions who past view := by
  change bindingResponse who event serial bit ∈
    (nativeBounds.rawMenu nativeRuntime leaks).actions who past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change (⟨⟨.commitment event (who, .prepared serial.val), some ⟨.bool, bit⟩⟩, .none⟩ :
    WitnessedSubmission nativeGraph) ∈ nativeBounds.submissions _
  rw [MessageBounds.submissions_mem]
  refine ⟨⟨serial.isLt, ?_⟩, trivial⟩
  change (⟨.bool, bit⟩ : Raw simpleExpr) ∈ nativeBounds.values
  cases bit <;> decide

open Classical in
def freshSlot (view : app.PlayerView) : Option (Fin 2) :=
  if view.application.candidates (.prepared 0) = .fresh then some 0
  else if view.application.candidates (.prepared 1) = .fresh then some 1 else none

theorem freshSlot_spec (view : app.PlayerView) (slot : Fin 2)
    (selected : freshSlot view = some slot) :
    view.application.candidates (.prepared slot.val) = .fresh := by
  unfold freshSlot at selected
  split at selected
  · cases Option.some.inj selected
    assumption
  · split at selected
    · cases Option.some.inj selected
      assumption
    · cases selected

theorem freshSlot_exists (view : app.PlayerView)
    (available : ∃ slot : Fin 2, view.application.candidates (.prepared slot.val) = .fresh) :
    ∃ slot, freshSlot view = some slot := by
  unfold freshSlot
  split
  · exact ⟨0, rfl⟩
  · split
    · exact ⟨1, rfl⟩
    · obtain ⟨slot, fresh⟩ := available
      fin_cases slot <;> contradiction

def correctiveBinding (who : Player) (event : nativeGraph.EventId) (bit : Bool)
    (view : app.PlayerView) : app.Action :=
  match freshSlot view with
  | none => ⟨none⟩
  | some slot => bindingResponse who event slot bit

theorem correctiveBinding_available (who : Player) (event : nativeGraph.EventId) (bit : Bool)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    correctiveBinding who event bit view ∈ menu.actions who past view := by
  unfold correctiveBinding
  split
  · exact silence_available who past view
  · exact bindingResponse_available who event _ bit past view

def publicGuess (view : app.PlayerView) : Bool :=
  match view.application.publicView.accepted aliceBindingRef.field with
  | none => false
  | some accepted => view.messages.ledger.any fun message =>
      message.payload.evidence.any fun fact =>
        decide (fact.handle = accepted) && (fact.raw.as? .bool).getD false

private theorem raw_true (raw : Raw simpleExpr)
    (decoded : (raw.as? .bool).getD false = true) : raw = ⟨.bool, true⟩ := by
  rcases raw with ⟨payload, value⟩
  unfold Raw.as? at decoded
  split at decoded
  · rename_i same
    change payload = BaseTy.bool at same
    subst payload
    have chosen : value = true := decoded
    subst value
    rfl
  · cases decoded

/-- The prescribed true guess is supported by a public certificate of the
actual accepted binding, rather than by evidence of an unrelated candidate. -/
theorem publicGuess_true_evidence (view : app.PlayerView) (selected : publicGuess view = true) :
    nativeRuntime.bindingEvidenceObserved leaks view ⟨alice, .bool, aliceBindingRef, true⟩ := by
  unfold publicGuess at selected
  cases accepted : view.application.publicView.accepted aliceBindingRef.field with
  | none => simp only [accepted] at selected; cases selected
  | some handle =>
      rw [accepted] at selected
      obtain ⟨message, published, certified⟩ := List.any_eq_true.mp selected
      cases evidence : message.payload.evidence with
      | none => simp [evidence] at certified
      | some fact =>
          simp only [evidence, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at certified
          have factEq : fact = ⟨handle, ⟨.bool, true⟩⟩ := by
            obtain ⟨sameHandle, raw⟩ := certified
            cases fact
            simp only at sameHandle raw ⊢
            cases sameHandle
            exact congrArg (OpeningFact.mk _) (raw_true _ raw)
          refine ⟨handle, accepted, ?_⟩
          apply List.mem_flatMap.mpr
          refine ⟨message, List.mem_append_right _ published, ?_⟩
          change (⟨handle, ⟨.bool, true⟩⟩ : OpeningFact nativeGraph) ∈
            message.payload.evidence.toList
          simp [evidence, factEq]

/-- A true prescribed guess is correct at every history in its information
set. This statement uses actual native evidence soundness, including off-path
histories, and makes no assumption about the assessment's beliefs. -/
theorem publicGuess_true_known (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (selected : publicGuess view = true)
    (history : model.InformationHistory who (some (past, view))) :
    ReactiveApplication.stateInvariant (fun state : State nativeGraph =>
      aliceBindingRef.get? state.config.store = some (.success true)) history.1.state := by
  have known := nativeRuntime.knows_bindingEvidence_menu leaks menu (FinDist.pure nativeInputs)
    nativeHorizon scheduler who past view ⟨alice, .bool, aliceBindingRef, true⟩
      (publicGuess_true_evidence view selected)
  rw [FinDist.map_pure] at known
  exact known history

def openingResponse (who : Player) (view : app.PlayerView) : app.Action := by
  classical
  exact match (nativeBindingRef who).get? view.application.observation.store,
      view.application.publicView.accepted (nativeBindingRef who).field with
    | some (.success bit), some accepted =>
        if nativeBounds.AllowsHandle accepted then
          ⟨some (.submit (nativeOpeningSubmission (nativePublicationEvent who) accepted bit))⟩
        else ⟨none⟩
    | _, _ => ⟨none⟩

theorem openingResponse_available (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) : openingResponse who view ∈ menu.actions who past view := by
  unfold openingResponse
  split
  · rename_i bit accepted _ _
    split
    · rename_i allowed
      change (⟨some (.submit _)⟩ : app.Action) ∈
        (nativeBounds.rawMenu nativeRuntime leaks).actions who past view
      rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
      change nativeOpeningSubmission (nativePublicationEvent who) accepted bit ∈
        nativeBounds.submissions _
      rw [MessageBounds.submissions_mem]
      have value : (⟨.bool, bit⟩ : Raw simpleExpr) ∈ nativeBounds.values := by cases bit <;> decide
      exact ⟨⟨⟨allowed, value⟩, trivial⟩, allowed, value⟩
    · exact silence_available who past view
  · exact silence_available who past view

def response (who : Player) (view : app.PlayerView) : app.Action :=
  match view.application.publicView.serviceGrant with
  | none => ⟨none⟩
  | some event =>
      if who = nativeOwner event then
        if event.val < 3 then
          correctiveBinding who event (if who = alice then false else publicGuess view) view
        else openingResponse who view
      else ⟨none⟩

def policy (who : Player) : app.Policy := fun _ view => FinDist.pure (response who view)

theorem response_available (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView) :
    response who view ∈ menu.actions who past view := by
  unfold response
  split
  · exact silence_available who past view
  · split
    · split
      · exact correctiveBinding_available who _ _ past view
      · exact openingResponse_available who past view
    · exact silence_available who past view

theorem policy_available (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (action : app.Action) (supported : action ∈ (policy who past view).support) :
    action ∈ menu.actions who past view := by
  cases FinDist.mem_support_pure.mp supported
  exact response_available who past view

def profile : Profile model.behavioralSignature := fun who =>
  menu.restrictPolicy (FinDist.pure nativeInitial) nativeHorizon scheduler who (policy who)
    (fun _ _ _ => policy_available who _ _)

/-- Finite native histories admit one consistent completion of this exact
profile. This theorem asserts neither posterior fairness nor optimality. -/
theorem exists_consistent_assessment :
    ∃ assessment : model.BehavioralAssessment, assessment.strategy = profile ∧
      assessment.IsSequentiallyConsistent
        (menu.decisionInformationAntichain (FinDist.pure nativeInitial) nativeHorizon scheduler) :=
  InformationModel.BehavioralAssessment.exists_consistent_completion
    (menu.uniformAssessment (FinDist.pure nativeInitial) nativeHorizon scheduler)
    (menu.uniform_fullyMixed (FinDist.pure nativeInitial) nativeHorizon scheduler)
    (menu.decisionInformationAntichain (FinDist.pure nativeInitial) nativeHorizon scheduler) profile

end VegasTests.SelectiveAssociation.Restricted
