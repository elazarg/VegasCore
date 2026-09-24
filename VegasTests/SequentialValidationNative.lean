/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationSource
import Vegas.Compile.EventGraphAssembly
import Vegas.Pending.ReactiveDependencyService

/-! # A validated opening with a failed publication in the compiled graph -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.SourceProgram Vegas.EventGraphRuntime Interaction
open GameTheory.Math.Probability

abbrev nativeGraph := sourceSetup.eventGraph

def bindingEvent : nativeGraph.EventId := ⟨0, by decide⟩
def dummyEvent : nativeGraph.EventId := ⟨1, by decide⟩
def secretEvent : nativeGraph.EventId := ⟨2, by decide⟩
def guessEvent : nativeGraph.EventId := ⟨3, by decide⟩
def secretInput : nativeGraph.InputId := ⟨1, by decide⟩
def guessInput : nativeGraph.InputId := ⟨2, by decide⟩

def nativeRuntime : EventGraphRuntime nativeGraph where
  deadline _ := 10

def nativeStart (bit : Bool) : EventGraphRuntime.State nativeGraph :=
  .initial (sourceSetup.eventInputs (initialState bit))

def nativeSubmit (state : EventGraphRuntime.State nativeGraph) (who : Bool) (serial : Nat)
    (submission : Submission nativeGraph) : Option (EventGraphRuntime.State nativeGraph) :=
  handle nativeRuntime (submitStep (submission.register state who) who submission.packet)
    ⟨(who, serial), submission.packet⟩

def dummySubmission : Submission nativeGraph :=
  ⟨.commitment bindingEvent (false, .prepared 0), some ⟨.bool, false⟩⟩

def dummyOpening : Submission nativeGraph :=
  ⟨.opening dummyEvent (false, .prepared 0) ⟨.bool, false⟩, none⟩

def secretOpening (bit : Bool) : Submission nativeGraph :=
  ⟨.opening secretEvent (false, .initial secretInput) ⟨.bool, bit⟩, none⟩

def nativeRegistered (bit : Bool) : EventGraphRuntime.State nativeGraph :=
  dummySubmission.register (nativeStart bit) false

theorem native_binding_node : nodeView nativeGraph bindingEvent =
    .bind false .bool (by rfl) (by rfl) := by rfl

theorem native_registered_ready (bit : Bool) :
    (nativeRegistered bit).config.cut.Ready bindingEvent := by cases bit <;> decide

theorem native_registered_timely (bit : Bool) :
    (nativeRegistered bit).WithinDeadline nativeRuntime bindingEvent := by
  have entered : (nativeRegistered bit).activatedAt bindingEvent = some 0 := by
    have ready : (nativeStart bit).config.cut.Ready bindingEvent := native_registered_ready bit
    change State.refreshActivated (graph := nativeGraph)
      (nativeStart bit).config 0 (fun _ => none) bindingEvent = some 0
    rw [State.refreshActivated, dite_eq_left ready]
    rfl
  rw [State.WithinDeadline, entered]
  exact Nat.zero_lt_succ 9

theorem native_registered_vacant (bit : Bool) :
    (nativeRegistered bit).accepted (.inr bindingEvent) = none := by rfl

theorem native_registered_unused (bit : Bool) :
    (nativeRegistered bit).HandleUnused (false, .prepared 0) := by
  intro field
  cases field with
  | inl input => cases bit <;> fin_cases input <;> decide
  | inr event => change (none : Option (Handle nativeGraph)) ≠ some _; simp

theorem native_registered_value (bit : Bool) :
    (nativeRegistered bit).bindingResult (false, .prepared 0) .bool = .success false := by
  simp [State.bindingResult, nativeRegistered, dummySubmission, Submission.register,
    CommitmentCandidates.lookup_prepare_self, nativeStart, State.initial_candidate, Raw.as?]

def nativeBoundState (bit : Bool) : EventGraphRuntime.State nativeGraph :=
  { (nativeRegistered bit).complete bindingEvent (native_registered_ready bit)
      (.success false) (.success false) with
    accepted := Function.update (nativeRegistered bit).accepted (.inr bindingEvent)
      (some (false, .prepared 0))
    candidates := (nativeRegistered bit).candidates.freeze (false, .prepared 0) }

theorem native_binding_law (bit : Bool) :
    nativeSubmit (nativeStart bit) false 0 dummySubmission = some (nativeBoundState bit) := by
  unfold nativeSubmit
  rw [handle_submitStep]
  have law := handle_commitment_eq nativeRuntime (nativeRegistered bit) (false, 0)
    bindingEvent (false, .prepared 0) false .bool rfl rfl native_binding_node
    (native_registered_ready bit) (native_registered_timely bit) rfl rfl
    (native_registered_vacant bit) (native_registered_unused bit)
  change handle nativeRuntime (nativeRegistered bit)
    ⟨(false, 0), .commitment bindingEvent (false, .prepared 0)⟩ = some (nativeBoundState bit)
  rw [law]
  simp only [native_registered_value]
  rfl

def nativeBound (bit : Bool) : EventGraphRuntime.State nativeGraph :=
  (nativeSubmit (nativeStart bit) false 0 dummySubmission).getD (nativeStart bit)

theorem nativeBound_eq (bit : Bool) : nativeBound bit = nativeBoundState bit := by
  rw [nativeBound, native_binding_law]
  rfl

def nativeDummyPublished (bit : Bool) : EventGraphRuntime.State nativeGraph :=
  (nativeSubmit (nativeBound bit) false 1 dummyOpening).getD (nativeBound bit)

def nativeSecretPublished (bit : Bool) : EventGraphRuntime.State nativeGraph :=
  (nativeSubmit (nativeDummyPublished bit) false 2 (secretOpening bit)).getD
    (nativeDummyPublished bit)

def nativeDummyBinding : EventGraph.FieldRef nativeGraph.layout (.binding false .bool) :=
  ⟨.inr bindingEvent, rfl⟩

theorem native_dummy_node : nodeView nativeGraph dummyEvent =
    .resolve false .bool nativeDummyBinding [] (by rfl) (by rfl) := by rfl

theorem native_bound_ready (bit : Bool) :
    (nativeBound bit).config.cut.Ready dummyEvent := by
  rw [nativeBound_eq]
  cases bit <;> decide

theorem native_bound_timely (bit : Bool) :
    (nativeBound bit).WithinDeadline nativeRuntime dummyEvent := by
  rw [nativeBound_eq]
  have ready := native_bound_ready bit
  rw [nativeBound_eq] at ready
  have actor : nativeGraph.actor? dummyEvent = some false := rfl
  change (match State.refreshActivated (nativeBoundState bit).config 0
      (nativeRegistered bit).activatedAt dummyEvent with
    | none => False | some entered => 0 - entered < 10)
  rw [State.refreshActivated, dite_eq_left ready, actor]
  cases (nativeRegistered bit).activatedAt dummyEvent <;> simp

theorem native_bound_associated (bit : Bool) :
    (nativeBound bit).accepted nativeDummyBinding.field = some (false, .prepared 0) := by
  rw [nativeBound_eq]
  change Function.update (nativeRegistered bit).accepted (.inr bindingEvent)
    (some (false, .prepared 0)) (.inr bindingEvent) = _
  exact Function.update_self ..

theorem native_bound_candidate (bit : Bool) :
    (nativeBound bit).candidates.lookup (false, .prepared 0) = .openable ⟨.bool, false⟩ := by
  rw [nativeBound_eq]
  simp [nativeBoundState, nativeRegistered, dummySubmission, Submission.register,
    CommitmentCandidates.lookup_freeze_self, CommitmentCandidates.lookup_prepare_self,
    nativeStart, State.initial_candidate]

theorem native_bound_stored (bit : Bool) :
    nativeDummyBinding.get? (nativeBound bit).config.store = some (.success false) := by
  rw [nativeBound_eq]
  rfl

theorem native_dummy_result (bit : Bool) :
    EventGraph.EventCode.resolveOutput? nativeDummyBinding [] true (nativeBound bit).config.store =
      some (.success false) := by
  simp [EventGraph.EventCode.resolveOutput?, native_bound_stored,
    EventGraph.GuardCheck.allAccepted?]

def nativeDummyState (bit : Bool) : EventGraphRuntime.State nativeGraph :=
  (nativeBound bit).complete dummyEvent (native_bound_ready bit) true (.success false)

theorem native_dummy_law (bit : Bool) :
    nativeSubmit (nativeBound bit) false 1 dummyOpening = some (nativeDummyState bit) := by
  unfold nativeSubmit
  rw [handle_submitStep]
  exact handle_opening_eq nativeRuntime (nativeBound bit) (false, 1) dummyEvent
    (false, .prepared 0) false .bool nativeDummyBinding [] rfl rfl native_dummy_node
    (native_bound_ready bit) (native_bound_timely bit) rfl rfl
    (native_bound_associated bit) false (native_bound_candidate bit) (native_bound_stored bit)
    (.success false) (native_dummy_result bit)

theorem nativeDummyPublished_eq (bit : Bool) : nativeDummyPublished bit = nativeDummyState bit :=
  by rw [nativeDummyPublished, native_dummy_law]; rfl

def nativeSecretBinding : EventGraph.FieldRef nativeGraph.layout (.binding false .bool) :=
  ⟨.inl secretInput, rfl⟩

def nativeSecretChecks : List (EventGraph.GuardCheck nativeGraph.layout (.bool : BaseTy)) :=
  match nativeGraph.nodes secretEvent with
  | .resolve _ _ _ checks => checks

theorem native_secret_node : nodeView nativeGraph secretEvent =
    .resolve false .bool nativeSecretBinding nativeSecretChecks (by rfl) (by rfl) := by rfl

theorem native_dummy_ready (bit : Bool) :
    (nativeDummyPublished bit).config.cut.Ready secretEvent := by
  simp only [nativeDummyPublished_eq, nativeDummyState, nativeBound_eq]
  cases bit <;> decide

theorem native_bound_clock (bit : Bool) : (nativeBound bit).clock = 0 := by
  rw [nativeBound_eq]
  rfl

theorem native_dummy_timely (bit : Bool) :
    (nativeDummyPublished bit).WithinDeadline nativeRuntime secretEvent := by
  have ready := native_dummy_ready bit
  rw [nativeDummyPublished_eq] at ready ⊢
  have actor : nativeGraph.actor? secretEvent = some false := rfl
  change (match State.refreshActivated (nativeDummyState bit).config (nativeBound bit).clock
      (nativeBound bit).activatedAt secretEvent with
    | none => False | some entered => (nativeBound bit).clock - entered < 10)
  rw [State.refreshActivated, dite_eq_left ready, actor, native_bound_clock]
  cases (nativeBound bit).activatedAt secretEvent <;> simp

theorem native_dummy_associated (bit : Bool) :
    (nativeDummyPublished bit).accepted nativeSecretBinding.field =
      some (false, .initial secretInput) := by
  simp only [nativeDummyPublished_eq, nativeDummyState, State.complete, nativeBound_eq]
  rfl

theorem native_dummy_candidate (bit : Bool) :
    (nativeDummyPublished bit).candidates.lookup (false, .initial secretInput) =
      .openable ⟨.bool, bit⟩ := by
  simp only [nativeDummyPublished_eq, nativeDummyState, State.complete, nativeBound_eq]
  cases bit <;> rfl

theorem native_dummy_stored (bit : Bool) :
    nativeSecretBinding.get? (nativeDummyPublished bit).config.store = some (.success bit) := by
  simp only [nativeDummyPublished_eq, nativeDummyState, State.complete, nativeBound_eq]
  rfl

theorem native_secret_result (bit : Bool) :
    EventGraph.EventCode.resolveOutput? nativeSecretBinding nativeSecretChecks true
      (nativeDummyPublished bit).config.store = some .failure := by
  simp only [nativeDummyPublished_eq, nativeDummyState, State.complete, nativeBound_eq]
  cases bit <;> rfl

def nativeSecretState (bit : Bool) : EventGraphRuntime.State nativeGraph :=
  (nativeDummyPublished bit).complete secretEvent (native_dummy_ready bit) true .failure

theorem native_secret_law (bit : Bool) :
    nativeSubmit (nativeDummyPublished bit) false 2 (secretOpening bit) =
      some (nativeSecretState bit) := by
  unfold nativeSubmit
  rw [handle_submitStep]
  exact handle_opening_eq nativeRuntime (nativeDummyPublished bit) (false, 2) secretEvent
    (false, .initial secretInput) false .bool nativeSecretBinding nativeSecretChecks rfl rfl
    native_secret_node (native_dummy_ready bit) (native_dummy_timely bit) rfl rfl
    (native_dummy_associated bit) bit (native_dummy_candidate bit) (native_dummy_stored bit)
    .failure (native_secret_result bit)

theorem nativeSecretPublished_eq (bit : Bool) : nativeSecretPublished bit = nativeSecretState bit :=
  by rw [nativeSecretPublished, native_secret_law]; rfl

/-- Packet validation succeeds although the retained guard makes publication fail. -/
theorem native_secret_receipt (bit : Bool) :
    (nativeSubmit (nativeDummyPublished bit) false 2 (secretOpening bit)).isSome = true := by
  rw [native_secret_law]
  rfl

theorem native_secret_failure (bit : Bool) :
    (nativeSecretPublished bit).config.store (.inr secretEvent) = some .failure := by
  rw [nativeSecretPublished_eq]
  rfl

theorem native_binding_receipt (bit : Bool) :
    (nativeSubmit (nativeStart bit) false 0 dummySubmission).isSome = true := by
  unfold nativeSubmit
  rw [handle_submitStep]
  change (handle nativeRuntime (nativeRegistered bit)
    ⟨(false, 0), .commitment bindingEvent (false, .prepared 0)⟩).isSome = true
  simp [handle, native_registered_ready, native_registered_timely, native_binding_node,
    Message.sender, native_registered_vacant, native_registered_unused]

end VegasTests.SequentialValidation
