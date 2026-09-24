/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationNative
import Vegas.Pending.ReactiveDisclosure
import Vegas.Pending.ReactiveEvidence
import Interaction.ReactiveEvidenceKnowledge

/-! # The disclosure compiler and native certificate agree on rejected openings

The actual deferred-guard witness still publishes failure. Its compiled
disclosure now sends the opening, and the generic receipt decoder records the
binding as evidence. The observation rule is arbitrary throughout.
-/

noncomputable section

namespace VegasTests.CommunicationNative

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Math.Probability
open SequentialValidation

variable (leaks : MessageNetwork.ObservationRule Bool (Payload nativeGraph))

def fact (bit : Bool) : EventGraph.CommitmentEvidence nativeGraph :=
  ⟨false, .bool, nativeSecretBinding, bit⟩

theorem compiled_packet (bit : Bool) :
    (nativeRuntime.reactiveDecision leaks false secretEvent true
      ((nativeRuntime.reactiveApplication leaks).observePlayer
        (nativeDummyPublished bit) false)).transmission = some (.submit (secretOpening bit)) := by
  have packet := reactiveResolutionPacket_opening false secretEvent .bool nativeSecretBinding
    rfl true ((nativeRuntime.reactiveApplication leaks).observePlayer
      (nativeDummyPublished bit) false) rfl bit
    (by
      change nativeSecretBinding.get?
        (nativeGraph.playerStore false (nativeDummyPublished bit).config.store) = _
      rw [nativeSecretBinding.get?_playerStore false _ rfl, native_dummy_stored])
    (false, .initial secretInput) (native_dummy_associated bit) rfl
  simp only [reactiveDecision, native_secret_node, packet, secretOpening]

theorem decoded_fact (bit : Bool) :
    (secretOpening bit).packet.bindingEvidence = [fact bit] := by
  simp only [secretOpening, Payload.bindingEvidence, native_secret_node, Raw.as?_mk]
  rfl

def submitted (bit : Bool) : (nativeRuntime.reactiveApplication leaks).Execution :=
  (ReactiveApplication.Execution.initial (nativeRuntime.reactiveApplication leaks)
    (nativeDummyPublished bit)).respond (nativeRuntime.reactiveApplication leaks) false
      ⟨some (.submit (secretOpening bit))⟩

def included (bit : Bool) : (nativeRuntime.reactiveApplication leaks).Execution :=
  (submitted leaks bit).includePending (nativeRuntime.reactiveApplication leaks) (false, 0)

private theorem handle_secret (bit : Bool) (serial : Nat) :
    handle nativeRuntime (nativeDummyPublished bit)
      ⟨(false, serial), .opening secretEvent (false, .initial secretInput) ⟨.bool, bit⟩⟩ =
        some (nativeSecretState bit) :=
  handle_opening_eq nativeRuntime (nativeDummyPublished bit) (false, serial) secretEvent
    (false, .initial secretInput) false .bool nativeSecretBinding nativeSecretChecks rfl rfl
    native_secret_node (native_dummy_ready bit) (native_dummy_timely bit) rfl rfl
    (native_dummy_associated bit) bit (native_dummy_candidate bit) (native_dummy_stored bit)
    .failure (native_secret_result bit)

theorem included_application (bit : Bool) :
    (included leaks bit).application = nativeSecretState bit := by
  simp [included, submitted, ReactiveApplication.Execution.initial,
    ReactiveApplication.Execution.respond, ReactiveApplication.Execution.includePending,
    MessageNetwork.empty, MessageNetwork.submit, MessageNetwork.includePending,
    MessageNetwork.lookup, reactiveApplication, secretOpening, Submission.register,
    submitStep_opening, handle_secret]

/-- A successful native receipt carries evidence even though publication fails. -/
theorem observed_fact (bit who : Bool) :
    fact bit ∈ (nativeRuntime.receiptEvidence leaks).observe
      ((included leaks bit).observe (nativeRuntime.reactiveApplication leaks) who) := by
  simp [included, submitted, ReactiveApplication.Execution.initial,
    ReactiveApplication.Execution.respond, ReactiveApplication.Execution.includePending,
    ReactiveApplication.Execution.observe, ReactiveApplication.ReceiptEvidence.observe,
    ReactiveApplication.ReceiptEvidence.observations,
    MessageNetwork.empty, MessageNetwork.submit, MessageNetwork.includePending,
    MessageNetwork.lookup, MessageNetwork.observe, reactiveApplication, secretOpening,
    Submission.register, submitStep_opening, handle_secret, receiptEvidence,
    Payload.bindingEvidence, native_secret_node, fact]

theorem failed_publication (bit : Bool) :
    (included leaks bit).application.config.store (.inr secretEvent) = some .failure := by
  rw [included_application]
  rfl

/-- All native information fibers that receive this certificate satisfy the
binding fact; the theorem is independent of beliefs, utility and prior play. -/
theorem all_compatible_bindings
    (menu : (nativeRuntime.reactiveApplication leaks).ResponseMenu)
    (initial : FinDist (EventGraphRuntime.State nativeGraph)) (horizon : Nat)
    (scheduler : (nativeRuntime.reactiveApplication leaks).Scheduler) (who bit : Bool)
    (past : List (nativeRuntime.reactiveApplication leaks).PlayerEntry)
    (view : (nativeRuntime.reactiveApplication leaks).PlayerView)
    (received : fact bit ∈ (nativeRuntime.receiptEvidence leaks).observe view) :
    (menu.information initial horizon scheduler).Knows who (some (past, view))
      (fun history => ReactiveApplication.stateInvariant
        (app := nativeRuntime.reactiveApplication leaks)
        (fun state => (fact bit).Holds state.config.store) history.state) :=
  (nativeRuntime.receiptEvidence leaks).knows_observed_menu menu initial horizon scheduler
    who past view (fact bit) received

end VegasTests.CommunicationNative
