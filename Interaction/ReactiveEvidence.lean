/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveReceipts

/-! # Persistent facts certified by application receipts

Decoding is a function of visible packets and receipts. Soundness is proved
against the current application state, after arbitrary later submissions and
service steps. Inclusion success and the application's game result are distinct.
Pending packets and unsuccessful receipts do not supply certificates here.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

structure ReceiptEvidence where
  Fact : Type
  valid : app.State → Fact → Prop
  decode : app.Payload → List Fact
  persists : ∀ fact, app.Invariant (fun state => valid state fact)
  checked : ∀ state message next, app.handle state message = some next →
    ∀ fact ∈ decode message.payload, valid next fact

namespace ReceiptEvidence

variable {app} (evidence : app.ReceiptEvidence)

def observations (messages : List (Message Principal app.Payload))
    (receipts : List (MessageId Principal × Bool)) : List evidence.Fact :=
  (messages.zip receipts).flatMap fun pair =>
    if pair.2.2 then evidence.decode pair.1.payload else []

def observe (view : app.PlayerView) : List evidence.Fact :=
  evidence.observations view.messages.ledger view.receipts

def Sound (execution : app.Execution) : Prop :=
  execution.ReceiptsSound app (fun packet =>
    ∀ fact ∈ evidence.decode packet, evidence.valid execution.application fact)

theorem sound_initial (state : app.State) : evidence.Sound (Execution.initial app state) :=
  List.Forall₂.nil

private theorem sound_mono (execution : app.Execution) (next : app.State)
    (sound : evidence.Sound execution)
    (preserved : ∀ fact, evidence.valid execution.application fact → evidence.valid next fact) :
    execution.ReceiptsSound app (fun packet =>
      ∀ fact ∈ evidence.decode packet, evidence.valid next fact) := by
  apply List.Forall₂.imp _ sound
  intro message receipt valid
  exact ⟨valid.1, fun accepted fact member => preserved fact (valid.2 accepted fact member)⟩

theorem observed_valid (execution : app.Execution) (who : Principal)
    (sound : evidence.Sound execution) (fact : evidence.Fact)
    (observed : fact ∈ evidence.observe (execution.observe app who)) :
    evidence.valid execution.application fact := by
  obtain ⟨⟨message, id, accepted⟩, member, decoded⟩ := List.mem_flatMap.mp observed
  cases accepted with
  | false => simp at decoded
  | true => exact (List.forall₂_zip sound member).2 rfl fact decoded

variable [DecidableEq Principal]

theorem sound_respond (execution : app.Execution) (who : Principal) (action : app.Action)
    (sound : evidence.Sound execution) : evidence.Sound (execution.respond app who action) := by
  apply app.receiptsSound_respond _ execution who action
  exact evidence.sound_mono execution _ sound
    (fun fact => (evidence.persists fact).respond execution who action)

theorem sound_includePending (execution : app.Execution) (id : MessageId Principal)
    (sound : evidence.Sound execution) : evidence.Sound (execution.includePending app id) := by
  have prior := evidence.sound_mono execution
    (execution.includePending app id).application sound
    (fun fact => (evidence.persists fact).includePending execution id)
  unfold Execution.includePending MessageNetwork.includePending at prior ⊢
  cases found : execution.network.lookup id with
  | none => simpa only [found] using sound
  | some message =>
      simp only [found] at prior ⊢
      have addressed : message.id = id := by
        have identified := (List.find?_eq_some_iff_append.mp found).1
        simpa only [decide_eq_true_eq] using identified
      apply List.rel_append prior
      refine List.Forall₂.cons ⟨addressed.symm, ?_⟩ List.Forall₂.nil
      intro accepted fact decoded
      obtain ⟨next, handled⟩ := Option.isSome_iff_exists.mp accepted
      rw [handled]
      exact evidence.checked execution.application message next handled fact decoded

theorem sound_environment (execution next : app.Execution) (command : app.Command)
    (sound : evidence.Sound execution)
    (reached : next ∈ (execution.environmentStep app command).support) : evidence.Sound next := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact sound
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact sound
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact evidence.sound_includePending execution id sound
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := FinDist.support_map .. ▸ supported
      exact evidence.sound_mono execution state sound
        (fun fact valid => (evidence.persists fact).environment _ command state valid changed)

theorem serviceInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler evidence.Sound where
  respond := evidence.sound_respond
  environment execution next command sound _ reached :=
    evidence.sound_environment execution next command sound reached

/-- All legal histories, without restrictions on players or scheduling. -/
theorem history_sound (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {state} (trace : (app.protocol initial horizon scheduler).Trace state) :
    ReactiveApplication.serviceInvariant evidence.Sound state :=
  (evidence.serviceInvariant scheduler).history initial horizon
    (fun state _ => evidence.sound_initial state) trace

end ReceiptEvidence
end Interaction.ReactiveApplication
