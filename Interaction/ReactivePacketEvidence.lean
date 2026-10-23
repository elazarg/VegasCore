/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetworkInvariant
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveInvariant

/-! # Persistent evidence carried by emitted packets

The emission check uses the post-submission state and actual packets already
possessed by the sender. It allows owner issuance and forwarding without
turning arbitrary guesses into certificates. Evidence remains observable in
pending leaks and the ledger irrespective of application-call acceptance.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

structure PacketEvidence where
  Fact : Type
  valid : app.State → Fact → Prop
  decode : app.Payload → List Fact
  persists : ∀ fact, app.Invariant (fun state => valid state fact)
  issued : ∀ state who known material,
    (∀ message ∈ known, ∀ fact ∈ decode message.payload, valid state fact) →
    ∀ fact ∈ decode (app.packet state who known material), valid state fact

namespace PacketEvidence

variable {app} (evidence : app.PacketEvidence)

def Sound (execution : app.Execution) : Prop :=
  execution.network.Satisfies (fun message =>
    ∀ fact ∈ evidence.decode message.payload, evidence.valid execution.application fact)

def observe (view : app.PlayerView) : List evidence.Fact :=
  (view.messages.leaked ++ view.messages.ledger).flatMap fun message =>
    evidence.decode message.payload

theorem sound_initial (state : app.State) : evidence.Sound (Execution.initial app state) :=
  MessageNetwork.Satisfies.empty

private theorem sound_mono (execution : app.Execution) (next : app.State)
    (sound : evidence.Sound execution)
    (preserved : ∀ fact, evidence.valid execution.application fact → evidence.valid next fact) :
    execution.network.Satisfies (fun message =>
      ∀ fact ∈ evidence.decode message.payload, evidence.valid next fact) :=
  sound.mono fun _ valid fact member => preserved fact (valid fact member)

variable [DecidableEq Principal]

theorem sound_respond (execution : app.Execution) (who : Principal) (action : app.Action)
    (sound : evidence.Sound execution) : evidence.Sound (execution.respond app who action) := by
  have prior := evidence.sound_mono execution (execution.respond app who action).application sound
    (fun fact => (evidence.persists fact).respond execution who action)
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact sound
  | some material =>
      apply prior.submit who
        (app.packet (app.submit execution.application who material) who
          (execution.network.known who) material)
      exact evidence.issued (app.submit execution.application who material) who
        (execution.network.known who) material (fun message member =>
          prior.known who message member)

theorem sound_includePending (execution : app.Execution) (id : MessageId Principal)
    (sound : evidence.Sound execution) : evidence.Sound (execution.includePending app id) := by
  have prior := evidence.sound_mono execution
    (execution.includePending app id).application sound
    (fun fact => (evidence.persists fact).includePending execution id)
  have retained := prior.includePending id
  cases found : execution.network.lookup id <;>
    simpa only [Sound, Execution.includePending, MessageNetwork.includePending, found]
      using retained

theorem sound_environment (execution next : app.Execution) (command : app.Command)
    (sound : evidence.Sound execution)
    (reached : next ∈ (execution.environmentStep app command).support) : evidence.Sound next := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact sound
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact sound.learn who selected
  | «include» id =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact evidence.sound_includePending execution id sound
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact evidence.sound_mono execution state sound
        (fun fact valid => (evidence.persists fact).environment _ command state valid changed)

theorem serviceInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler evidence.Sound where
  respond := evidence.sound_respond
  environment execution next command sound _ reached :=
    evidence.sound_environment execution next command sound reached

/-- Carried evidence is sound at every history, for arbitrary raw responses
and adaptive scheduling, including all application rejections. -/
theorem history_sound (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {state} (trace : (app.protocol initial horizon scheduler).Trace state) :
    ReactiveApplication.serviceInvariant evidence.Sound state :=
  (evidence.serviceInvariant scheduler).history initial horizon
    (fun state _ => evidence.sound_initial state) trace

end PacketEvidence
end Interaction.ReactiveApplication
