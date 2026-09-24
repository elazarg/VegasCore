/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetworkInvariant
import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveInvariant
import Interaction.ReactiveResponseMenu
import GameTheoryExtensions.Protocol.Knowledge

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

theorem observed_valid (execution : app.Execution) (who : Principal)
    (sound : evidence.Sound execution) (fact : evidence.Fact)
    (observed : fact ∈ evidence.observe (execution.observe app who)) :
    evidence.valid execution.application fact := by
  obtain ⟨message, member, decoded⟩ := List.mem_flatMap.mp observed
  rcases List.mem_append.mp member with leaked | published
  · exact sound.leaked who message leaked fact decoded
  · exact sound.ledger message published fact decoded

variable [DecidableEq Principal]

theorem sound_respond (execution : app.Execution) (who : Principal) (action : app.Action)
    (sound : evidence.Sound execution) : evidence.Sound (execution.respond app who action) := by
  have prior := evidence.sound_mono execution (execution.respond app who action).application sound
    (fun fact => (evidence.persists fact).respond execution who action)
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact sound
  | some transmission =>
      cases transmission with
      | replay id => exact prior.replay who id
      | submit material =>
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
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact sound
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact sound.learn who selected
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

/-- Carried evidence is sound at every history, for arbitrary raw responses
and adaptive scheduling, including all application rejections. -/
theorem history_sound (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {state} (trace : (app.protocol initial horizon scheduler).Trace state) :
    ReactiveApplication.serviceInvariant evidence.Sound state :=
  (evidence.serviceInvariant scheduler).history initial horizon
    (fun state _ => evidence.sound_initial state) trace

/-- A received certificate is true at every history compatible with the
recipient's information, including zero-probability histories of a profile. -/
theorem knows_observed (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView)
    (fact : evidence.Fact) (observed : fact ∈ evidence.observe view) :
    (app.information initial horizon scheduler).Knows who (some (past, view))
      (fun history => stateInvariant (fun state => evidence.valid state fact) history.state) := by
  rintro ⟨⟨state, trace⟩, equal⟩
  change (app.signals initial horizon scheduler).infoOf who trace = some (past, view) at equal
  rw [app.info] at equal
  cases state with
  | none => cases equal
  | some control =>
      change (if control.actor = some who then
        some (control.execution.recall who, control.execution.observe app who)
        else none) = some (past, view) at equal
      split at equal
      · have sameView := congrArg Prod.snd (Option.some.inj equal)
        change control.execution.observe app who = view at sameView
        apply evidence.observed_valid control.execution who
          (evidence.history_sound initial horizon scheduler trace) fact
        exact sameView.symm ▸ observed
      · cases equal

/-- Finite menus inherit the same knowledge guarantee without any profile or
positive-probability premise. -/
theorem knows_observed_menu (menu : app.ResponseMenu) (initial : FinDist app.State)
    (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView)
    (fact : evidence.Fact) (observed : fact ∈ evidence.observe view) :
    (menu.information initial horizon scheduler).Knows who (some (past, view))
      (fun history => stateInvariant (fun state => evidence.valid state fact) history.state) := by
  rintro ⟨⟨state, trace⟩, equal⟩
  change (menu.signals initial horizon scheduler).infoOf who trace = some (past, view) at equal
  rw [ResponseMenu.info] at equal
  cases state with
  | none => cases equal
  | some control =>
      change (if control.actor = some who then
        some (control.execution.recall who, control.execution.observe app who)
        else none) = some (past, view) at equal
      split at equal
      · have sameView := congrArg Prod.snd (Option.some.inj equal)
        change control.execution.observe app who = view at sameView
        apply evidence.observed_valid control.execution who
          (evidence.history_sound initial horizon scheduler
            (menu.toRawTrace initial horizon scheduler trace)) fact
        exact sameView.symm ▸ observed
      · cases equal

end PacketEvidence
end Interaction.ReactiveApplication
