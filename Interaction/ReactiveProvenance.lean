/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetworkInvariant
import Interaction.ReactiveRecall

/-! # Every retained envelope has an actual author submission

Replay retains the original author's envelope. The broadcaster's input record
does not make that broadcaster its author. Origins are actual submission
entries in the author's private recall, with the emitted envelope and payload.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def Execution.Issued (execution : app.Execution) (message : Message Principal app.Payload) : Prop :=
  ∃ entry ∈ execution.recall message.sender, ∃ material,
    entry.action.transmission = some (.submit material) ∧ entry.emitted = some message ∧
      ∃ state known, app.packet state message.sender known material = message.payload

def Execution.Provenance (execution : app.Execution) : Prop :=
  execution.network.Satisfies (execution.Issued app)

omit [DecidableEq Principal] in
theorem Issued.mono {before after : app.Execution}
    (recall : ∀ who, before.recall who ⊆ after.recall who)
    {message : Message Principal app.Payload} (issued : before.Issued app message) :
    after.Issued app message := by
  obtain ⟨entry, member, material, transmission, emitted, packet⟩ := issued
  exact ⟨entry, recall message.sender member, material, transmission, emitted, packet⟩

theorem respond_provenance (execution : app.Execution) (who : Principal) (action : app.Action)
    (valid : execution.Provenance app) : (execution.respond app who action).Provenance app := by
  have prior : execution.network.Satisfies ((execution.respond app who action).Issued app) :=
    valid.mono fun _ issued => Issued.mono app
      (fun observer => app.respond_recall_mono execution who observer action) issued
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact prior
  | some transmission =>
      cases transmission with
      | replay id => exact prior.replay who id
      | submit material =>
          apply prior.submit who
            (app.packet (app.submit execution.application who material) who
              (execution.network.known who) material)
          refine ⟨⟨execution.observe app who, ⟨some (.submit material)⟩,
            some ⟨(who, execution.network.nextSerial who),
              app.packet (app.submit execution.application who material) who
                (execution.network.known who) material⟩⟩, ?_,
            material, rfl, rfl, _, _, rfl⟩
          simp only [Execution.respond, Message.sender, MessageNetwork.submit, ↓reduceIte]
          exact List.mem_append_right _ (List.mem_singleton_self _)

theorem environment_provenance (execution next : app.Execution) (command : app.Command)
    (valid : execution.Provenance app)
    (reached : next ∈ (execution.environmentStep app command).support) : next.Provenance app := by
  have same : next.Issued app = execution.Issued app := by
    funext message
    simp only [Execution.Issued, app.environmentStep_recall execution next command reached]
  change next.network.Satisfies (next.Issued app)
  rw [same]
  cases command with
  | wait =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact valid.learn who selected
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      have kept := valid.includePending id
      cases found : execution.network.lookup id <;>
        simpa only [Execution.includePending, MessageNetwork.includePending, found] using kept
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact valid

def provenance : app.ProtocolState → Prop
  | none => True
  | some control => control.execution.Provenance app

theorem transition_provenance (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (before after : app.ProtocolState)
    (joint : Principal → Option app.Action) (valid : app.provenance before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.provenance after := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ reached
      exact MessageNetwork.Satisfies.empty
  | some control =>
      rcases control with ⟨remaining, current, execution⟩
      cases current with
      | some who =>
          cases FinDist.mem_support_pure.mp reached
          exact app.respond_provenance execution who _ valid
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, _, supported⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := FinDist.support_map .. ▸ supported
              exact app.environment_provenance execution next command valid moved

/-- Every legal initialized history authenticates every retained envelope
against an actual submission in its author's recall. -/
theorem history_provenance (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state), app.provenance state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      app.transition_provenance initial horizon scheduler _ _ joint
        (history_provenance initial horizon scheduler prior) reached

end Interaction.ReactiveApplication
