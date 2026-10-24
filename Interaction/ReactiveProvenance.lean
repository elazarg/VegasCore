/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.MessageNetworkInvariant
import Interaction.ReactiveRecall
import Interaction.ReactiveServiceInvariant

/-! # Every retained envelope has an actual author submission

Origins are actual submission entries in the author's private recall, with the
fresh emitted envelope and payload. Passive observation retains the same signed
envelope without creating a new submission or changing its author.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def Execution.Issued (execution : app.Execution) (message : Message Principal app.Payload) : Prop :=
  ∃ entry ∈ execution.recall message.sender, ∃ material,
    entry.action.transmission = some material ∧ entry.emitted = some message ∧
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
  | some material =>
      apply prior.submit who
        (app.packet (app.submit execution.application who material) who
          (execution.network.known who) material)
      refine ⟨⟨execution.observe app who, ⟨some material⟩,
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
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid.learn who selected
  | «include» id =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      have kept := valid.includePending id
      cases found : execution.network.lookup id <;>
        simpa only [Execution.includePending, MessageNetwork.includePending, found] using kept
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid

/-- Actual submission provenance is preserved by unrestricted responses and
every supported command of an arbitrary observation-local scheduler. -/
theorem provenanceInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution => execution.Provenance app) where
  respond := app.respond_provenance
  environment execution next command valid _ reached :=
    app.environment_provenance execution next command valid reached

/-- Every legal initialized history authenticates every retained envelope
against an actual submission in its author's recall. -/
theorem history_provenance (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.Provenance app) state :=
  (app.provenanceInvariant scheduler).history initial horizon
    (fun _ _ => MessageNetwork.Satisfies.empty) trace

end Interaction.ReactiveApplication
