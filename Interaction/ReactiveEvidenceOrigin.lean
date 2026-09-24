/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveEvidencePersistence
import Interaction.ReactiveObservationRestriction

/-! # Foreign certificates require an observation channel

Only the designated owner can issue a fresh fact; other senders may copy facts
from packets they already possess. At every initialized history, possession
of a foreign certificate therefore requires a certificate in the recipient's
leaked packets or in the public ledger. Own output memory, forwarding and
replay cannot create a third acquisition channel.

This is a provenance statement about carried certificates. It does not claim
that every inference about a hidden value requires a certificate.
-/

noncomputable section

namespace Interaction.ReactiveApplication.PacketEvidence

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (evidence : app.PacketEvidence) (owner : evidence.Fact → Principal)

/-- The emission interface can issue owned facts or copy possessed facts. -/
def OwnerIssued : Prop :=
  ∀ state who known material fact, fact ∈ evidence.decode (app.packet state who known material) →
    owner fact = who ∨ ∃ message ∈ known, fact ∈ evidence.decode message.payload

/-- Every input carrying a foreign fact is backed by the broadcaster's
observable evidence. The input may be a replay rather than an original issue. -/
def InputOrigin (execution : app.Execution) : Prop :=
  ∀ input ∈ execution.network.inputs, ∀ fact ∈ evidence.decode input.envelope.payload,
    owner fact = input.broadcaster ∨
      fact ∈ evidence.observe (execution.observe app input.broadcaster)

theorem known_origin (execution : app.Execution)
    (origin : evidence.InputOrigin owner execution) (who : Principal)
    (message : Message Principal app.Payload) (known : message ∈ execution.network.known who)
    (fact : evidence.Fact) (carried : fact ∈ evidence.decode message.payload) :
    owner fact = who ∨ fact ∈ evidence.observe (execution.observe app who) := by
  simp only [MessageNetwork.known, List.mem_append] at known
  rcases known with (input | leaked) | published
  · obtain ⟨record, retained, selected⟩ := List.mem_filterMap.mp input
    split at selected
    · rename_i same
      cases Option.some.inj selected
      simpa only [same] using origin record retained fact carried
    · cases selected
  · exact Or.inr (List.mem_flatMap.mpr
      ⟨message, List.mem_append_left _ leaked, carried⟩)
  · exact Or.inr (List.mem_flatMap.mpr
      ⟨message, List.mem_append_right _ published, carried⟩)

omit [DecidableEq Principal] in
theorem inputOrigin_initial (state : app.State) :
    evidence.InputOrigin owner (Execution.initial app state) := by
  intro input retained
  cases retained

theorem inputOrigin_respond (issued : evidence.OwnerIssued owner)
    (execution : app.Execution) (actor : Principal) (action : app.Action)
    (origin : evidence.InputOrigin owner execution) :
    evidence.InputOrigin owner (execution.respond app actor action) := by
  have prior (input : NetworkInput Principal app.Payload)
      (retained : input ∈ execution.network.inputs) (fact : evidence.Fact)
      (carried : fact ∈ evidence.decode input.envelope.payload) :
      owner fact = input.broadcaster ∨ fact ∈ evidence.observe
        ((execution.respond app actor action).observe app input.broadcaster) :=
    (origin input retained fact carried).imp id
      (evidence.observed_respond execution input.broadcaster actor action fact)
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact prior
  | some transmission =>
    cases transmission with
    | submit material =>
      intro input retained fact carried
      rcases List.mem_append.mp retained with retained | fresh
      · exact prior input retained fact carried
      · cases List.mem_singleton.mp fresh
        rcases issued (app.submit execution.application actor material) actor
          (execution.network.known actor) material fact carried with owned | copied
        · exact Or.inl owned
        · obtain ⟨message, known, carried⟩ := copied
          exact (evidence.known_origin owner execution origin actor message known fact carried).imp
            id (evidence.observed_respond execution actor actor _ fact)
    | replay id =>
      cases found : (execution.network.known actor).find? (fun message => message.id = id) with
      | none =>
        simpa only [InputOrigin, Execution.respond, MessageNetwork.replay, found] using prior
      | some message =>
        intro input retained fact carried
        change input ∈ (execution.network.replay actor id).2.inputs at retained
        rw [MessageNetwork.replay, found] at retained
        rcases List.mem_append.mp retained with retained | fresh
        · exact prior input retained fact carried
        · cases List.mem_singleton.mp fresh
          exact (evidence.known_origin owner execution origin actor message
            (List.mem_of_find?_eq_some found) fact carried).imp
              (fun same => same) (evidence.observed_respond execution actor actor _ fact)

theorem inputOrigin_environment (execution next : app.Execution) (command : app.Command)
    (origin : evidence.InputOrigin owner execution)
    (reached : next ∈ (execution.environmentStep app command).support) :
    evidence.InputOrigin owner next := by
  have inputs : next.network.inputs = execution.network.inputs := by
    cases command with
    | wait =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      rfl
    | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      rfl
    | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      cases found : execution.network.lookup id <;>
        simp [Execution.includePending, MessageNetwork.includePending, found]
    | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
      rfl
  intro input retained fact carried
  rw [inputs] at retained
  exact (origin input retained fact carried).imp id
    (fun seen => evidence.observed_environment execution next input.broadcaster command fact
      seen reached)

theorem inputOrigin_serviceInvariant (issued : evidence.OwnerIssued owner)
    (scheduler : app.Scheduler) : app.ServiceInvariant scheduler (evidence.InputOrigin owner) where
  respond := evidence.inputOrigin_respond owner issued
  environment execution next command origin _ reached :=
    evidence.inputOrigin_environment owner execution next command origin reached

/-- The acquisition constraint holds at every legal raw history, including
off-path histories, under arbitrary public-history scheduling and leak rules. -/
theorem history_inputOrigin (issued : evidence.OwnerIssued owner)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {state} (trace : (app.protocol initial horizon scheduler).Trace state) :
    ReactiveApplication.serviceInvariant (evidence.InputOrigin owner) state :=
  (evidence.inputOrigin_serviceInvariant owner issued scheduler).history initial horizon
    (fun state _ => evidence.inputOrigin_initial owner state) trace

/-- At any initialized history, a possessed foreign certificate has an actual
observation witness. Owning a copy in private output recall does not bypass it. -/
theorem foreign_known_observed (issued : evidence.OwnerIssued owner)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control) (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (message : Message Principal app.Payload)
    (known : message ∈ control.execution.network.known who) (fact : evidence.Fact)
    (carried : fact ∈ evidence.decode message.payload) (foreign : owner fact ≠ who) :
    fact ∈ evidence.observe (control.execution.observe app who) :=
  (evidence.known_origin owner control.execution
    (evidence.history_inputOrigin owner issued initial horizon scheduler trace)
    who message known fact carried).resolve_left foreign

/-- With passive observation disabled, every possessed foreign certificate
must already occur in the public ledger. This covers every legal prefix and
arbitrary forwarding chains; it concerns certificates, not arbitrary inference. -/
theorem foreign_known_published (issued : evidence.OwnerIssued owner)
    (emptyObservation : ∀ who pending, app.observePending who pending = FinDist.pure ∅)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control) (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (message : Message Principal app.Payload)
    (known : message ∈ control.execution.network.known who) (fact : evidence.Fact)
    (carried : fact ∈ evidence.decode message.payload) (foreign : owner fact ≠ who) :
    ∃ publication ∈ control.execution.network.ledger,
      fact ∈ evidence.decode publication.payload := by
  have observed := evidence.foreign_known_observed owner issued initial horizon scheduler
    control trace who message known fact carried foreign
  have empty := app.history_leaked_empty emptyObservation initial horizon scheduler trace
  change ∀ who, control.execution.network.leaked who = [] at empty
  change fact ∈ (control.execution.network.leaked who ++
    control.execution.network.ledger).flatMap (fun packet => evidence.decode packet.payload)
      at observed
  rw [empty who, List.nil_append] at observed
  exact List.mem_flatMap.mp observed

end Interaction.ReactiveApplication.PacketEvidence
