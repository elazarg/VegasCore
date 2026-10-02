/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameOpening
import Vegas.Pending.ReactiveGuardConformance

/-! # Publicly conforming disclosure inclusion in a repaired execution

The inclusion case starts from the actual pending envelope and its accepted
call. Certified format and public guard checks derive the unchanged successful
binding; no hidden value or repaired-candidate equality is assumed by the caller.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Inclusion of a certified opening that passes the recorded public guards
preserves the full repaired frame. An authentic guard-failing certificate is
excluded explicitly, even if the application would accept its call. -/
theorem accepted_guarded_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (id : MessageId Player) (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (sender : id.1 = actor) (packet : WitnessedPacket graph)
    (found : original.network.lookup id = some ⟨id, packet⟩)
    (addressed : packet.call.event? graph = some event)
    (tokened : packet.token = some ⟨event⟩)
    (certified : certifiedOpening packet = true)
    (guards : original.application.publicView.openingGuardsAccepted packet = true)
    (next : State graph)
    (accepted : runtime.handle original.application ⟨id, packet.call⟩ = some next) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  obtain ⟨actual, offered, raw, token, rfl⟩ := (certifiedOpening_iff packet).mp certified
  cases Option.some.inj addressed
  change token = some ⟨event⟩ at tokened
  subst token
  have owned : offered.1 = actor := by
    by_contra foreign
    simp [handle, node, foreign] at accepted
  have fixed := runtime.handle_opening_verified original.application next id event offered raw
    accepted
  let submission := disclosureSubmission (.opening event offered raw)
  have emitted : submission.emit original.application actor [] =
      ⟨.opening event offered raw, some ⟨offered, raw⟩, some ⟨event⟩⟩ := by
    have verified := (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr fixed
    simp only [submission, disclosureSubmission, WitnessedSubmission.emit, owned, verified,
      and_self, ↓reduceIte,
      original.application.publicView_tokenFor_of_ready (.opening event offered raw) event rfl
        ready]
  have canonicalAccepted : (runtime.reactiveApplication leaks).handle
      ((runtime.reactiveApplication leaks).submit original.application actor submission)
      ⟨(actor, id.2), submission.emit
        ((runtime.reactiveApplication leaks).submit original.application actor submission)
          actor []⟩ = some next := by
    change (runtime.reactiveApplication leaks).handle original.application
      ⟨(actor, id.2), submission.emit original.application actor []⟩ = some next
    rw [emitted, reactiveApplication_handle_of_tokenValid runtime leaks _ _
      (WitnessedPacket.tokenValid_opening _ _ _ _)]
    simpa only [← sender, Prod.mk.eta] using accepted
  obtain ⟨candidate, value, associated, _, stored, resolved, normalized⟩ :=
    runtime.accepted_guarded_opening_normalization leaks original.application next actor event
      payload binding checks outputEq codeEq node [] submission id.2 rfl
        (by change certifiedOpening (submission.emit original.application actor []) = true
            rw [emitted]
            simp only [certifiedOpening, decide_true])
        (by change original.application.publicView.openingGuardsAccepted
              (submission.emit original.application actor []) = true
            rw [emitted]
            exact guards)
        canonicalAccepted
  have callEq := congrArg (fun material : WitnessedSubmission graph => material.call.packet)
    normalized
  change Payload.opening event offered raw = .opening event candidate ⟨payload, value⟩ at callEq
  have selected : offered = candidate := (Payload.opening.inj callEq).2.1
  have rawEq : raw = ⟨payload, value⟩ := (Payload.opening.inj callEq).2.2
  subst offered
  subst raw
  obtain ⟨rightStored, actual, leftAssociated, rightAssociated, _, leftFixed, rightFixed⟩ :=
    frame.successful_opening leftBinding rightBinding binding value stored
  have same := Option.some.inj (leftAssociated.symm.trans associated)
  subst actual
  exact frame.opening_inclusion onlyBindings id event candidate actor payload binding checks
    outputEq codeEq node ready timely sender owned associated value leftFixed rightFixed stored
      rightStored (.success value) resolved (some ⟨candidate, ⟨payload, value⟩⟩) found

end Vegas.EventGraphRuntime.BindingMemory.Frame
