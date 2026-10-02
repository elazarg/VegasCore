/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceTraffic
import Vegas.Game.RevealServicePrefixEnforcement
import Vegas.Game.RevealServiceOwnerSupport
import Vegas.Game.RevealServiceWatcherSupport
import Interaction.ReactiveLocalContinuation
import Interaction.ReactiveTrafficState

/-! # Attributable audit evidence for every extra retained response

Every added effective owner response at a retained information history emits
an actual traffic record that breaks the send-time rule. Owners use the checked
source-prefix packet classifier. Later players and schedulers cannot remove the
record.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)

include reveals observer openable in
theorem owner_extra_traffic (who : Player) (ordinary : who ≠ watcher)
    (history : (protocol setup leaks bounds watcher).History)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (excluded : response ∉ ordinaryActions setup leaks bounds who (execution.recall who)
      (execution.observe (application setup leaks) who)) :
    ∃ record, (application setup leaks).trafficStep
        (some ⟨remaining, some who, execution⟩)
        (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) =
          [record] ∧ record.envelope.sender = who ∧
      permittedTraffic setup leaks watcher record = false := by
  let responses := menu setup leaks bounds watcher
  let reference := responses.uniformPolicy (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)
  have active : (protocol setup leaks bounds watcher).active history.state who := by
    change (application setup leaks).actor history.state = some who
    rw [current]
    rfl
  obtain ⟨event, owned, _length, supported⟩ := owner_history_supported setup leaks bounds
    watcher who reveals ordinary history active
  obtain ⟨boundary, _supported, nativeState, initial, _initialSupport, source,
      _boundaryCheckpoint, related, _decoded⟩ :=
    owner_supported setup leaks bounds watcher who reveals observer openable reference
      event owned history supported
  have sameExecution : execution = ownerOpportunity setup leaks who boundary :=
    congrArg ReactiveApplication.Control.execution
      (Option.some.inj (current.symm.trans nativeState))
  have checkpoint : PrefixCheckpoint setup leaks initial setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val source execution :=
    sameExecution.symm ▸ related
  obtain ⟨submission, same, departure⟩ := prefix_extra_submission setup leaks bounds who reveals
    initial event owned source execution checkpoint response effective excluded
  subst response
  have serials : execution.network.SerialsBeforeNext :=
    PrefixCheckpoint.runtime_fact (fun next => next.network.SerialsBeforeNext)
      (fun _ _ _ _ checkpoint => checkpoint.serials) _ _ _ _ _ _ _ _ checkpoint
  have binding : execution.application.BindingInvariant :=
    PrefixCheckpoint.runtime_fact (fun next => next.application.BindingInvariant)
      (fun _ _ _ _ checkpoint => checkpoint.binding) _ _ _ _ _ _ _ _ checkpoint
  have sound := ((runtime setup).packetEvidence leaks).history_sound (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher)
    (responses.toRawTrace (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) history.trace)
  rw [current] at sound
  refine ⟨_, (application setup leaks).trafficStep_submit execution remaining who submission,
    rfl, ?_⟩
  exact departureTraffic_forbidden setup leaks execution watcher who sound binding serials
    submission departure

end Vegas
