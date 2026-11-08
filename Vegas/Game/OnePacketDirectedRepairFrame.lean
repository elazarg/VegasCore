/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFactorization
import Vegas.Pending.ReactiveBindingFrameRounds

/-! # Operational projections of directed hidden-binding repair

The ordinary binding-repair frame preserves the scheduler's full information,
the network, and every foreign player's full information. Its owner-local
shadow restores private candidate material and source choices. The additional
invariants needed by the counterpart construction are the owner's operational
recall and the value delivered at its current reveal. These imply equality of
the complete operational state used in the native reach factorization.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The part of own recall retained by every late-delivery key. Private source
choices and candidate material are omitted, but actual envelopes are retained. -/
def operationalRecall (past : List (application setup timeouts leaks).PlayerEntry) :
    List (OperationalView setup timeouts leaks ×
      Option (Message Player (application setup timeouts leaks).Payload)) :=
  past.map fun entry => (operationalView setup timeouts leaks entry.beforeView, entry.emitted)

namespace EventGraphRuntime.BindingMemory.Frame

variable {memory : BindingMemory timeouts leaks} {owner : Player}
  {original repaired : (application setup timeouts leaks).Execution}

/-- A binding-repair frame preserves the operational current view of its owner. -/
theorem operationalView (frame : Frame timeouts leaks memory owner original repaired) :
    Vegas.operationalView setup timeouts leaks (original.observe (application setup timeouts leaks)
      owner) =
      Vegas.operationalView setup timeouts leaks (repaired.observe (application setup timeouts
        leaks) owner) := by
  exact (congrArg (Vegas.operationalView setup timeouts leaks) frame.observed).symm

/-- Foreign players have equal full decision inputs under the repair frame. -/
theorem decisionInput {who : Player}
    (frame : Frame timeouts leaks memory owner original repaired) (foreign : who ≠ owner) :
    (original.logs who, original.observe (application setup timeouts leaks) who) =
      (repaired.logs who, repaired.observe (application setup timeouts leaks) who) :=
  Prod.ext (frame.logs who foreign) (frame.foreign_observed who foreign)

/-- Replacing only the private material of a canonical binding leaves the
owner's operational recall unchanged. Both actual signed envelopes, including
the readiness token and fresh serial, are identical. -/
theorem operationalRecall_rawBinding
    (frame : Frame timeouts leaks memory owner original repaired)
    (recalled : Vegas.operationalRecall (timeouts := timeouts) (setup := setup) (leaks := leaks)
        (original.logs owner) = Vegas.operationalRecall (timeouts := timeouts) (repaired.logs
          owner))
    (event : (graph setup).EventId) (first second : Option (Raw L)) (serial : Nat) :
    Vegas.operationalRecall (timeouts := timeouts)
        ((original.respond (application setup timeouts leaks) owner
          ⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩⟩).logs owner) =
      Vegas.operationalRecall (timeouts := timeouts)
        ((repaired.respond (application setup timeouts leaks) owner
          ⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩).logs owner) := by
  have publicEq := frame.publicView
  have network := frame.network
  have current := frame.operationalView
  simp only [ReactiveApplication.Execution.respond, Vegas.operationalRecall,
    List.map_append, List.map_cons, List.map_nil,
    ite_true]
  change Vegas.operationalRecall (timeouts := timeouts) (original.logs owner) ++ [_] =
    Vegas.operationalRecall (timeouts := timeouts) (repaired.logs owner) ++ [_]
  rw [recalled]
  congr 1
  apply congrArg List.singleton
  apply Prod.ext current
  apply congrArg some
  apply congrArg₂ Message.mk (congrArg (fun net => (owner, net.nextSerial owner)) network)
  exact (reactiveApplication_packet_none timeouts leaks original.application owner
    (original.network.known owner) ⟨.commitment event (owner, .prepared serial), first⟩).trans
      ((congrArg (fun pub => (⟨.commitment event (owner, .prepared serial), none,
        pub.tokenFor (.commitment event (owner, .prepared serial))⟩ :
        WitnessedPacket (graph setup)))
          publicEq).trans
        (reactiveApplication_packet_none timeouts leaks repaired.application owner
          (repaired.network.known owner)
          ⟨.commitment event (owner, .prepared serial), second⟩).symm)

/-- Operational recall and the current delivered value are precisely the extra
owner-local invariants needed for equality of all players' late-delivery keys. -/
theorem lateKey (frame : Frame timeouts leaks memory owner original repaired)
    (recalled : Vegas.operationalRecall (timeouts := timeouts) (setup := setup) (leaks := leaks)
        (original.logs owner) = Vegas.operationalRecall (timeouts := timeouts) (repaired.logs
          owner))
    (delivered : deliveredValue setup timeouts leaks owner
        (original.observe (application setup timeouts leaks) owner) =
      deliveredValue setup timeouts leaks owner (repaired.observe (application setup timeouts leaks)
        owner))
    (who : Player) :
    Vegas.lateKey setup timeouts leaks who
        (some (original.logs who, original.observe (application setup timeouts leaks) who)) =
      Vegas.lateKey setup timeouts leaks who
        (some (repaired.logs who, repaired.observe (application setup timeouts leaks) who)) := by
  by_cases same : who = owner
  · subst who
    simp only [Vegas.lateKey]
    rw [frame.operationalView, delivered]
    change some (LateKey.mk owner _ (Vegas.operationalRecall (timeouts :=
      timeouts) _) _) =
      some (LateKey.mk owner _ (Vegas.operationalRecall (timeouts := timeouts)
        _) _)
    rw [recalled]
  · rw [frame.decisionInput same]

/-- A directed repair with its operational recall and reveal-value invariants
preserves the exact operational state, including the scheduler's private recall
and every player's delivery key. -/
theorem operationalState
    (frame : Frame timeouts leaks memory owner original repaired)
    (recalled : Vegas.operationalRecall (timeouts := timeouts) (setup := setup) (leaks := leaks)
        (original.logs owner) = Vegas.operationalRecall (timeouts := timeouts) (repaired.logs
          owner))
    (delivered : deliveredValue setup timeouts leaks owner
        (original.observe (application setup timeouts leaks) owner) =
      deliveredValue setup timeouts leaks owner (repaired.observe (application setup timeouts leaks)
        owner))
    (remaining : Nat) (actor : Option Player) :
    Vegas.operationalState setup timeouts leaks (some ⟨remaining, actor, original⟩) =
      Vegas.operationalState setup timeouts leaks (some ⟨remaining, actor, repaired⟩) := by
  simp only [Vegas.operationalState]
  congr 1
  simp only [frame.service, frame.environment, frame.network]
  congr 1
  funext who
  exact frame.lateKey recalled delivered who

end EventGraphRuntime.BindingMemory.Frame

end Vegas
