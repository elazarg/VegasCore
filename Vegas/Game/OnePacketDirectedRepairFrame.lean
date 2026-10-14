/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The part of own recall retained by every late-delivery key. Private source
choices and candidate material are omitted, but actual envelopes are retained. -/
def operationalRecall (past : List (application setup leaks).PlayerEntry) :
    List (OperationalView setup leaks ×
      Option (Message Player (application setup leaks).Payload)) :=
  past.map fun entry => (operationalView setup leaks entry.beforeView, entry.emitted)

/-- Reconstructing private candidate material changes no operational view. -/
theorem operationalView_shadow (memory : BindingShadow (graph setup))
    (view : (application setup leaks).PlayerView) :
    operationalView setup leaks (memory.inputView (runtime setup) leaks view) =
      operationalView setup leaks view := rfl

namespace EventGraphRuntime.BindingMemory.Frame

variable {memory : BindingMemory (runtime setup) leaks} {owner : Player}
  {original repaired : (application setup leaks).Execution}

/-- A binding-repair frame preserves the operational current view of its owner. -/
theorem operationalView (frame : Frame (runtime setup) leaks memory owner original repaired) :
    Vegas.operationalView setup leaks (original.observe (application setup leaks) owner) =
      Vegas.operationalView setup leaks (repaired.observe (application setup leaks) owner) := by
  exact (congrArg (Vegas.operationalView setup leaks) frame.observed).symm

/-- Foreign players have equal full decision inputs under the repair frame. -/
theorem decisionInput {who : Player}
    (frame : Frame (runtime setup) leaks memory owner original repaired) (foreign : who ≠ owner) :
    (original.recall who, original.observe (application setup leaks) who) =
      (repaired.recall who, repaired.observe (application setup leaks) who) :=
  Prod.ext (frame.recall who foreign) (frame.foreign_observed who foreign)

/-- Replacing only the private material of a canonical binding leaves the
owner's operational recall unchanged. Both actual signed envelopes, including
the readiness token and fresh serial, are identical. -/
theorem operationalRecall_rawBinding
    (frame : Frame (runtime setup) leaks memory owner original repaired)
    (recalled : Vegas.operationalRecall (setup := setup) (leaks := leaks)
        (original.recall owner) = Vegas.operationalRecall (repaired.recall owner))
    (event : (graph setup).EventId) (first second : Option (Raw L)) (serial : Nat) :
    Vegas.operationalRecall
        ((original.respond (application setup leaks) owner
          ⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩⟩).recall owner) =
      Vegas.operationalRecall
        ((repaired.respond (application setup leaks) owner
          ⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩).recall owner) := by
  have publicEq := frame.publicView
  have network := frame.network
  have current := frame.operationalView
  simp only [ReactiveApplication.Execution.respond, Vegas.operationalRecall,
    List.map_append, List.map_cons, List.map_nil,
    ite_true]
  change Vegas.operationalRecall (original.recall owner) ++ [_] =
    Vegas.operationalRecall (repaired.recall owner) ++ [_]
  rw [recalled]
  congr 1
  apply congrArg List.singleton
  apply Prod.ext current
  apply congrArg some
  apply congrArg₂ Message.mk (congrArg (fun net => (owner, net.nextSerial owner)) network)
  exact (reactiveApplication_packet_none (runtime setup) leaks original.application owner
    (original.network.known owner) ⟨.commitment event (owner, .prepared serial), first⟩).trans
      ((congrArg (fun pub => (⟨.commitment event (owner, .prepared serial), none,
        pub.tokenFor (.commitment event (owner, .prepared serial))⟩ :
        WitnessedPacket (graph setup)))
          publicEq).trans
        (reactiveApplication_packet_none (runtime setup) leaks repaired.application owner
          (repaired.network.known owner)
          ⟨.commitment event (owner, .prepared serial), second⟩).symm)

/-- Operational recall and the current delivered value are precisely the extra
owner-local invariants needed for equality of all players' late-delivery keys. -/
theorem lateKey (frame : Frame (runtime setup) leaks memory owner original repaired)
    (recalled : Vegas.operationalRecall (setup := setup) (leaks := leaks)
        (original.recall owner) = Vegas.operationalRecall (repaired.recall owner))
    (delivered : deliveredValue setup leaks owner
        (original.observe (application setup leaks) owner) =
      deliveredValue setup leaks owner (repaired.observe (application setup leaks) owner))
    (who : Player) :
    Vegas.lateKey setup leaks who
        (some (original.recall who, original.observe (application setup leaks) who)) =
      Vegas.lateKey setup leaks who
        (some (repaired.recall who, repaired.observe (application setup leaks) who)) := by
  by_cases same : who = owner
  · subst who
    simp only [Vegas.lateKey]
    rw [frame.operationalView, delivered]
    change some (LateKey.mk owner _ (Vegas.operationalRecall _) _) =
      some (LateKey.mk owner _ (Vegas.operationalRecall _) _)
    rw [recalled]
  · rw [frame.decisionInput same]

/-- A directed repair with its operational recall and reveal-value invariants
preserves the exact operational state, including the scheduler's private recall
and every player's delivery key. -/
theorem operationalState
    (frame : Frame (runtime setup) leaks memory owner original repaired)
    (recalled : Vegas.operationalRecall (setup := setup) (leaks := leaks)
        (original.recall owner) = Vegas.operationalRecall (repaired.recall owner))
    (delivered : deliveredValue setup leaks owner
        (original.observe (application setup leaks) owner) =
      deliveredValue setup leaks owner (repaired.observe (application setup leaks) owner))
    (remaining : Nat) (actor : Option Player) :
    Vegas.operationalState setup leaks (some ⟨remaining, actor, original⟩) =
      Vegas.operationalState setup leaks (some ⟨remaining, actor, repaired⟩) := by
  simp only [Vegas.operationalState]
  congr 1
  simp only [frame.service, frame.environment, frame.network]
  congr 1
  funext who
  exact frame.lateKey recalled delivered who

end EventGraphRuntime.BindingMemory.Frame

end Vegas
