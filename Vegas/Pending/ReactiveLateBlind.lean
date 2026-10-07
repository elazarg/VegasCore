/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCanonicalDecision
import Interaction.ReactiveErasure
import GameTheory.Math.Probability.Mixture

/-! # Builders blind to late packets

A packet is *late* when it names an event whose protected inclusion window had
already closed in the public view at which it was sent; that view is the
earliest recorded environment view whose inputs contain it, or the current
view if none does yet. A scheduler is *blind to late packets* when, at every
input holding a pending late packet, it either includes that packet or
otherwise acts exactly as it would in the world where the packet was never
sent (`Interaction.MessageId.erase` and the erasure of views and recall): no other command
depends on the packet or on its absence.

This is a named hypothesis on the builder. It is used only where a sequential
equilibrium is constructed for arbitrary builders; the contract
(`EventGraphRuntime.AsyncContract`) and the Nash results do not assume it.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bound : graph.EventId → Nat)

open Classical in
/-- The environment view right after `message` was sent: the earliest recorded
view whose inputs contain it, or the current view. -/
def sendingView (recall : List (runtime.reactiveApplication leaks).EnvironmentEntry)
    (view : (runtime.reactiveApplication leaks).EnvironmentView)
    (message : Message Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).EnvironmentView :=
  ((recall.find? fun entry => message.id ∈ entry.beforeView.network.inputs.map Message.id).map
    ReactiveApplication.EnvironmentEntry.beforeView).getD view

/-- `message` names an event whose protected inclusion window had closed in the
public view at which it was sent. -/
def SentLate (recall : List (runtime.reactiveApplication leaks).EnvironmentEntry)
    (view : (runtime.reactiveApplication leaks).EnvironmentView)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  ∃ event, message.payload.call.event? graph = some event ∧
    ¬ PublicView.InclusionFitsDeadline runtime bound
      (show PublicView graph from (runtime.sendingView leaks recall view message).application)
      event

/-- **Blind to late packets.** At every input holding a pending late packet, the
scheduler's law is a mixture of including that packet and its law in the world
where the packet was never sent, read back in the original identifiers. -/
def BlindToLatePackets (scheduler : (runtime.reactiveApplication leaks).Scheduler) : Prop :=
  ∀ (recall : List (runtime.reactiveApplication leaks).EnvironmentEntry)
    (view : (runtime.reactiveApplication leaks).EnvironmentView)
    (message : Message Player (WitnessedPacket graph)),
    message ∈ view.network.pending → runtime.SentLate leaks bound recall view message →
    ∃ (inclusion : ℝ) (nonnegative : 0 ≤ inclusion) (atMost : inclusion ≤ 1),
      scheduler recall view = mix inclusion nonnegative atMost (PMF.pure (.include message.id))
        ((scheduler
            (ReactiveApplication.eraseEnvironmentRecall _ message.id recall)
            (ReactiveApplication.EnvironmentView.erase _ message.id view)).map
          (ReactiveApplication.Command.restore _ message.id))

/-- The scheduler that always waits is blind to late packets. -/
theorem blindToLatePackets_wait :
    runtime.BlindToLatePackets leaks bound (fun _ _ => PMF.pure .wait) := by
  intro recall view message _ _
  refine ⟨0, le_rfl, zero_le_one, ?_⟩
  ext chosen
  rw [mix_apply, PMF.pure_map]
  simp [ReactiveApplication.Command.restore]

end Vegas.EventGraphRuntime
