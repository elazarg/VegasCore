/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.Cursor

/-! # Exact response counts at the native decision sites

The fixed calendar gives Bob one earlier response before his binding and two
before his opening. These are counts of unrestricted network responses.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

variable {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}

/-- The count is valid at every legal history at the owner's turn. -/
theorem native_decision_recall_count (event : nativeGraph.EventId) (control : (serviceApp
  observation).Control)
    (trace : (serviceArena observation).Trace (some control)) (who : Player)
    (active : control.actor = some who)
    (granted : NativeTurn event control) (observer : Player) :
    (control.execution.recall observer).length =
      nativeResponseCount observer (nativeBeforeResponse event) := by
  obtain ⟨owner, position⟩ := native_decision_cursor event control trace who active granted
  obtain ⟨_, prior, priorMem, observed⟩ :=
    native_decision_predecessor event control trace (owner ▸ active) position
  rw [(serviceApp observation).environmentStep_recall prior control.execution _ observed]
  simpa only [nativeRoot, ReactiveApplication.Execution.initial, List.length_nil,
    Nat.zero_add] using native_plan_recall_count (serviceMenu observation).uniformResponses
      (nativeBeforeResponse event) nativeRoot prior observer priorMem

theorem native_bob_binding_recall (control : (serviceApp observation).Control)
    (trace : (serviceArena observation).Trace (some control)) (active : control.actor = some bob)
    (granted : NativeTurn bobBinding control) :
    (control.execution.recall bob).length = 1 :=
  native_decision_recall_count bobBinding control trace bob active granted bob

theorem native_bob_opening_recall (control : (serviceApp observation).Control)
    (trace : (serviceArena observation).Trace (some control)) (active : control.actor = some bob)
    (granted : NativeTurn bobPublication control) :
    (control.execution.recall bob).length = 2 :=
  native_decision_recall_count bobPublication control trace bob active granted bob

theorem native_alice_opening_recall (control : (serviceApp observation).Control)
    (trace : (serviceArena observation).Trace (some control)) (active : control.actor = some alice)
    (granted : NativeTurn alicePublication control) :
    (control.execution.recall alice).length = 2 :=
  native_decision_recall_count alicePublication control trace alice active granted alice

end Vegas.Examples.SelectiveAssociation
