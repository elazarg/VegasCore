/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionBoundedProfile

/-! # Actual recovery policies evaluated at clear native observations

The policy projection reads complete lifted own recall and views. It is
independent of the scheduler used to type a protocol behavioral profile.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Evaluate a raw recovery policy at the full clear lift of native information. -/
def nativePolicy (policy : (runtime.recoveryApplication leaks).Policy) :
    (runtime.reactiveApplication leaks).Policy := fun past view =>
  (policy (past.map (liftPlayerEntry runtime leaks))
    (liftPlayerView runtime leaks view)).map (action runtime leaks)

variable [Fintype Player]

/-- Genuine bounded recovery policies project to the native one-packet menu
without any scheduler or hidden-seed parameter. -/
theorem nativePolicy_onePacket (bounds : MessageBounds graph)
    (players : Player → (runtime.recoveryApplication leaks).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (Recovery.onePacketMenu runtime leaks bounds).actions who past view)
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (supported : response ∈ (nativePolicy runtime leaks (players who) past view).support) :
    response ∈ (bounds.onePacketMenu runtime leaks).actions who past view := by
  obtain ⟨original, possible, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact (onePacket_actions_lifted runtime leaks bounds who past view original).mp
    (covered who _ _ original possible)

end Vegas.EventGraphRuntime.RecoveryProjection
