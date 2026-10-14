/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketFactorization

/-! # The initial floor

The smallest positive mass the initial law gives the application state of a
native history (`Vegas.initialFloor`) is positive (`Vegas.initialFloor_pos`) and
bounds the mass of every initial state the law supports
(`Vegas.initialFloor_le`), since every supported initial state starts a history.
It does not depend on any assessment.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]

/-- The mass the initial law gives the application state of a native state. -/
def initialMass : (application setup leaks).ProtocolState → ℝ
  | none => 0
  | some control => (initialLaw setup control.execution.application).toReal

open Classical in
/-- The positive initial masses of the states of the native histories. -/
def initialMasses : Finset ℝ :=
  let := Fintype.ofFinite (onePacketProtocol setup leaks bounds horizon scheduler).History
  ((Finset.univ : Finset (onePacketProtocol setup leaks bounds horizon scheduler).History).image
    fun history => initialMass setup leaks history.state).filter (0 < ·)

/-- **The initial floor.** The smallest positive initial mass of the state of a
native history; one when there is none. -/
def initialFloor : ℝ :=
  if nonempty : (initialMasses setup leaks bounds horizon scheduler).Nonempty then
    (initialMasses setup leaks bounds horizon scheduler).min' nonempty
  else 1

theorem initialFloor_pos : 0 < initialFloor setup leaks bounds horizon scheduler := by
  classical
  unfold initialFloor
  split
  · rename_i nonempty
    have member := (initialMasses setup leaks bounds horizon scheduler).min'_mem nonempty
    unfold initialMasses at member
    exact (Finset.mem_filter.mp member).2
  · exact zero_lt_one

/-- **Supported initial states are above the initial floor.** -/
theorem initialFloor_le {state : (application setup leaks).State}
    (supported : state ∈ (initialLaw setup).support) :
    initialFloor setup leaks bounds horizon scheduler ≤ (initialLaw setup state).toReal := by
  classical
  let := Fintype.ofFinite (onePacketProtocol setup leaks bounds horizon scheduler).History
  obtain ⟨trace⟩ := (bounds.onePacketMenu (runtime setup) leaks).trace_initial (initialLaw setup)
    horizon scheduler state supported
  have positive : 0 < (initialLaw setup state).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp supported) (PMF.apply_ne_top _ _)
  have member : (initialLaw setup state).toReal ∈ initialMasses setup leaks bounds horizon
      scheduler := by
    unfold initialMasses
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨⟨_, trace⟩, Finset.mem_univ _, rfl⟩,
      positive⟩
  have nonempty : (initialMasses setup leaks bounds horizon scheduler).Nonempty := ⟨_, member⟩
  unfold initialFloor
  rw [dite_eq_left_of_eq_true (eq_true nonempty)]
  exact Finset.min'_le _ _ member

end Vegas
