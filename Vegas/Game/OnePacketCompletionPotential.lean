/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCompletionLaw
import Vegas.Game.OnePacketLateBadMass
import Vegas.Game.OnePacketLateLumping

/-! # Completion potentials for actual current-event laws -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler

open Classical in
/-- On any actual law supported on completed events, missing intended completion
points without failure have exactly the mass of the physical bad-stop observable. -/
theorem completionPoint_badMass_eq_lateBadStop
    (law : PMF (E).History) (rank : Nat) (key : LateKey setup runtime leaks)
    (event : (graph setup).EventId)
    (decided : decidedEvent (runtime := runtime) key = some event)
    (fresh : (application setup runtime leaks).Control → Prop)
    (completed : ∀ final ∈ law.support,
      ∃ control : (application setup runtime leaks).Control, final.state = some control ∧
        event ∈ control.execution.application.config.cut.completed) :
    (law.toOuterMeasure {final |
      completionPoint setup runtime leaks bounds horizon scheduler rank fresh final = none ∧
        ¬ DecisionFailed (runtime := runtime) key final.state}).toReal =
      expect law (lateBadStop setup runtime leaks bounds horizon scheduler rank fresh event) := by
  rw [← expect_indicator]
  apply expect_congr_on_support
  intro final member
  obtain ⟨control, state, completed⟩ := completed final member
  have failed : DecisionFailed (runtime := runtime) key final.state ↔
      StoreEventFailed control.execution.application.config.store event := by
    simp only [state, DecisionFailed, decided, completed, true_and]
  have successful : (∃ next : (application setup runtime leaks).Control,
      final.state = some next ∧ event ∈ next.execution.application.config.cut.completed ∧
        ¬ StoreEventFailed next.execution.application.config.store event) ↔
      ¬ DecisionFailed (runtime := runtime) key final.state := by
    rw [failed]
    constructor
    · rintro ⟨next, same, _completed, works⟩
      rw [state, Option.some.injEq] at same
      cases same
      exact works
    · intro works
      exact ⟨_, state, completed, works⟩
  unfold lateBadStop
  simp only [Set.mem_ofPred_eq]
  have equivalence :
      (completionPoint setup runtime leaks bounds horizon scheduler rank fresh final = none ∧
        ¬ DecisionFailed (runtime := runtime) key final.state) ↔
      (∃ next : (application setup runtime leaks).Control,
        final.state = some next ∧ event ∈ next.execution.application.config.cut.completed ∧
          ¬ StoreEventFailed next.execution.application.config.store event) ∧
        completionPoint setup runtime leaks bounds horizon scheduler rank fresh final = none :=
    ⟨fun holds => ⟨successful.mpr holds.2, holds.1⟩,
      fun holds => ⟨holds.2, successful.mp holds.1⟩⟩
  by_cases first : completionPoint setup runtime leaks bounds horizon scheduler rank fresh final =
      none ∧ ¬ DecisionFailed (runtime := runtime) key final.state
  · rw [ite_eq_left first, ite_eq_left (equivalence.mp first)]
  · rw [ite_eq_right first, ite_eq_right (fun second => first (equivalence.mpr second))]

end Vegas
