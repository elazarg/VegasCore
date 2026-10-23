/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountMenu
import Interaction.ReactiveFiniteAssessment
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay

/-! # Fixed intrinsic chance floors for actual counted repair histories

The game and its initial joint law are fixed before response weights are
chosen. Nature's full trace mass therefore has one positive finite minimum,
even when initialization, public samples and service draws are correlated.
This floor is used only for rare-preparation bounds, not as a likelihood
factorization of ordinary source values.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (PhaseRuntimeState graph))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "E" =>
  ReactiveApplication.ResponseMenu.protocol (PhaseCount.onePacketMenu runtime leaks bounds)
    initial horizon scheduler
local notation "N" =>
  ReactiveApplication.ResponseMenu.information (PhaseCount.onePacketMenu runtime leaks bounds)
    initial horizon scheduler

/-- The intrinsic trace factor is an actual product of probabilities and
does not depend on a behavioral assessment. -/
theorem transitionMass_le_one {state : (E).State} (trace : (E).Trace state) :
    trace.transitionMass ≤ 1 := by
  induction trace with
  | start => exact le_rfl
  | @extend source target prior joint legal reached ih =>
      rw [Trace.transitionMass_extend]
      have upper : ((E).step source ⟨joint, legal⟩ target).toReal ≤ 1 := by
        simpa only [ENNReal.toReal_one] using
          ENNReal.toReal_mono ENNReal.one_ne_top
            (PMF.coe_le_one ((E).step source ⟨joint, legal⟩) target)
      exact (mul_le_mul_of_nonneg_left upper
        (le_of_lt prior.transitionMass_pos)).trans (by simpa only [mul_one] using ih)

/-- Finite nature and the fixed horizon supply one positive lower bound for
all actual histories, chosen independently of later bad/alias/source weights. -/
theorem exists_transitionMass_floor
    [(phaseApplication runtime leaks).FiniteNature initial scheduler] :
    ∃ lower : ℝ, 0 < lower ∧ lower ≤ 1 ∧
      ∀ history : (E).History, lower ≤ history.trace.transitionMass := by
  classical
  let masses := (Finset.univ : Finset (E).History).image fun history => history.trace.transitionMass
  have nonempty : masses.Nonempty := ⟨1, by
    exact Finset.mem_image.mpr ⟨(E).initHistory, Finset.mem_univ _, rfl⟩⟩
  let lower := masses.min' nonempty
  have present : lower ∈ masses := Finset.min'_mem masses nonempty
  obtain ⟨history, _included, minimum⟩ := Finset.mem_image.mp present
  have positive : 0 < lower := by rw [← minimum]; exact history.trace.transitionMass_pos
  have bounded : ∀ history : (E).History, lower ≤ history.trace.transitionMass := by
    intro history
    exact Finset.min'_le masses _ (Finset.mem_image.mpr ⟨history, Finset.mem_univ _, rfl⟩)
  exact ⟨lower, positive, bounded (E).initHistory, bounded⟩

/-- The existing continuation factorization at the literal empty prefix
separates every actual own-action factor from the original chance product. -/
theorem historyReach_eq_transitionMass_mul_ownPlay
    (profile : ∀ owner, (N).BehavioralPolicy owner) (history : (E).History) :
    ((N).historyReachWeight profile history).toReal = history.trace.transitionMass *
      ∏ owner, (N).ownPlayReachProbability (profile owner) ((N).ownPlay owner history.trace) := by
  obtain ⟨records, words, _origins, chance, _nonnegative, mass, factor⟩ :=
    (N).exists_continuation_ownPlay_factor (Trace.start : (E).Trace (E).init) history.trace
      (TracePrefix.start history.trace)
  have recordsEq (owner : Player) : records owner = (N).ownPlay owner history.trace := by
    simpa only [InfoSignals.ownPlay, List.append_nil] using (words owner).symm
  have chanceEq : chance = history.trace.transitionMass := by
    simpa only [Trace.transitionMass_start, mul_one] using mass
  have actual := factor profile
  change ((N).historyReachWeight profile history).toReal =
    chance * ∏ owner, (N).ownPlayReachProbability (profile owner) (records owner) at actual
  rw [chanceEq] at actual
  simpa only [recordsEq] using actual

end Vegas.EventGraphRuntime.PhaseProposal
