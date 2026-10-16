/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceTable
import Interaction.ReactiveStoppedProfileMixture
import Interaction.ReactiveAnchoredStopped

/-! # Complete original service tables realize the actual stopped policy jointly -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

variable
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
  (horizon : Nat)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
local notation "Q" => phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
local notation "P" => phaseCountServicePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
local notation "original" => independentProduct (fun _address : PhaseSeedAddress graph =>
  independentProduct (fun index : Fin horizon => PhaseCount.bindingServiceCoinLaw failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded rawWeight rawNonnegative
      rawBounded (Fin.val index)))

/-- The original all-address mixture has the same whole stopped history law
as the literal normalized policy, from any genuine full starting history. -/
theorem phaseCountServiceTapePolicy_table_run
    (certificate : (E).WellFoundedHistories) (stopped : (E).History → Prop)
    (history : (E).History) :
    (N).runBehavioralUntil certificate (fun who =>
      (menu).restrictPolicy initial horizon scheduler who
        ((app).policyMixture original (fun table => Q table who)).policy) stopped history =
      (N).runBehavioralUntil certificate (fun who =>
        (menu).restrictPolicy initial horizon scheduler who (P who)) stopped history := by
  classical
  apply (N).runBehavioralUntil_congr certificate stopped history
  intro later _reached _running who
  rcases later with ⟨state, trace⟩
  have observed := (menu).info initial horizon scheduler who trace
  change (N).infoOf who trace = (app).observe who state at observed
  cases state with
  | none => rw [observed]; rfl
  | some current =>
      by_cases active : current.actor = some who
      · simp only [ReactiveApplication.observe, ite_eq_left active] at observed
        rw [observed]
        apply (menu).restrictPolicy_eq_of_law_eq
        exact phaseCountServiceTapePolicy_table_policy_of_history setup mode runtime leaks bounds
          values choose failure timing firstNonnegative firstBounded timingNonnegative
          timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon plan inputs scheduler current trace who active
      · simp only [ReactiveApplication.observe, ite_eq_right active] at observed
        rw [observed]
        rfl

/-- Original private tables disintegrate the actual normalized stopped run
jointly with its full final history. At a later entry the left prior is the
genuine own-recall posterior of those same tables, including every used and
unused coordinate; it is not replaced by a fresh independent table draw. -/
theorem phaseCountServiceTapePolicy_table_run_joint
    (certificate : (E).WellFoundedHistories) (stopped : (E).History → Prop)
    (history : (E).History) :
    (independentProduct (fun who =>
      ((app).policyMixture original (fun table => Q table who)).posterior
        ((app).recallAt who history.state))).bind (fun tables =>
      ((N).runBehavioralUntil certificate (fun who =>
        (menu).restrictPolicy initial horizon scheduler who (Q (tables who) who)) stopped
          history).map (fun final => (final, tables))) =
      ((N).runBehavioralUntil certificate (fun who =>
        (menu).restrictPolicy initial horizon scheduler who (P who)) stopped history).bind
          fun final => (independentProduct (fun who =>
            ((app).policyMixture original (fun table => Q table who)).posterior
              ((app).recallAt who final.state))).map (Prod.mk final) := by
  have joint := (menu).runUntil_policyMixtures_joint initial horizon scheduler certificate
    (fun _who => original) (fun who table => Q table who)
    (fun who table past view action supported =>
      phaseCountServiceTapePolicy_covered setup mode runtime leaks bounds values choose failure
        timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon table who past view
        action supported) stopped history
  rw [phaseCountServiceTapePolicy_table_run setup mode runtime leaks bounds values choose failure
    timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
    slotBounded rawWeight rawNonnegative rawBounded horizon plan inputs scheduler certificate
    stopped history] at joint
  exact joint

/-- The original tables are sampled once before the actual physical input
draw. Their joint with the entire stopped history is the literal normalized
policy law augmented by its genuine final table posteriors. -/
theorem phaseCountServiceTapePolicy_table_initial_joint
    (certificate : (E).WellFoundedHistories) (stopped : (E).History → Prop) :
    (independentProduct (fun _who : Player => original)).bind (fun tables =>
      ((N).runBehavioralUntil certificate (fun who =>
        (menu).restrictPolicy initial horizon scheduler who (Q (tables who) who)) stopped
          (E).initHistory).map (fun final => (final, tables))) =
      ((N).runBehavioralUntil certificate (fun who =>
        (menu).restrictPolicy initial horizon scheduler who (P who)) stopped (E).initHistory).bind
          fun final => (independentProduct (fun who =>
            ((app).policyMixture original (fun table => Q table who)).posterior
              ((app).recallAt who final.state))).map (Prod.mk final) := by
  exact phaseCountServiceTapePolicy_table_run_joint setup mode runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon plan inputs scheduler
    certificate stopped (E).initHistory

end Vegas
