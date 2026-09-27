/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveTrafficAudit
import Interaction.ReactiveResponseMenu
import GameTheoryExtensions.Analysis.Protocol.TerminalAudit

/-! # Conditional collection from persistent traffic evidence

The settlement service samples an authenticated subrecord of the actual traffic
history and applies a fixed conformance checker. A sampling guarantee for any
recorded violation implies the conditional collection premise of terminal-audit
enforcement, against arbitrary subsequent responses and scheduling.

Coverage and collection are service assumptions. The results do not infer them
from passive monitoring, independence, or a prescribed continuation strategy.
The verdict below represents an actually collected charge.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Audit randomness is sampled at settlement. The same sampled record determines
all charges, so neither player verdicts nor recorded transmissions need be independent. -/
def sampledTrafficAudit (permitted : app.TrafficRecord → Bool)
    (sample : List app.TrafficRecord → FinDist (List app.TrafficRecord))
    (actual : List app.TrafficRecord) : FinDist (Principal → Bool) :=
  (sample actual).map fun observed who => app.trafficViolation permitted who observed

theorem sampledTrafficAudit_collection (permitted : app.TrafficRecord → Bool)
    (sample : List app.TrafficRecord → FinDist (List app.TrafficRecord))
    (actual : List app.TrafficRecord) (who : Principal) :
    ((app.sampledTrafficAudit permitted sample actual).map (fun verdict => verdict who)).prob
        true =
      (sample actual).probOf
        {observed | app.trafficViolation permitted who observed = true} := by
  rw [sampledTrafficAudit, FinDist.map_comp, FinDist.prob_map_eq_probOf_preimage_singleton]
  rfl

/-- Authentic partial observation never fines a player whose actual traffic conforms. -/
theorem sampledTrafficAudit_sound (permitted : app.TrafficRecord → Bool)
    (sample : List app.TrafficRecord → FinDist (List app.TrafficRecord))
    (actual : List app.TrafficRecord) (who : Principal)
    (authentic : ∀ observed ∈ (sample actual).support, observed ⊆ actual)
    (conforms : ∀ record ∈ actual,
      record.input.broadcaster = who → permitted record = true) :
    ((app.sampledTrafficAudit permitted sample actual).map (fun verdict => verdict who)).prob
        true = 0 := by
  have silent : (app.sampledTrafficAudit permitted sample actual).map
      (fun verdict => verdict who) = FinDist.pure false := by
    rw [sampledTrafficAudit, FinDist.map_comp]
    calc
      _ = (sample actual).map (fun _ => false) := by
        apply FinDist.map_congr_of_eq_on_support
        intro observed supported
        exact app.trafficViolation_partial_sound permitted who actual observed
          (authentic observed supported) conforms
      _ = _ := by simp only [FinDist.map_eq_bind, FinDist.bind_const]
  rw [silent]
  exact FinDist.prob_pure_of_ne Bool.noConfusion

namespace ResponseMenu

variable {app} (menu : app.ResponseMenu)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- The original raw-history readout, restricted to this response menu. -/
def trafficAudit (history : (menu.protocol initial horizon scheduler).History) :
    List app.TrafficRecord :=
  app.trafficAudit initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.trace)

/-- An actual step appends precisely the traffic derived from its public before
and after states. The original response and observation semantics are unchanged. -/
theorem trafficAudit_extend
    (history : (menu.protocol initial horizon scheduler).History)
    (joint : Principal → Option app.Action)
    (legal : (menu.protocol initial horizon scheduler).Legal history.state joint)
    (next : app.ProtocolState)
    (realized : next ∈ ((menu.protocol initial horizon scheduler).step history.state
      ⟨joint, legal⟩).support) :
    menu.trafficAudit initial horizon scheduler (history.extend legal realized) =
      menu.trafficAudit initial horizon scheduler history ++ app.trafficStep history.state next :=
  rfl

theorem trafficAudit_reaches
    {first last : (menu.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (menu.protocol initial horizon scheduler).ReachesWithin fuel first last) :
    menu.trafficAudit initial horizon scheduler first <+:
      menu.trafficAudit initial horizon scheduler last :=
  app.trafficAudit_reaches initial horizon scheduler
    (menu.reaches_raw initial horizon scheduler path)

variable [Fintype Principal]

/-- Once evidence exists, per-record coverage suffices uniformly over every
later target strategy. The sample may depend on the complete final transcript. -/
theorem trafficAudit_collection_from_record
    (permitted : app.TrafficRecord → Bool)
    (sample : List app.TrafficRecord → FinDist (List app.TrafficRecord))
    (who : Principal) (rate : ℝ)
    (coverage : ∀ actual record, record ∈ actual →
      record.input.broadcaster = who → permitted record = false →
      rate ≤ (sample actual).probOf {observed | record ∈ observed})
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (record : app.TrafficRecord)
    (present : record ∈ menu.trafficAudit initial horizon scheduler history)
    (owner : record.input.broadcaster = who) (forbidden : permitted record = false) :
    rate ≤ (((((menu.information initial horizon scheduler).runBehavioralFrom profile fuel
      history).map (menu.trafficAudit initial horizon scheduler)).bind
        (app.sampledTrafficAudit permitted sample)).map
          (fun verdict => verdict who)).prob true := by
  rw [TerminalAudit.collection_probability]
  calc
    rate = ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel
      history).expect (fun _ => rate) := (FinDist.expect_const _ _).symm
    _ ≤ _ := by
      apply FinDist.expect_mono
      intro final supported
      have path := (menu.protocol initial horizon scheduler).runRandomizedFor_reachesWithin
        ((menu.information initial horizon scheduler).randomizedChooser profile)
        fuel history final supported
      have retained := (menu.trafficAudit_reaches initial horizon scheduler path).subset present
      exact (coverage _ record retained owner forbidden).trans
        (by
          change _ ≤ ((app.sampledTrafficAudit permitted sample _).map
            (fun verdict => verdict who)).prob true
          rw [app.sampledTrafficAudit_collection]
          exact app.trafficViolation_sampling_lower permitted who _ record owner forbidden)

/-- The continuation collection obligation reduces to evidence after one actual
response. Only that first step is classified; later responses are unrestricted. -/
theorem trafficAudit_collection_after_step
    (permitted : app.TrafficRecord → Bool)
    (sample : List app.TrafficRecord → FinDist (List app.TrafficRecord))
    (who : Principal) (rate : ℝ)
    (coverage : ∀ actual record, record ∈ actual →
      record.input.broadcaster = who → permitted record = false →
      rate ≤ (sample actual).probOf {observed | record ∈ observed})
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (evidence : ∀ next ∈ ((menu.information initial horizon scheduler).runBehavioralFrom
      profile 1 history).support,
      ∃ record ∈ menu.trafficAudit initial horizon scheduler next,
        record.input.broadcaster = who ∧ permitted record = false) :
    rate ≤ (((((menu.information initial horizon scheduler).runBehavioralFrom profile
      (1 + fuel) history).map (menu.trafficAudit initial horizon scheduler)).bind
        (app.sampledTrafficAudit permitted sample)).map
          (fun verdict => verdict who)).prob true := by
  rw [(menu.information initial horizon scheduler).runBehavioralFrom_add,
    TerminalAudit.collection_probability, FinDist.expect_bind]
  calc
    rate = ((menu.information initial horizon scheduler).runBehavioralFrom profile 1
      history).expect (fun _ => rate) := (FinDist.expect_const _ _).symm
    _ ≤ _ := by
      apply FinDist.expect_mono
      intro next supported
      obtain ⟨record, present, owner, forbidden⟩ := evidence next supported
      have bound := menu.trafficAudit_collection_from_record initial horizon scheduler permitted
        sample who rate coverage profile fuel next record present owner forbidden
      rwa [TerminalAudit.collection_probability] at bound

end ResponseMenu
end Interaction.ReactiveApplication
