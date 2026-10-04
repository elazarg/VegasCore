/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveTrafficAudit
import Interaction.ReactiveResponseMenu
import GameTheoryExtensions.Analysis.Protocol.TerminalAudit
import GameTheoryExtensions.Math.Probability.Support

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

open Classical in
/-- Settlement samples projected authenticated evidence. Attribution is derived
from the signed evidence.
The same sampled record determines all charges. -/
def sampledTrafficAudit {Evidence : Type} (project : app.TrafficRecord → Evidence)
    (attribution : Evidence → Principal) (permitted : Evidence → Bool)
    (sample : List Evidence → PMF (List Evidence))
    (actual : List app.TrafficRecord) : PMF (Principal → Bool) :=
  (sample (actual.map project)).map fun observed who =>
    decide (∃ evidence ∈ observed, attribution evidence = who ∧ permitted evidence = false)

open Classical in
theorem sampledTrafficAudit_collection {Evidence : Type}
    (project : app.TrafficRecord → Evidence) (attribution : Evidence → Principal)
    (permitted : Evidence → Bool) (sample : List Evidence → PMF (List Evidence))
    (actual : List app.TrafficRecord) (who : Principal) :
    (((app.sampledTrafficAudit project attribution permitted sample actual).map
        (fun verdict => verdict who)) true).toReal =
      ((sample (actual.map project)).toOuterMeasure {observed | ∃ evidence ∈ observed,
          attribution evidence = who ∧ permitted evidence = false}).toReal := by
  rw [sampledTrafficAudit, PMF.map_comp, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  congr 2
  ext observed
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply, decide_eq_true_eq,
    Set.mem_ofPred_eq]

/-- Authenticity is required after projection to the evidence used by the audit. -/
theorem sampledTrafficAudit_sound {Evidence : Type}
    (project : app.TrafficRecord → Evidence) (attribution : Evidence → Principal)
    (permitted : Evidence → Bool) (sample : List Evidence → PMF (List Evidence))
    (actual : List app.TrafficRecord) (who : Principal)
    (authentic : ∀ observed ∈ (sample (actual.map project)).support,
      observed ⊆ actual.map project)
    (conforms : ∀ record ∈ actual,
      attribution (project record) = who → permitted (project record) = true) :
    (((app.sampledTrafficAudit project attribution permitted sample actual).map
        (fun verdict => verdict who)) true).toReal = 0 := by
  classical
  have silent : (app.sampledTrafficAudit project attribution permitted sample actual).map
      (fun verdict => verdict who) = PMF.pure false := by
    rw [sampledTrafficAudit, PMF.map_comp]
    calc
      _ = (sample (actual.map project)).map (fun _ => false) := by
        apply map_congr_on_support _
        intro observed supported
        change decide _ = false
        apply decide_eq_false
        rintro ⟨evidence, member, owner, forbidden⟩
        obtain ⟨record, present, rfl⟩ := List.mem_map.mp (authentic observed supported member)
        have allowed := conforms record present owner
        rw [allowed] at forbidden
        cases forbidden
      _ = _ := by simp only [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_const]
  rw [silent, PMF.pure_apply_of_ne _ _ Bool.noConfusion, ENNReal.toReal_zero]

omit [DecidableEq Principal] in
private theorem evidence_sampling_lower {Evidence : Type}
    (attribution : Evidence → Principal) (permitted : Evidence → Bool)
    (who : Principal) (observations : PMF (List Evidence))
    (record : Evidence) (owner : attribution record = who)
    (forbidden : permitted record = false) :
    (observations.toOuterMeasure {observed | record ∈ observed}).toReal ≤
      (observations.toOuterMeasure {observed | ∃ evidence ∈ observed,
        attribution evidence = who ∧ permitted evidence = false}).toReal := by
  apply ENNReal.toReal_mono (outerMeasure_ne_top _ _)
  apply PMF.toOuterMeasure_mono
  intro observed ⟨included, _⟩
  exact ⟨record, included, owner, forbidden⟩

/-- Per-record coverage applies to an arbitrary actual continuation law once
the attributed record is present in every possible final readout. -/
theorem sampledTrafficAudit_collection_from_record {Evidence Outcome : Type}
    (project : app.TrafficRecord → Evidence) (attribution : Evidence → Principal)
    (permitted : Evidence → Bool) (sample : List Evidence → PMF (List Evidence))
    (law : PMF Outcome) (readout : Outcome → List app.TrafficRecord)
    (who : Principal) (rate : ℝ)
    (coverage : ∀ actual record, record ∈ actual →
      attribution record = who → permitted record = false →
      rate ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (record : app.TrafficRecord)
    (present : ∀ outcome ∈ law.support, record ∈ readout outcome)
    (owner : attribution (project record) = who)
    (forbidden : permitted (project record) = false) :
    rate ≤ (((((law.map readout).bind
      (app.sampledTrafficAudit project attribution permitted sample)).map
        (fun verdict => verdict who)) true).toReal) := by
  rw [TerminalAudit.collection_probability]
  calc
    rate = expect law (fun _ => rate) := (expect_constant _ _).symm
    _ ≤ _ := by
      refine expect_mono ?_ (payoffIntegrable_constant _ _)
        (TerminalAudit.payoffIntegrable_charge _ _ _ _)
      intro outcome supported
      have projected : project record ∈ (readout outcome).map project :=
        List.mem_map.mpr ⟨record, present outcome supported, rfl⟩
      change _ ≤ (((app.sampledTrafficAudit project attribution permitted sample
        (readout outcome)).map (fun verdict => verdict who)) true).toReal
      rw [app.sampledTrafficAudit_collection]
      exact (coverage _ (project record) projected owner forbidden).trans
        (evidence_sampling_lower attribution permitted who _ (project record) owner forbidden)

namespace ResponseMenu

variable {app} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

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
theorem trafficAudit_collection_from_record {Evidence : Type}
    (project : app.TrafficRecord → Evidence) (attribution : Evidence → Principal)
    (permitted : Evidence → Bool) (sample : List Evidence → PMF (List Evidence))
    (who : Principal) (rate : ℝ)
    (coverage : ∀ actual record, record ∈ actual →
      attribution record = who → permitted record = false →
      rate ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (record : app.TrafficRecord)
    (present : record ∈ menu.trafficAudit initial horizon scheduler history)
    (owner : attribution (project record) = who)
    (forbidden : permitted (project record) = false) :
    rate ≤ ((((((menu.information initial horizon scheduler).runBehavioralFrom profile fuel
      history).map (menu.trafficAudit initial horizon scheduler)).bind
        (app.sampledTrafficAudit project attribution permitted sample)).map
          (fun verdict => verdict who)) true).toReal := by
  apply app.sampledTrafficAudit_collection_from_record project attribution permitted sample
    _ _ who rate coverage record _ owner forbidden
  intro final supported
  have path := (menu.protocol initial horizon scheduler).runRandomizedFor_reachesWithin
    ((menu.information initial horizon scheduler).randomizedChooser profile)
    fuel history final supported
  exact (menu.trafficAudit_reaches initial horizon scheduler path).subset present

/-- Only the first additional response is classified; subsequent play is
unrestricted. Persistent projected evidence retains the conditional charge bound. -/
theorem trafficAudit_collection_after_step {Evidence : Type}
    (project : app.TrafficRecord → Evidence) (attribution : Evidence → Principal)
    (permitted : Evidence → Bool) (sample : List Evidence → PMF (List Evidence))
    (who : Principal) (rate : ℝ)
    (coverage : ∀ actual record, record ∈ actual →
      attribution record = who → permitted record = false →
      rate ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (evidence : ∀ next ∈ ((menu.information initial horizon scheduler).runBehavioralFrom
      profile 1 history).support,
      ∃ record ∈ menu.trafficAudit initial horizon scheduler next,
        attribution (project record) = who ∧ permitted (project record) = false) :
    rate ≤ ((((((menu.information initial horizon scheduler).runBehavioralFrom profile
      (1 + fuel) history).map (menu.trafficAudit initial horizon scheduler)).bind
        (app.sampledTrafficAudit project attribution permitted sample)).map
          (fun verdict => verdict who)) true).toReal := by
  rw [(menu.information initial horizon scheduler).runBehavioralFrom_add,
    TerminalAudit.collection_probability,
    expect_bind_tower _ _ _ (TerminalAudit.payoffIntegrable_charge _ _ _ _)]
  calc
    rate = expect ((menu.information initial horizon scheduler).runBehavioralFrom profile 1
      history) (fun _ => rate) := (expect_constant _ _).symm
    _ ≤ _ := by
      refine expect_mono ?_ (payoffIntegrable_constant _ _) ?_
      rotate_left
      · exact payoffIntegrable_of_bounded _ _ (C := 1) fun next => by
          rw [abs_of_nonneg (expect_nonneg _ _ fun _ _ =>
            (TerminalAudit.charge_mem_Icc _ _ _ _).1)]
          exact expect_le_const _ _ (TerminalAudit.payoffIntegrable_charge _ _ _ _) _
            fun _ _ => (TerminalAudit.charge_mem_Icc _ _ _ _).2
      intro next supported
      obtain ⟨record, present, owner, forbidden⟩ := evidence next supported
      have bound := menu.trafficAudit_collection_from_record initial horizon scheduler
        project attribution permitted sample who rate coverage profile fuel next
          record present owner forbidden
      rwa [TerminalAudit.collection_probability] at bound

end ResponseMenu
end Interaction.ReactiveApplication
