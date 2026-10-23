/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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

namespace ResponseMenu

variable {app} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- The original raw-history readout, restricted to this response menu. -/
def trafficAudit (history : (menu.protocol initial horizon scheduler).History) :
    List app.TrafficRecord :=
  app.trafficAudit initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.trace)

theorem trafficAudit_reaches
    {first last : (menu.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (menu.protocol initial horizon scheduler).ReachesWithin fuel first last) :
    menu.trafficAudit initial horizon scheduler first <+:
      menu.trafficAudit initial horizon scheduler last :=
  app.trafficAudit_reaches initial horizon scheduler
    (menu.reaches_raw initial horizon scheduler path)

variable [Fintype Principal]

end ResponseMenu
end Interaction.ReactiveApplication
