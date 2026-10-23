/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveResponseEmbedding
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison

/-! # Exact stopped continuation laws under response-menu embedding

Embedding the actual menu policy preserves the complete history law stopped at
any raw-history predicate, including from arbitrary off-path menu histories.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- A response-menu embedding preserves any stopped law of entire histories. -/
theorem runBehavioralUntil_embed
    (rawCertificate : (app.protocol initial horizon scheduler).WellFoundedHistories)
    (menuCertificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (stop : (app.protocol initial horizon scheduler).History → Prop)
    (history : (menu.protocol initial horizon scheduler).History) :
    ((menu.information initial horizon scheduler).runBehavioralUntil menuCertificate profile
      (fun history => stop (menu.toRawHistory initial horizon scheduler history)) history).map
        (menu.toRawHistory initial horizon scheduler) =
      (app.information initial horizon scheduler).runBehavioralUntil rawCertificate
        (fun who => menu.embedPolicy initial horizon scheduler who (profile who)) stop
        (menu.toRawHistory initial horizon scheduler history) := by
  classical
  let embed := menu.toRawHistory initial horizon scheduler
  let raw := app.information initial horizon scheduler
  let bounded := menu.information initial horizon scheduler
  have compared := raw.runBehavioralUntil_map_eq_of_paired_steps bounded
    rawCertificate menuCertificate
    (fun who => menu.embedPolicy initial horizon scheduler who (profile who)) profile
    stop (fun history => stop (embed history)) id embed
    (fun first second => first = embed second)
    (by intro first second same; subst first; rfl)
    (by intro first second same _halt; exact same)
    (by
      intro first second same _going _running
      subst first
      let law := bounded.runBehavioralFrom profile 1 second
      refine ⟨law.map (fun next => (embed next, next)), ?_, ?_, ?_⟩
      · rw [PMF.map_comp]
        change law.map embed = _
        exact menu.run_embed initial horizon scheduler profile 1 second
      · rw [PMF.map_comp]
        change law.map id = law
        exact PMF.map_id law
      · intro next supported
        obtain ⟨child, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        rfl)
    (embed history) history rfl
  simpa only [PMF.map_id] using compared.symm

end Interaction.ReactiveApplication.ResponseMenu
