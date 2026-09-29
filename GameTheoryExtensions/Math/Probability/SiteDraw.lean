/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Product
import Mathlib.Data.Fintype.Pi

/-! # Independent draws at finitely many sites

A pure strategy fixes one value at every site, while a behavioral one draws a
value at a site only when it is reached. Drawing independently at each of
finitely many listed sites, and keeping a fallback elsewhere, gives a law on
whole assignments whose value at each listed site has that site's law.
-/

noncomputable section

namespace GameTheory.Math.Probability

variable {Site Value Result : Type*}

/-- Draw independently at each listed site; unlisted sites keep their fallback. -/
def drawAtSites (law : Site → PMF Value) (sites : Finset Site) (fallback : Site → Value) :
    PMF (Site → Value) := by
  classical
  exact (independentProduct fun site : sites => law site.1).map fun draw site =>
    if listed : site ∈ sites then draw ⟨site, listed⟩ else fallback site

/-- A continuation reading only one listed site sees exactly that site's law. -/
theorem drawAtSites_bind_apply (law : Site → PMF Value) (sites : Finset Site)
    (fallback : Site → Value) {site : Site} (listed : site ∈ sites)
    (next : Value → PMF Result) :
    (drawAtSites law sites fallback).bind (fun assignment => next (assignment site)) =
      (law site).bind next := by
  classical
  have marginal := independentProduct_map_eval (fun site : sites => law site.1) ⟨site, listed⟩
  unfold drawAtSites
  rw [PMF.bind_map, ← marginal, PMF.bind_map]
  congr 1
  funext draw
  simp only [Function.comp_apply, listed, ↓reduceDIte]

/-- Finitely many sites with finitely supported laws draw finitely many
assignments. -/
theorem drawAtSites_support_finite (law : Site → PMF Value) (sites : Finset Site)
    (fallback : Site → Value) (finite : ∀ site ∈ sites, (law site).support.Finite) :
    (drawAtSites law sites fallback).support.Finite := by
  classical
  unfold drawAtSites
  rw [PMF.support_map]
  refine Set.Finite.image _ ((Set.Finite.pi fun site : sites => finite site.1 site.2).subset ?_)
  intro draw supported
  exact fun site _ => (independentProduct_support_iff _ draw).mp supported site

end GameTheory.Math.Probability
