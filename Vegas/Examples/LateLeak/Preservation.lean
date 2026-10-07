/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Intended

/-! # Late sends with leaked openings break sequential-equilibrium preservation

The intended game, in which the sender can only open at the protected turn,
has sequential equilibria, and all of them have the intended outcome law. The
late-turn game, which adds two late turns with a content-blind inclusion coin
of probability `99/100` and a listener who sees openings pending between them,
has no sequential equilibrium with that outcome law, although the forfeit is
three times the payoff range and the drop charge exceeds it.
-/

noncomputable section

namespace Vegas

/-- **No sequential equilibrium of the late-turn game preserves the intended
outcome.** The intended game has a sequential equilibrium; each of its
sequential equilibria has the intended outcome law, in which every type opens
at the protected turn and the listener answers safely; and no sequential
equilibrium of the late-turn game has that outcome law. -/
theorem lateLeak_intended_outcome_not_preserved :
    (∃ A : (lateLeakModel false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain false) (lateLeak_terminates false)
        (lateLeakPayoff false)) ∧
    (∀ A : (lateLeakModel false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain false) (lateLeak_terminates false)
          (lateLeakPayoff false) →
        lateLeakOutcomeLaw false A.strategy = lateLeakIntendedOutcome) ∧
    ∀ A : (lateLeakModel true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain true) (lateLeak_terminates true)
          (lateLeakPayoff true) →
        lateLeakOutcomeLaw true A.strategy ≠ lateLeakIntendedOutcome :=
  ⟨lateLeak_intended_equilibria.1, lateLeak_intended_equilibria.2,
    lateLeak_no_intended_equilibrium⟩

end Vegas
