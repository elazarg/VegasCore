/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveRounds

/-! # Scheduler laws implemented through restricted observations

The runtime exposes a complete public network view to a scheduler. A backend
with less visibility can implement a particular scheduler when its command law
factors through the backend's observation. This is a law equality, so the
adapter preserves execution probabilities for arbitrary player policies.
Restricting scheduler support alone does not supply this certificate.
-/

namespace Interaction.ReactiveApplication

variable {Principal : Type} (app : ReactiveApplication Principal)

/-- Implement a scheduler using only the observation supplied by a backend. -/
def Scheduler.ofObservation {Observation : Type}
    (observe : List app.EnvironmentEntry → app.EnvironmentView → Observation)
    (choose : Observation → PMF app.Command) : app.Scheduler :=
  fun past view => choose (observe past view)

end Interaction.ReactiveApplication
