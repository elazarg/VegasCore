/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRounds
import Interaction.ReactiveProtocol
import Interaction.ReactiveMessageReadout
import Interaction.ReactivePolicyMixture

/-! # Finitely branching reactive rounds

When every player response law and the application's own nature branch
finitely, so does every dispatched command. The standard policies are finitely
branching: silence is a point mass, a scheduled policy is one of
two policies, and a mixture over finitely many indices mixes finitely branching
policies.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- A policy branches finitely at every recall and view. -/
def Policy.FiniteSupport (policy : app.Policy) : Prop :=
  ∀ past view, (policy past view).support.Finite

end Interaction.ReactiveApplication
