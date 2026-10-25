/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Purification
import Vegas.Examples.CommitRevealAuction

/-! # Purification with integer binding payloads

The auction admits integer reports. Its conditional withholding policy has
finite action support at every view, so one finite pure-policy mixture can be
drawn before the initial state without a finite integer alphabet.
-/

noncomputable section

namespace Vegas.Tests.FiniteSupportPurification

open SourceProgram GameTheory
open Examples.CommitRevealAuction

def sourceProfile (report : Int) : BehavioralProfile program :=
  valueBindingProfile (profile report)

theorem finiteSupport (report : Int) (who : Player) :
    (sourceProfile report who).HasFiniteSupport program := by
  cases who <;>
    simp [sourceProfile, valueBindingProfile, profile, aliceStrategy, bobStrategy,
      BehavioralPolicy.HasFiniteSupport, program, alicePolicy, bobPolicy, PMF.support_pure]

instance : setup.FiniteInitialLaw where
  support_finite := by
    change (PMF.pure _).support.Finite
    simp

/-- The mixture serves all initial branches and is drawn before the setup. -/
theorem integer_policy_purifies (report : Int) :
    ∃ mixture : PMF (PurePolicy Player.alice program), mixture.support.Finite ∧
      setup.run (Function.update (sourceProfile report) .alice (alicePolicy report)) =
        mixture.bind fun choice =>
          setup.run (Function.update (sourceProfile report) .alice
            (PurePolicy.toBehavioral program choice)) := by
  apply exists_pureMixture_run setup (sourceProfile report) (alicePolicy report)
  · exact finiteSupport report
  · exact finiteSupport report .alice

end Vegas.Tests.FiniteSupportPurification
