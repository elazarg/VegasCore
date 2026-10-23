/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSchedulerFinishSeed
import GameTheory.Math.Probability.Support

/-! # Terminal readouts under the original scheduler posterior -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- The original scheduler mixture integrates the actual endpoint posterior.
This identity keeps the remaining physical execution law before any readout. -/
theorem schedulerMixture_finish_marginal {Seed : Type} (prior : PMF Seed)
    (family : Seed → app.Scheduler) (initial : PMF app.State) (horizon : Nat)
    (players : Principal → app.Policy) (state : app.ProtocolState) :
    (match state with
      | none => prior
      | some current => (app.schedulerMixture prior family).posterior
          current.execution.environmentRecall).bind
        (fun seed => app.finish initial horizon (family seed) players state) =
      app.finish initial horizon (app.schedulerMixture prior family).scheduler players state := by
  have joint := congrArg (PMF.map Prod.fst)
    (app.schedulerMixture_finish_joint prior family initial horizon players state)
  have identity (law : PMF app.ProtocolState) : law.map (fun current => current) = law :=
    PMF.map_id _
  have constant (law : PMF Seed) (current : app.ProtocolState) :
      law.map (fun _ => current) = PMF.pure current := PMF.map_const _ _
  have bindIdentity (law : PMF app.ProtocolState) :
      law.bind (fun current => PMF.pure current) = law := PMF.bind_pure _
  cases state <;>
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, identity, constant,
      bindIdentity] using joint

end Interaction.ReactiveApplication
