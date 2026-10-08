/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceContinuationBridge
import Vegas.Game.SourceServiceChoiceSupport
import Vegas.Pending.ReactiveServiceFiniteness
import Vegas.Compile.EventGraphDeviation

/-! # Finite support of the timed source service

The timed compilation of a source profile branches finitely: fresh binding
values are finite because the service covers them, the timing draw ranges over
finitely many slots, and silence is a single response.
With the service's finitely branching prior and leak rule, every reserved phase
of the actual service therefore has a finitely supported law, and so do the
source continuations it is compared with.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem sourceServicePolicy_finiteSupport (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (finite : setup.program.FiniteBindingTypes) (profile : BehavioralProfile setup.program)
    (who : Player) :
    ReactiveApplication.Policy.FiniteSupport _ (sourceServicePolicy setup leaks profile who) := by
  intro past view
  have finiteActions := Vegas.toEventGraph_finiteActions setup.program finite
  unfold sourceServicePolicy
  split
  · split
    · simp
    · split
      · rw [PMF.support_map]
        exact ((Set.finite_univ_iff.mpr (finiteActions _)).subset (Set.subset_univ _)).image _
      · simp
  · simp

theorem sourceServiceOpportunity_finiteSupport (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (finite : setup.program.FiniteBindingTypes) (profile : BehavioralProfile setup.program)
    (who : Player) (event : (graph setup).EventId) :
    ReactiveApplication.Policy.FiniteSupport _
      (sourceServiceOpportunity setup leaks profile who event) := by
  intro past view
  unfold sourceServiceOpportunity
  split
  · exact (application setup leaks).silentPolicy_finiteSupport past view
  · refine bind_support_finite
      (sourceServicePolicy_finiteSupport setup leaks finite profile who past view)
      fun response _ => ?_
    split
    · exact (application setup leaks).silentPolicy_finiteSupport past view
    · simp

theorem sourceServiceTimedFamily_finiteSupport (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (finite : setup.program.FiniteBindingTypes) (profile : BehavioralProfile setup.program)
    (who : Player) (event : (graph setup).EventId) (slot : Fin ((rosters event).count who)) :
    ReactiveApplication.Policy.FiniteSupport _
      (sourceServiceTimedFamily setup leaks rosters profile who event slot) :=
  (application setup leaks).scheduledPolicy_finiteSupport _ _
    (sourceServiceOpportunity_finiteSupport setup leaks finite profile who event)
    (application setup leaks).silentPolicy_finiteSupport

theorem sourceServiceTimedPolicy_finiteSupport (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (timing : TimingLaw setup rosters)
    (finite : setup.program.FiniteBindingTypes) (profile : BehavioralProfile setup.program)
    (who : Player) :
    ReactiveApplication.Policy.FiniteSupport _
      (sourceServiceTimedPolicy setup leaks rosters timing profile who) := by
  intro past view
  unfold sourceServiceTimedPolicy
  split
  · exact (application setup leaks).silentPolicy_finiteSupport past view
  · split
    · exact (application setup leaks).policyMixture_finiteSupport _
        (sourceServiceTimedFamily_finiteSupport setup leaks rosters finite profile who _)
        past view
    · exact (application setup leaks).silentPolicy_finiteSupport past view

variable [Fintype Player]

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

omit [Fintype Player] in
/-- The service's fresh binding alphabets are finite, since it covers them. -/
theorem finiteBindingTypes : service.setup.program.FiniteBindingTypes :=
  sourceService_finiteBindingTypes service.setup service.bounds service.values

theorem players_finiteSupport (who : Player) :
    ReactiveApplication.Policy.FiniteSupport _ (approx.players who) :=
  sourceServiceTimedPolicy_finiteSupport service.setup service.leaks service.rosters
    approx.timing (finiteBindingTypes (service := service)) approx.profile who

theorem phaseLaw_support_finite {who : Player}
    {execution : (application service.setup service.leaks).Execution}
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action) :
    (approx.phaseLaw phase response).support.Finite :=
  (runtime service.setup).runInteractionPlan_support_finite_of_no_wire service.leaks
    approx.players_finiteSupport service.network phase.tail phase.tail_no_wire _

theorem phaseConfigLaw_support_finite {who : Player}
    {execution : (application service.setup service.leaks).Execution}
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action) :
    (approx.phaseConfigLaw phase response).support.Finite := by
  rw [phaseConfigLaw, PMF.support_map]
  exact (approx.phaseLaw_support_finite phase response).image _

theorem responseReadout_support_finite {who : Player}
    {execution : (application service.setup service.leaks).Execution}
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action) :
    (approx.responseReadout phase response).support.Finite := by
  rw [responseReadout, PMF.support_map]
  exact (ReactiveApplication.runToHorizon_support_finite
    (ReactiveApplication.FiniteNature.scheduler_finite (initial := initialLaw service.setup))
    approx.players_finiteSupport _ _).image _

theorem boundaryContinuation_support_finite (count : Nat)
    (config : (graph service.setup).Config) :
    (approx.boundaryContinuation count config).support.Finite := by
  rw [boundaryContinuation, PMF.support_map]
  exact (service.setup.continuationLaw_support_finite approx.profile
    ((finiteBindingTypes (service := service)).profileFiniteSupport _ approx.profile) _).image _

end TimedApproximant

end Vegas
