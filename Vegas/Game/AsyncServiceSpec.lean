/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRuntime
import Vegas.Pending.ReactiveAsyncContract
import Vegas.Pending.ReactiveCompiledMenu
import Vegas.Pending.ReactiveBoundedValues

/-! # Full-source services under an asynchronous scheduler

`Vegas.AsyncServiceSpec` is the full-source native service with an arbitrary
public scheduler in place of the roster calendar: the program setup, passive
observation rule and message bounds with the compiler's side conditions on
them, a horizon, and a scheduler satisfying the asynchronous contract with
per-event reaction bounds `delay` and inclusion bounds `bound` that leave room
before every deadline. It has no rosters and no activation opportunities: the
contract's opportunity clause replaces them.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

/-- The full-source native service under an asynchronous scheduler: the
program setup, passive observation rule and message bounds, with the
compiler's side conditions on them, and a scheduler satisfying the
asynchronous contract up to a fixed horizon, with bounds that fit every
deadline. -/
structure AsyncServiceSpec (Player : Type) [DecidableEq Player] (L : IExpr)
    [IExpr.ResultTypes L] where
  setup : Setup (Player := Player) (L := L)
  leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))
  bounds : MessageBounds (graph setup)
  /-- Every binding value the source can choose has a native message form. -/
  values : bounds.CoversBindingValues
  /-- Every supported initial binding table fits the candidate catalogue. -/
  initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state
  /-- The candidate catalogue has a slot for every event. -/
  capacity : (graph setup).order.eventCount ≤ bounds.candidateCount
  /-- The number of scheduler rounds. -/
  horizon : Nat
  /-- The public scheduler: activations, inclusions, clock, sampling and expiry. -/
  scheduler : (application setup leaks).Scheduler
  /-- Per-event reaction bound: slots before the owner's first activation. -/
  delay : (graph setup).EventId → Nat
  /-- Per-event inclusion bound for an owner's sole packet. -/
  bound : (graph setup).EventId → Nat
  contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay bound
  /-- Every owned event's reaction and inclusion fit before its deadline. -/
  timely : AsyncTimely (runtime setup) delay bound
  /-- The prior over initial states is finitely supported. -/
  initialFinite : setup.FiniteInitialLaw
  /-- The leak rule branches finitely. -/
  leaksFinite : leaks.FiniteSupport
  /-- The scheduler branches finitely. -/
  schedulerFinite : ∀ past view, (scheduler past view).support.Finite

attribute [instance] AsyncServiceSpec.initialFinite AsyncServiceSpec.leaksFinite

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace AsyncServiceSpec

variable (service : AsyncServiceSpec Player L)

/-- All of the service's nature branches finitely: the prior, the leak rule and
the scheduler. -/
instance finiteNature :
    (application service.setup service.leaks).FiniteNature (initialLaw service.setup)
      service.scheduler where
  initial_finite := by
    rw [initialLaw, PMF.support_map]
    exact service.setup.initialLaw_support_finite.image _
  scheduler_finite := service.schedulerFinite

/-- The scheduler completes every event by the horizon. -/
theorem completes : CompletesPlay (runtime service.setup) service.leaks
    (initialLaw service.setup) service.horizon service.scheduler :=
  service.contract.completes

end AsyncServiceSpec

end Vegas

-- OPEN OBLIGATION: Asynchronous sequential-equilibrium preservation
-- Prove every source sequential equilibrium has a bounded raw-runtime
-- equilibrium under any AsyncServiceSpec, preserving the joint source outcome
-- and realized settlement law. Retained slot invariants, prescribed policy
-- admission after misses and prescribed continuation bounds are checked.
-- The candidate owner-local risk menu, post-miss base-payoff rationality equivalence and a
-- localized restriction-extension theorem are checked; their source embedding
-- and runtime comparison premises remain open.
-- Exact first-turn play keeps the owner's full service-risk flag clear against
-- arbitrary foreign raw policies. Prescribed authored packets pass the actual
-- settled record for any turn timing; authentic sampling and first-turn absence
-- of public misses give zero owner charge. These results do not establish the
-- strategic source embedding or the local clean-continuation comparisons.
-- Prescribed responses are locally admitted at clear risk-menu histories, even
-- after foreign raw branches. Actual supported responses supply completion
-- boundaries and the generic continuation-error bridge within the raw horizon.
-- At every legal clear active owner prefix, one immediate policy preserves actual
-- recall through earlier deferrals and has zero owner audit charge throughout its
-- supported raw suffix within the horizon. The prefix packet and opportunity
-- premises are derived from that legal history. Whole-policy replacement in the
-- risk-menu game has that actual continuation law. One fixed comparator has zero
-- owner collection across every hidden history of a clear information site;
-- terminal base bounds give its clean lower bound under any belief. The source
-- equilibrium embedding remains open. Constructor breaches, wrong current-event
-- handles and public guard failures have actual terminal collection bounds
-- from authentic final-record challenge coverage. Their information-local
-- classifier reconstructs the actual envelope from own recall and view. The
-- risk-menu-to-effective SE extension derives the clean comparator, collection
-- and fixed-deposit bound; other excluded-action comparisons remain hypotheses.
-- Exact private-alias transport supplies the final bounded raw-runtime stage.
-- Exact first-turn execution preserves the joint typed outcome and actual
-- sampled payoff vector for every source profile after disclosure normalization.
-- This physical law does not establish a behavioral equilibrium embedding.
-- Actual binding and resolution decisions, public sampling and stopped silent
-- continuations have source-conditioned full traffic kernels. Native input
-- likelihoods after retained deferrals, relative escape bounds and original
-- source belief transport remain open. The auxiliary risk-menu source embedding,
-- conditional incentives and general continuation repair still require proofs.
-- False source resolutions emit authenticated evidence-free withholding packets.
-- Silence is retained waiting, whose local incentives and source likelihood
-- transport remain separate proof obligations.
-- The fixed-calendar SourceServiceSpec capstone does not discharge this edge.
