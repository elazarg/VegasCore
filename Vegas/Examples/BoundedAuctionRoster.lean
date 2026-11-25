module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.BoundedAuctionService
public import Vegas.Game.RosterSubmissionOpportunity
public import Vegas.Game.SourceServiceFacts
public import Vegas.Pending.ReactiveMonitoring

@[expose] public section

/-! # A fixed single-opportunity builder for every bounded auction prior -/

noncomputable section

namespace Vegas.Examples.BoundedAuctionRoster

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability
open BoundedPrivateValueAuction
open BoundedAuctionService (leaks fundedSpecification truthful_single_opportunity)
open CommitRevealAuction (Player)

/-- Offer a single activation to the tagged event's owner. -/
def rosters (event : graph.EventId) : List Player :=
  ownerRoster (setup uniformPrior).dataflowGraph event

abbrev rt : EventTimeouts graph := Vegas.timeouts (setup uniformPrior)
abbrev network := (idleNetwork rt) leaks
abbrev steps := (rosterPlan (setup uniformPrior).dataflowGraph rosters).length

/-- The calendar and its guard use the public event and completion data. -/
def builder : ((reactiveApplication rt) leaks).Scheduler :=
  readyRosterScheduler (setup uniformPrior).dataflowGraph leaks rosters network

theorem contract (prior : PMF (Player → Bid)) :
    AsyncContract rt leaks (Vegas.initialLaw (setup prior)) steps builder
      (fun event => event.val) (fun _ => 0) := by
  let inputs := (setup prior).initialLaw.map (setup prior).eventInputs
  have initial : Vegas.initialLaw (setup prior) =
      rosterInitialLaw (setup prior).dataflowGraph inputs :=
    serviceInitialLaw_eq_inputs (setup prior)
  rw [initial]
  exact readyRoster_owner_contract (setup prior).dataflowGraph leaks inputs network

theorem singleOpportunity (prior : PMF (Player → Bid)) :
    SingleSubmissionOpportunity (setup prior) rt leaks bounds steps builder :=
  readyRoster_singleSubmissionOpportunity_of_length_le_one (setup prior) leaks rosters network
    bounds (ownerRoster_length_le_one (setup prior).dataflowGraph)

instance finiteNature (prior : PMF (Player → Bid)) :
    ((reactiveApplication rt) leaks).FiniteNature (Vegas.initialLaw (setup prior)) builder := by
  let inputs := (setup prior).initialLaw.map (setup prior).eventInputs
  have initial : Vegas.initialLaw (setup prior) =
      rosterInitialLaw (setup prior).dataflowGraph inputs :=
    serviceInitialLaw_eq_inputs (setup prior)
  rw [initial]
  let : Fact inputs.support.Finite := ⟨by
    rw [show inputs = (setup prior).initialLaw.map (setup prior).eventInputs from rfl,
      PMF.support_map]
    exact (setup prior).initialLaw_support_finite.image _⟩
  let finiteLeaks : leaks.FiniteSupport :=
    inferInstanceAs (MessageNetwork.ObservationRule.allPending
      (Principal := Player) (Payload := WitnessedPacket graph)).FiniteSupport
  exact @readyRoster_finiteNature Player _ simpleExpr _ (setup prior).dataflowGraph leaks rosters
    inputs ‹Fact inputs.support.Finite› finiteLeaks network

def specification (prior : PMF (Player → Bid)) :=
  fundedSpecification prior rt steps builder (finiteNature prior) _ _ (contract prior)
    (rosterScheduler_asyncTimely (setup prior).dataflowGraph)
    (.singleOpportunity (by decide) (singleOpportunity prior))

/-- The same public builder realizes a truthful sequential equilibrium and the exact
joint law of truthful terminal configurations and bidder surplus for every joint prior. -/
theorem native_equilibrium (prior : PMF (Player → Bid)) :
    ∃ compiled : ClientCompilation (specification prior) (truthfulAssessment prior),
      ((bounds.rawMenu rt leaks).run (Vegas.initialLaw (setup prior)) steps builder
        compiled.assessment.strategy).bind (fun final =>
          (specification prior).observation final.state) =
          prior.map (fun types => (some (finalConfig types (types .alice) (types .bob)),
            surplus types (types .alice) (types .bob))) :=
  truthful_single_opportunity prior rt steps builder (finiteNature prior) _ _ (contract prior)
    (rosterScheduler_asyncTimely (setup prior).dataflowGraph) (singleOpportunity prior)

end Vegas.Examples.BoundedAuctionRoster
