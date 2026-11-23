module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.BoundedAuctionService
public import Vegas.Game.RosterSubmissionOpportunity
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
def rosters (event : graph.EventId) : List Player := (graph.actor? event).toList

abbrev rt : EventTimeouts graph := Vegas.timeouts (setup uniformPrior)
abbrev network := (idleNetwork rt) leaks
abbrev steps := (rosterPlan (setup uniformPrior) rosters).length

/-- The calendar and its guard use the public event and completion data. -/
def builder : ((reactiveApplication rt) leaks).Scheduler :=
  readyRosterScheduler (setup uniformPrior) leaks rosters network

private theorem plan_eq (prior : PMF (Player → Bid)) :
    rosterPlan (setup prior) rosters = rosterPlan (setup uniformPrior) rosters := rfl

private theorem prefix_eq (prior : PMF (Player → Bid)) (i : Nat) :
    rosterPlanPrefix (setup prior) rosters i = rosterPlanPrefix (setup uniformPrior) rosters i :=
  rfl

private theorem timeouts_eq (prior : PMF (Player → Bid)) : Vegas.timeouts (setup prior) = rt := rfl

private theorem builder_eq (prior : PMF (Player → Bid)) :
    readyRosterScheduler (setup prior) leaks rosters network = builder := by
  funext past view
  simp only [builder, readyRosterScheduler, rosterScheduler, plan_eq prior, rosterBlockCompleted,
    prefix_eq prior, timeouts_eq prior]
  cases located : (rosterPlan (setup uniformPrior) rosters)[past.length]? with
  | none => rfl
  | some pair =>
    obtain ⟨event, instruction⟩ := pair
    cases instruction <;> rfl

private def cursor (event : graph.EventId) : Nat :=
  (rosterPlanPrefix (setup uniformPrior) rosters event.val).length

private theorem unique_position (i : Nat) (event : graph.EventId) (who : Player)
    (found : (rosterPlan (setup uniformPrior) rosters)[i]? = some (event, .player who)) :
    i = cursor event := by
  let tag : graph.EventId × ServiceInstruction graph → Option graph.EventId
    | (target, .player _) => some target
    | _ => none
  have checked : ∀ index : Fin steps,
      (((rosterPlan (setup uniformPrior) rosters)[index.val]?).bind tag).all
        (fun target => index.val == cursor target) = true := by decide
  have bounded : i < steps := by
    by_contra! beyond
    rw [List.getElem?_eq_none beyond] at found
    cases found
  have yes := checked ⟨i, bounded⟩
  simpa only [found, Option.bind_some, tag, Option.all_some, beq_iff_eq] using yes

private theorem opportunities (prior : PMF (Player → Bid)) :
    ActorOpportunities (setup prior) rosters := by
  intro event owner owned
  change graph.actor? event = some owner at owned
  simp [rosters, owned]

theorem contract (prior : PMF (Player → Bid)) :
    AsyncContract rt leaks (Vegas.initialLaw (setup prior)) steps builder
      (fun event => event.val) (fun _ => 0) := by
  have supplied := readyRoster_contract (setup prior) leaks rosters network (opportunities prior)
  rw [builder_eq prior, plan_eq prior] at supplied
  exact supplied

theorem singleOpportunity (prior : PMF (Player → Bid)) :
    SingleSubmissionOpportunity (setup prior) rt leaks bounds steps builder := by
  simpa only [builder_eq prior, plan_eq prior, timeouts_eq prior, steps] using
    readyRoster_singleSubmissionOpportunity (setup prior) leaks rosters network cursor bounds
      (fun i e who found => unique_position i e who ((plan_eq prior) ▸ found))

instance finiteNature (prior : PMF (Player → Bid)) :
    ((reactiveApplication rt) leaks).FiniteNature (Vegas.initialLaw (setup prior)) builder := by
  simpa only [builder_eq prior, application, timeouts_eq prior] using
    @readyRoster_finiteNature Player _ simpleExpr _ (setup prior) leaks rosters
      (inferInstanceAs (setup prior).FiniteInitialLaw) (inferInstanceAs leaks.FiniteSupport) network

def specification (prior : PMF (Player → Bid)) :=
  fundedSpecification prior rt steps builder (finiteNature prior) _ _ (contract prior)
    (rosterScheduler_asyncTimely (setup prior))
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
    (rosterScheduler_asyncTimely (setup prior)) (singleOpportunity prior)

end Vegas.Examples.BoundedAuctionRoster
