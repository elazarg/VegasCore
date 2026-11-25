module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Expr.Simple
public import Vegas.Pending.ReadyRosterService
public import Vegas.Pending.SingleOwnerSimulation
public import Interaction.MessageNetworkObservation

@[expose] public section

/-! # The owner roster on a hand-built graph with chance and bindings -/

noncomputable section

namespace VegasTests.GraphReadyRoster

open Vegas EventGraph EventGraphRuntime GameTheory.Math.Probability Interaction

abbrev order : EventOrder where
  eventCount := 6
  predecessors _ := ∅
  predecessor_lt := by simp

abbrev inputLayout : Fin 1 → EventField Bool simpleExpr := fun _ => .publicData .bool

abbrev outputLayout : Fin 6 → EventField Bool simpleExpr :=
  Fin.cases (.publicData .bool) fun _ => .binding false .bool

abbrev layout := fieldLayout inputLayout outputLayout

def coinDistribution : RationalDistribution Bool where
  entries := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

def coin : EventCode layout (.publicData .bool) :=
  .sample (L := simpleExpr) BaseTy.bool {
    schema := []
    code := .weighted coinDistribution
    reads := fun ref => nomatch ref
    readFields := ∅
    reads_mem := fun ref => nomatch ref
  }

abbrev graph : Vegas.EventGraph Bool simpleExpr where
  inputCount := 1
  order := order
  inputLayout := inputLayout
  outputLayout := outputLayout
  nodes := Fin.cases coin (fun _ => .bind (L := simpleExpr) false BaseTy.bool)
  reads_available := by
    intro event field member
    refine Fin.cases ?_ (fun _ => ?_) event member
    · intro member
      change field ∈ coin.readFields at member
      simp [coin, EventCode.readFields] at member
    · intro member
      change field ∈ (∅ : Finset _) at member
      exact False.elim (Finset.notMem_empty field member)
  payoffs := []

abbrev leaks : MessageNetwork.ObservationRule Bool (WitnessedPacket graph.sequentialize) :=
  MessageNetwork.ObservationRule.allPending

abbrev network : (NetworkPolicy (rosterTimeouts graph)) leaks :=
  fun _ _ => PMF.pure .wait

example : ((rosterBlock graph (ownerRoster graph) 0)[0]?) =
    some (.sample ⟨0, by decide⟩) := rfl

example : ((rosterBlock graph (ownerRoster graph) 1)[0]?) =
    some (.player false) := rfl

theorem calendarLength : (rosterPlan graph (ownerRoster graph)).length = 38 := by decide

theorem contract (input : PMF graph.Inputs) :
    AsyncContract (rosterTimeouts graph) leaks
      (rosterInitialDistribution graph input) 38
      (readyRosterScheduler graph leaks (ownerRoster graph) network)
      (fun event => event.val) (fun _ => 0) := by
  rw [← calendarLength]
  exact readyRoster_owner_contract graph leaks input network

/-- One policy realizes all six physical prefixes for any raw deviation of the
owner of the five bindings, including deviations after seeing the coin. -/
theorem deviation_prefix_distribution (inputs : PMF graph.Inputs)
    (reference : graph.sequentialize.BehavioralProfile)
    (deviation : (rosterApplication graph leaks).Policy) :
    let scheduler := readyRosterScheduler graph leaks (ownerRoster graph) network
    let players := Function.update (turnPolicy (rosterTimeouts graph) leaks (fun _ => 0) 1
      (EventGraphRuntime.firstTurnTiming graph.sequentialize 1) reference) false deviation
    ∃ policy : graph.sequentialize.BehavioralPolicy false,
      ∀ rank, rank ≤ 6 →
        (physicalPrefix (rosterTimeouts graph) leaks scheduler players inputs 38 rank).map
          (fun execution => Config.rankPrefix rank execution.application.config) =
        inputs.bind fun seed => graph.sequentialize.runPlan
          (graph.sequentialize.policyPlan (Function.update reference false policy)
            graph.sequentialize.canonicalScheduler) rank (Config.initial seed) := by
  intro scheduler players
  have actors : ∀ event : graph.sequentialize.EventId,
      graph.sequentialize.actor? event = none ∨ graph.sequentialize.actor? event = some false := by
    decide
  obtain ⟨policy, prefixes, _⟩ := singleOwner_deviation_config_distribution
    (rosterTimeouts graph) leaks
    scheduler (fun _ => 0) 1 (EventGraphRuntime.firstTurnTiming graph.sequentialize 1) reference
    false deviation inputs 38 (contract inputs).completes actors
  exact ⟨policy, prefixes⟩

end VegasTests.GraphReadyRoster
