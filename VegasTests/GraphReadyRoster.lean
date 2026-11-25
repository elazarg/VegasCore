module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Expr.Simple
public import Vegas.Pending.ReadyRosterService
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

def coinLaw : RationalLaw Bool where
  entries := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

def coin : EventCode layout (.publicData .bool) :=
  .sample (L := simpleExpr) BaseTy.bool {
    schema := []
    code := .weighted coinLaw
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
      (rosterInitialLaw graph input) 38
      (readyRosterScheduler graph leaks (ownerRoster graph) network)
      (fun event => event.val) (fun _ => 0) := by
  rw [← calendarLength]
  exact readyRoster_owner_contract graph leaks input network

end VegasTests.GraphReadyRoster
