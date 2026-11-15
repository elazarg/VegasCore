module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import VegasTests.EventCompilation
public import VegasTests.AbsorbingFailure
public import Vegas.EventGraph.DependencyRelaxation

@[expose] public section

/-! # Dependency choices on two private bindings and two reveals

The existing source fixture numbers one owner's binding and reveal as 0 and 2,
and the other's as 1 and 3. Ready sets distinguish evaluation dependencies
from source information order and the two independent relaxations.
-/

noncomputable section

namespace VegasTests.DependencyLayers

open Vegas EventGraph

abbrev dataflowGraph := toEventGraph EventCompilation.pairSource
abbrev informationGraph := toInformationGraph EventCompilation.pairSource
abbrev revealGraph := informationGraph.relaxReveals
abbrev bindingGraph := informationGraph.relaxBindings
abbrev combinedGraph := informationGraph.relaxReveals.relaxBindings

/-- A cut with precisely the first `length` events completed. -/
private def prefixCut (order : EventOrder) (length : Nat) : order.Cut where
  completed := Finset.univ.filter fun event => event.val < length
  predecessor_closed := by
    intro event completed prior predecessor
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at completed ⊢
    exact lt_trans (order.predecessor_lt predecessor) completed

private theorem binding_independence (prior event : Fin 4) :
    informationGraph.IndependentBindings prior event ↔
      prior.val < 2 ∧ event.val < 2 ∧ prior ≠ event := by
  have layout (event : Fin 4) : dataflowGraph.outputLayout event =
      if event.val < 2 then .binding (event.val == 1) .bool else .publication .bool := by
    fin_cases event <;> rfl
  fin_cases prior <;> fin_cases event <;>
    simp [IndependentBindings, layout]

private theorem relaxed_binding_independence (prior event : Fin 4) :
    informationGraph.relaxReveals.IndependentBindings prior event ↔
      prior.val < 2 ∧ event.val < 2 ∧ prior ≠ event :=
  binding_independence prior event

example :
    (prefixCut dataflowGraph.order 0).enabled = ({0, 1} : Finset (Fin 4)) ∧
    (prefixCut dataflowGraph.order 1).enabled = ({1, 2} : Finset (Fin 4)) := by
  decide

example :
    (prefixCut informationGraph.order 0).enabled = ({0} : Finset (Fin 4)) ∧
    (prefixCut informationGraph.order 2).enabled = ({2} : Finset (Fin 4)) := by
  decide

example :
    (prefixCut revealGraph.order 0).enabled = ({0} : Finset (Fin 4)) ∧
    (prefixCut revealGraph.order 2).enabled = ({2, 3} : Finset (Fin 4)) := by
  constructor <;> ext event <;>
    simp only [EventOrder.Cut.mem_enabled, EventOrder.Cut.Ready, prefixCut,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_iff,
    relaxReveals_predecessors, IndependentReveals]
  all_goals fin_cases event <;> decide

example :
    (prefixCut bindingGraph.order 0).enabled = ({0, 1} : Finset (Fin 4)) ∧
    (prefixCut bindingGraph.order 2).enabled = ({2} : Finset (Fin 4)) := by
  constructor <;> ext event <;>
    simp only [EventOrder.Cut.mem_enabled, EventOrder.Cut.Ready, prefixCut,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_iff,
    relaxBindings_predecessors, binding_independence]
  all_goals fin_cases event <;> decide

example :
    (prefixCut combinedGraph.order 0).enabled = ({0, 1} : Finset (Fin 4)) ∧
    (prefixCut combinedGraph.order 2).enabled = ({2, 3} : Finset (Fin 4)) ∧
    (prefixCut combinedGraph.order 1).enabled = ({1} : Finset (Fin 4)) := by
  refine ⟨?_, ?_, ?_⟩ <;> ext event <;>
    simp only [EventOrder.Cut.mem_enabled, EventOrder.Cut.Ready, prefixCut,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_iff,
    relaxBindings_predecessors, relaxReveals_predecessors,
    relaxed_binding_independence, IndependentReveals]
  all_goals fin_cases event <;> decide

example : combinedGraph = informationGraph.relaxBindings.relaxReveals :=
  informationGraph.relaxReveals_relaxBindings

example (event : Fin 4) :
    dataflowGraph.order.predecessors event ⊆ combinedGraph.order.predecessors event :=
  informationGraph.dataflow_predecessors_subset_combinedRelaxation event

example (event : Fin 4) :
    combinedGraph.order.predecessors event ⊆ revealGraph.order.predecessors event ∧
    combinedGraph.order.predecessors event ⊆ bindingGraph.order.predecessors event := by
  constructor
  · exact revealGraph.relaxBindings_predecessors_subset event
  · intro prior member
    obtain ⟨revealed, notBinding⟩ :=
      (revealGraph.relaxBindings_predecessors prior event).mp member
    exact (informationGraph.relaxBindings_predecessors prior event).mpr
      ⟨((informationGraph.relaxReveals_predecessors prior event).mp revealed).1, notBinding⟩

/-- Per-owner service can be unambiguous without source information barriers. -/
example : dataflowGraph.ActorSerial ∧ ¬ dataflowGraph.BarrierOrdered := by
  refine ⟨?_, ?_⟩
  · have owners (event : Fin 4) :
        dataflowGraph.actor? event = some (event.val % 2 == 1) := by
      fin_cases event <;> rfl
    intro event cut other who ready otherReady actor otherActor
    have same := actor.trans otherActor.symm
    rw [owners event, owners other] at same
    fin_cases event <;> fin_cases other
    all_goals first
      | rfl
      | exact (ready.1 (otherReady.2 (by decide))).elim
      | exact (otherReady.1 (ready.2 (by decide))).elim
      | cases (Option.some.inj same)
  · intro ordered
    have missing : (1 : Fin 4) ∉ dataflowGraph.order.predecessors (2 : Fin 4) := by decide
    exact missing (ordered (2 : Fin 4) (by decide))

/-- Declared reads alone can leave two bindings of one owner ready together. -/
example : ¬ (toEventGraph AbsorbingFailure.twoBindings).ActorSerial := by
  intro serial
  have same : (1 : Fin 4) = 0 := serial.ready_actor_unique
    (prefixCut _ 0) (event := (0 : Fin 4)) (other := (1 : Fin 4))
    (by decide) (by decide) rfl rfl
  exact (by decide : (1 : Fin 4) ≠ 0) same

/-- Binding relaxation keeps the information edge between the same owner's bindings. -/
example : (0 : Fin 4) ∈
    (toInformationGraph AbsorbingFailure.twoBindings).relaxBindings.order.predecessors
      (1 : Fin 4) := by
  rw [relaxBindings_predecessors]
  refine ⟨by decide, ?_⟩
  rintro ⟨left, right, _, _, _, _, different⟩
  exact different (Subsingleton.elim left right)

end VegasTests.DependencyLayers
