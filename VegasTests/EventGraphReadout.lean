/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Commutation
import Vegas.Expr.Simple

/-! # Event-graph typed readout regressions

This hand-built graph has one private initial binding, one public integer chance
event, and one Boolean publication event resolving that binding. The two events
are independent and ready together, while their output types remain distinct.
-/

namespace VegasTests.EventGraphReadout

open Vegas
open GameTheory.Math.Probability

noncomputable section

private abbrev readoutOrder : EventOrder where
  eventCount := 2
  predecessors _ := ∅
  predecessor_lt := by simp

private abbrev readoutInputs : Fin 1 → Vegas.EventGraph.EventField Bool simpleExpr :=
  fun _ => .binding false .bool

private abbrev readoutOutputs : Fin 2 → Vegas.EventGraph.EventField Bool simpleExpr :=
  Fin.cases (.publicData .int) fun _ => .publication .bool

private abbrev readoutLayout :=
  Vegas.EventGraph.fieldLayout readoutInputs readoutOutputs

private def fairInt : RationalLaw Int where
  entries := [(2, 1 / 2), (8, 1 / 2)]
  normalized := by norm_num

private def chanceCode :
    Vegas.EventGraph.EventCode (Player := Bool) (L := simpleExpr)
      readoutLayout (.publicData BaseTy.int) :=
  Vegas.EventGraph.EventCode.sample (layout := readoutLayout) BaseTy.int {
    schema := []
    code := .weighted fairInt
    reads := fun ref => nomatch ref
    readFields := ∅
    reads_mem := fun ref => nomatch ref
  }

private def initialBinding :
    Vegas.EventGraph.FieldRef (Player := Bool) (L := simpleExpr)
      readoutLayout (.binding false .bool) :=
  ⟨.inl 0, rfl⟩

private def resolveCode :
    Vegas.EventGraph.EventCode (Player := Bool) (L := simpleExpr)
      readoutLayout (.publication BaseTy.bool) :=
  Vegas.EventGraph.EventCode.resolve (layout := readoutLayout)
    false BaseTy.bool initialBinding []

private def payoffExpr : Vegas.EventGraph.PublicExpr (Player := Bool) (L := simpleExpr)
    readoutLayout .int where
  schema := [(10, .int), (11, .result .bool)]
  code := .ite
    (.isSuccess (.var 11 (.there .here)))
    (.addInt (.var 10 .here) (.constInt 10))
    (.constInt 0)
  reads := fun ref => match ref with
    | .here => .publicData ⟨.inr 0, rfl⟩
    | .there .here => .publication ⟨.inr 1, rfl⟩
  readFields := {.inr 0, .inr 1}
  reads_mem := by
    intro name input ref member
    cases ref with
    | here =>
        change (.inr 0 : Vegas.EventGraph.FieldId 1 2) ∈ {Sum.inr 0, Sum.inr 1}
        simp
    | there ref =>
        cases ref with
        | here =>
            change (.inr 1 : Vegas.EventGraph.FieldId 1 2) ∈ {Sum.inr 0, Sum.inr 1}
            simp
        | there ref => nomatch ref

private abbrev readoutGraph : Vegas.EventGraph Bool simpleExpr where
  inputCount := 1
  order := readoutOrder
  inputLayout := readoutInputs
  outputLayout := readoutOutputs
  nodes := Fin.cases chanceCode fun tail =>
    Fin.cases resolveCode (fun impossible => Fin.elim0 impossible) tail
  reads_available := by
    intro event field member
    fin_cases event
    · change field ∈ chanceCode.readFields at member
      simp [chanceCode, Vegas.EventGraph.EventCode.readFields] at member
    · change field ∈ resolveCode.readFields at member
      cases field with
      | inl input => trivial
      | inr producer =>
          change Sum.inr producer ∈ ({Sum.inl 0} : Finset (Vegas.EventGraph.FieldId 1 2))
            at member
          simp at member
  payoffs := [(false, payoffExpr)]

private def inputValues : readoutGraph.Inputs :=
  fun _ => PublicationResult.success true

private def sampleValue : (readoutGraph.outputLayout 0).Value := by
  rw [show readoutGraph.outputLayout 0 = .publicData BaseTy.int from rfl]
  exact 2

private def graphPayoff :
    Vegas.EventGraph.PublicExpr readoutGraph.layout BaseTy.int := by
  change Vegas.EventGraph.PublicExpr readoutLayout BaseTy.int
  exact payoffExpr

private def initial : readoutGraph.Config := .initial inputValues

private theorem initial_ready (event : readoutGraph.EventId) :
    initial.cut.Ready event := by
  simp [initial, Vegas.EventGraph.Config.initial, EventOrder.Cut.Ready,
    EventOrder.Cut.empty, readoutGraph, readoutOrder]

example : readoutGraph.inputLayout 0 = .binding false .bool := rfl

example : readoutGraph.outputLayout 0 = .publicData .int := rfl

example : readoutGraph.outputLayout 1 = .publication .bool := rfl

/-- The backend retains the exact nontrivial rational table before denotation. -/
example :
    (match readoutGraph.nodes 0 with
      | .sample _ law => law.evalLaw? initial.store
      | _ => none) = some fairInt := rfl

example :
    (readoutGraph.nodes 0).eval? PUnit.unit initial.store =
      some fairInt.denote := rfl

/-- Resolving the original private input binding stores its successful value. -/
example :
    (readoutGraph.nodes 1).eval? true initial.store =
      some (FinDist.pure (.success true)) := rfl

private def sampled : readoutGraph.Config :=
  initial.complete 0 (initial_ready 0) PUnit.unit sampleValue

private theorem sampled_ready_resolve : sampled.cut.Ready 1 :=
  (initial_ready 1).after_complete (initial_ready 0) (by decide)

private def terminal : readoutGraph.Config :=
  sampled.complete 1 sampled_ready_resolve true (.success true)

private theorem terminal_is_terminal : terminal.cut.Terminal := by
  unfold EventOrder.Cut.Terminal
  change (insert (1 : Fin 2) (insert (0 : Fin 2) ∅) : Finset (Fin 2)) = Finset.univ
  decide

example : terminal.outcome terminal_is_terminal (.inl 0) = .success true := rfl

example : terminal.outcome terminal_is_terminal (.inr 0) = sampleValue := rfl

example : terminal.outcome terminal_is_terminal (.inr 1) = .success true := rfl

/-- Terminal payoff evaluation reads both heterogeneous public outputs. -/
example : terminal.terminalPayoffs terminal_is_terminal =
    [(false, 12)] := by
  rfl

/-- The local commutation theorem transports through the retained payoff
expression: sampling first or resolving first yields the same readout law. -/
example :
    (readoutGraph.stepThen initial 0 1 (initial_ready 0) (initial_ready 1)
      (by decide) PUnit.unit true).map
        (fun config => graphPayoff.eval? config.store) =
    (readoutGraph.stepThen initial 1 0 (initial_ready 1) (initial_ready 0)
      (by decide) true PUnit.unit).map
        (fun config => graphPayoff.eval? config.store) := by
  have stores := Vegas.EventGraph.stepThen_map_store_comm initial 0 1
    (initial_ready 0) (initial_ready 1) (by decide) PUnit.unit true
  have readouts := congrArg
    (FinDist.map fun store => graphPayoff.eval? store) stores
  simpa only [FinDist.map_comp, Function.comp_def] using readouts

end

end VegasTests.EventGraphReadout
