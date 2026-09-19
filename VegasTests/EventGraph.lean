/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Order
import Vegas.EventGraph.Code
import Vegas.EventGraph.Semantics
import Vegas.Expr.Simple

/-! # Dependency-driven execution regressions

Two independent events precede a public barrier. Readiness permits either
completion order; the numeric event rank does not act as an execution cursor.
-/

namespace VegasTests.EventGraph

open Vegas
open GameTheory.Math.Probability

noncomputable section

private abbrev independentOrder : EventOrder where
  eventCount := 4
  predecessors event := if event = 2 then {0, 1} else if event = 3 then {2} else ∅
  predecessor_lt := by decide

private def initial : EventOrder.Cut independentOrder := .empty independentOrder

example : initial.enabled = {0, 1} := by decide

/-- The higher-ranked independent event completes first. -/
private def rightFirst : EventOrder.Cut independentOrder := initial.complete 1 (by decide)

example : 1 ∈ rightFirst.completed ∧ 0 ∉ rightFirst.completed := by decide

/-- The public barrier remains disabled while either commitment is unfinished. -/
example : ¬ rightFirst.Ready 2 := by decide

example : (rightFirst.complete 0 (by decide)).Ready 2 := by decide

/-- The two schedules reach the same cut without requiring the same trace. -/
example :
    (initial.complete 0 (by decide)).complete 1 (by decide) =
      rightFirst.complete 0 (by decide) := by
  exact EventOrder.Cut.complete_comm (by decide) (by decide) (by decide)

private abbrev BindingLayout : Fin 1 → Vegas.EventGraph.EventField Bool simpleExpr :=
  fun _ => .binding false .bool

private def bindingRef : Vegas.EventGraph.FieldRef BindingLayout (.binding false .bool) :=
  ⟨0, rfl⟩

private def openBinding : Vegas.EventGraph.EventCode BindingLayout (.publication .bool) :=
  Vegas.EventGraph.EventCode.resolve (layout := BindingLayout) false .bool bindingRef []

/-- Missing storage is distinct from a completed failed binding. -/
example : openBinding.eval? true (fun _ => none) = none := rfl

example : openBinding.eval? true (fun _ => some .failure) =
    some (FinDist.pure .failure) := rfl

example : openBinding.eval? true (fun _ => some (.success true)) =
    some (FinDist.pure (.success true)) := rfl

/-- Withholding produces failure, not an ordinary Boolean default. -/
example : openBinding.eval? false (fun _ => some (.success true)) =
    some (FinDist.pure .failure) := rfl

private def falseCheck : Vegas.EventGraph.GuardCheck BindingLayout .bool where
  subject := 7
  payload := .bool
  code := { schema := [], schemaNames := by decide, subjectFresh := by decide,
            code := .constBool false }
  subjectRead := .proposed
  reads := fun ref _ => nomatch ref
  readFields := ∅
  subject_mem := by intro field impossible; cases impossible
  reads_mem := fun ref => nomatch ref

private def guardedOpening : Vegas.EventGraph.EventCode BindingLayout (.publication .bool) :=
  Vegas.EventGraph.EventCode.resolve (layout := BindingLayout) false .bool bindingRef [falseCheck]

/-- An unsatisfiable guard is retained; its valid opening resolves to failure. -/
example : guardedOpening.eval? true (fun _ => some (.success true)) =
    some (FinDist.pure .failure) := rfl

/-- Failure vacuously satisfies the same retained check. -/
example : falseCheck.eval? (fun _ => none) .failure = some true := rfl

private def rangeBinding :
    Vegas.EventGraph.EventCode BindingLayout (.binding false (.range 1 0)) :=
  Vegas.EventGraph.EventCode.bind (layout := BindingLayout) false (.range 1 0)

/-- A native candidate that will never open binds to failure. No source policy
produces one, and the graph still has to represent it. -/
example : rangeBinding.eval? .failure (fun _ => none) =
    some (FinDist.pure .failure) := rfl

private abbrev DeferredLayout : Fin 2 → Vegas.EventGraph.EventField Bool simpleExpr :=
  Fin.cases (.binding false .bool) (fun _ => .publication .bool)

/-- A schema input the code never reads needs no operand and no stored field. -/
private def unreadInput : Vegas.EventGraph.GuardCheck DeferredLayout .bool where
  subject := 2
  payload := .bool
  code := { schema := [(1, .bool)], schemaNames := by decide, subjectFresh := by decide,
            code := .constBool true }
  subjectRead := .proposed
  reads := fun ref unread => by
    cases ref with
    | here => exact absurd unread (by decide)
    | there ref => nomatch ref
  readFields := ∅
  subject_mem := by intro field impossible; cases impossible
  reads_mem := by
    intro name input ref read field impossible
    cases ref with
    | here => exact absurd read (by decide)
    | there ref => nomatch ref

example : unreadInput.eval? (fun _ => none) (.success true) = some true := rfl

/-- The relation y = x is checked when x is proposed after y is public. -/
private def closingEquality : Vegas.EventGraph.GuardCheck DeferredLayout .bool where
  subject := 2
  payload := .bool
  code := { schema := [(1, .bool)], schemaNames := by decide, subjectFresh := by decide,
            code := .eq (.var 2 .here) (.var 1 (.there .here)) }
  subjectRead := .publication ⟨1, rfl⟩
  reads := fun ref _ => match ref with | .here => .proposed
  readFields := {1}
  subject_mem := by
    intro field same
    simpa [Vegas.EventGraph.GuardOperand.field?] using same.symm
  reads_mem := by
    intro name input ref read field impossible
    cases ref with
    | here => cases impossible
    | there ref => nomatch ref

private def publishedTrue : Vegas.EventGraph.Store DeferredLayout :=
  Fin.cases (some (.success false)) (fun _ => some (.success true))

example : closingEquality.eval? publishedTrue (.success false) = some false := rfl

example : closingEquality.eval? publishedTrue (.success true) = some true := rfl

private def closeRelation : Vegas.EventGraph.EventCode DeferredLayout (.publication .bool) :=
  Vegas.EventGraph.EventCode.resolve (layout := DeferredLayout) false .bool ⟨0, rfl⟩
    [closingEquality]

/-- The current conflicting publication fails; the already published y is retained. -/
example : closeRelation.eval? true publishedTrue = some (FinDist.pure .failure) := rfl

example : publishedTrue 1 = some (.success true) := rfl

private abbrev pairOrder : EventOrder where
  eventCount := 2
  predecessors _ := ∅
  predecessor_lt := by simp

private abbrev pairInputs : Fin 0 → Vegas.EventGraph.EventField Bool simpleExpr := Fin.elim0

private abbrev pairOutputs : Fin 2 → Vegas.EventGraph.EventField Bool simpleExpr :=
  fun event => .binding (event.val == 1) .bool

private abbrev pairLayout := Vegas.EventGraph.fieldLayout pairInputs pairOutputs

/-- A hand-built graph with one independent binding per player. -/
private abbrev pairGraph : Vegas.EventGraph Bool simpleExpr where
  inputCount := 0
  order := pairOrder
  inputLayout := pairInputs
  outputLayout := pairOutputs
  nodes event := Vegas.EventGraph.EventCode.bind (layout := pairLayout)
    (event.val == 1) .bool
  reads_available := by
    intro event field member
    exact False.elim (Finset.notMem_empty field member)
  payoffs := []

private def pairSchema : pairGraph.LogicalSchema where
  fields := fun _ => ∅
  ownHistory := fun _ => []

/-- The two bindings are information-independent: when either is ready, no
public or same-owner result/action has completed. -/
private theorem pairInformation : pairGraph.InformationDiscipline pairSchema where
  fields_visible := by simp [pairSchema]
  fields_causal := by simp [pairSchema]
  ready_fields_exact := by
    intro cut event who ready actor
    change pairGraph.visibleFields who cut = ∅
    rw [Finset.eq_empty_iff_forall_notMem]
    intro field member
    have facts := Finset.mem_filter.mp member
    rcases facts with ⟨_, available, visible⟩
    cases field with
    | inl input => exact Fin.elim0 input
    | inr producer =>
        fin_cases event <;> fin_cases producer <;>
          simp [Vegas.EventGraph.actor?, Vegas.EventGraph.EventCode.actor,
            Vegas.EventGraph.layout, Vegas.EventGraph.fieldLayout,
            pairGraph, pairLayout, pairInputs, pairOutputs,
            Vegas.EventGraph.fieldVisibleTo, Vegas.EventGraph.EventField.VisibleTo,
            Vegas.EventGraph.FieldAvailable, EventOrder.Cut.Ready]
            at actor available visible ready <;>
          aesop
  own_history_ranked := by simp [pairSchema]
  own_history_owned := by simp [pairSchema]
  own_history_causal := by simp [pairSchema]
  ready_own_history_exact := by
    intro cut event who ready actor
    change (∅ : Finset pairGraph.EventId) = pairGraph.completedOwnEvents who cut
    symm
    rw [Finset.eq_empty_iff_forall_notMem]
    intro prior member
    have facts := Finset.mem_filter.mp member
    rcases facts with ⟨completed, owned⟩
    fin_cases event <;> fin_cases prior <;>
      simp_all [Vegas.EventGraph.actor?, Vegas.EventGraph.EventCode.actor,
        pairGraph, pairLayout, EventOrder.Cut.Ready]
  same_owner_ordered := by
    intro earlier later who earlierBefore earlierOwner laterOwner
    fin_cases earlier <;> fin_cases later <;>
      simp_all [Vegas.EventGraph.actor?, Vegas.EventGraph.EventCode.actor]

private def pairInputValues : pairGraph.Inputs := fun input => nomatch input

private def pairInitial : pairGraph.Config := .initial pairInputValues

private theorem pairInitial_ready (event : pairGraph.EventId) :
    pairInitial.cut.Ready event := by
  simp [pairInitial, Vegas.EventGraph.Config.initial, EventOrder.Cut.Ready,
    EventOrder.Cut.empty, pairGraph, pairOrder]

private def secondAccepted : pairGraph.Config :=
  pairInitial.complete (1 : Fin 2) (pairInitial_ready 1) (.success true) (.success true)

private theorem secondAccepted_ready0 : secondAccepted.cut.Ready (0 : Fin 2) := by
  exact (pairInitial_ready 0).after_complete (pairInitial_ready 1) (by decide)

/-- This is an actual binding transition, not just a reordered submission. -/
example : pairInitial.step (1 : Fin 2) (pairInitial_ready 1) (.success true) =
    FinDist.pure secondAccepted := by
  simp [Vegas.EventGraph.Config.step, Vegas.EventGraph.EventCode.eval?, secondAccepted]

example : secondAccepted.outputs 1 = some (.success true) ∧
    secondAccepted.outputs 0 = none := by
  constructor
  · simp [secondAccepted]
  · rw [secondAccepted, pairInitial.complete_output_of_ne]
    · rfl
    · decide

/-- Completion order remains visible even though the other player's value is hidden. -/
example : (pairGraph.publicObserve secondAccepted).completionOrder = [1] := by
  simp [secondAccepted, pairInitial, Vegas.EventGraph.Config.initial]

example : (pairGraph.playerObserve false secondAccepted).store (.inr 1) = none := rfl

example : (pairGraph.playerObserve true secondAccepted).store (.inr 1) =
    some (.success true) := rfl

example : (pairGraph.publicObserve secondAccepted).store (.inr 1) = none := rfl

/-- The certified logical projection drops scheduling metadata, but no value
or original own action available to the next actor. -/
example :
    (pairGraph.logicalObserve pairSchema 0 false
      (pairGraph.playerObserve false secondAccepted)).store =
      (pairGraph.playerObserve false secondAccepted).store :=
  pairInformation.logicalObserve_store secondAccepted 0 false secondAccepted_ready0 rfl

example :
    (pairGraph.logicalObserve pairSchema 0 false
      (pairGraph.playerObserve false secondAccepted)).ownActions =
      (pairGraph.playerObserve false secondAccepted).ownActions :=
  pairInformation.logicalObserve_ownActions secondAccepted 0 false secondAccepted_ready0 rfl

private def firstAccepted : pairGraph.Config :=
  pairInitial.complete (0 : Fin 2) (pairInitial_ready 0) (.success false) (.success false)

private theorem firstAccepted_ready1 : firstAccepted.cut.Ready (1 : Fin 2) := by
  exact (pairInitial_ready 1).after_complete (pairInitial_ready 0) (by decide)

private def canonicalResult : pairGraph.Config :=
  firstAccepted.complete (1 : Fin 2) firstAccepted_ready1 (.success true) (.success true)

private def reverseResult : pairGraph.Config :=
  secondAccepted.complete (0 : Fin 2) secondAccepted_ready0 (.success false) (.success false)

/-- Each player supplies its own Boolean bit at its binding event. -/
private def pairProfile : pairGraph.BehavioralProfile :=
  fun who _event _owner _observation => FinDist.pure (.success who)

private theorem pairInitial_notTerminal : ¬ pairInitial.cut.Terminal := by
  intro terminal
  rw [EventOrder.Cut.Terminal] at terminal
  have zeroCompleted := congrArg (fun completed => (0 : Fin 2) ∈ completed) terminal
  simp [pairInitial, Vegas.EventGraph.Config.initial,
    EventOrder.Cut.empty] at zeroCompleted

/-- The canonical and greatest public schedulers induce distinct first policy
steps on the same genuinely concurrent configuration. -/
example :
    (pairGraph.policyPlan pairProfile pairGraph.canonicalScheduler pairInitial
      pairInitial_notTerminal).map (fun choice => choice.1.1) = FinDist.pure 0 := by
  have minUniv (nonempty : (Finset.univ : Finset (Fin 2)).Nonempty) :
      (Finset.univ : Finset (Fin 2)).min' nonempty = 0 := by
    refine (Finset.min'_eq_iff _ _ _).2 ⟨by simp, ?_⟩
    intro event _
    omega
  simp [Vegas.EventGraph.policyPlan, Vegas.EventGraph.canonicalScheduler, pairProfile,
    Vegas.EventGraph.actor?, Vegas.EventGraph.EventCode.actor,
    pairInitial, Vegas.EventGraph.Config.initial, pairGraph, pairOrder,
    EventOrder.Cut.enabled, EventOrder.Cut.empty, EventOrder.Cut.Ready, minUniv]

example :
    (pairGraph.policyPlan pairProfile pairGraph.greatestScheduler pairInitial
      pairInitial_notTerminal).map (fun choice => choice.1.1) = FinDist.pure 1 := by
  have maxUniv (nonempty : (Finset.univ : Finset (Fin 2)).Nonempty) :
      (Finset.univ : Finset (Fin 2)).max' nonempty = 1 := by
    refine (Finset.max'_eq_iff _ _ _).2 ⟨by simp, ?_⟩
    intro event _
    omega
  simp [Vegas.EventGraph.policyPlan, Vegas.EventGraph.greatestScheduler, pairProfile,
    Vegas.EventGraph.actor?, Vegas.EventGraph.EventCode.actor,
    pairInitial, Vegas.EventGraph.Config.initial, pairGraph, pairOrder,
    EventOrder.Cut.enabled, EventOrder.Cut.empty, EventOrder.Cut.Ready, maxUniv]

/-- Both schedule traces consist of supported semantic binding transitions. -/
example : pairInitial.step (0 : Fin 2) (pairInitial_ready 0) (.success false) =
    FinDist.pure firstAccepted := by
  simp [Vegas.EventGraph.Config.step, Vegas.EventGraph.EventCode.eval?, firstAccepted]

example : firstAccepted.step (1 : Fin 2) firstAccepted_ready1 (.success true) =
    FinDist.pure canonicalResult := by
  simp [Vegas.EventGraph.Config.step, Vegas.EventGraph.EventCode.eval?, canonicalResult]

example : secondAccepted.step (0 : Fin 2) secondAccepted_ready0 (.success false) =
    FinDist.pure reverseResult := by
  simp [Vegas.EventGraph.Config.step, Vegas.EventGraph.EventCode.eval?, reverseResult]

/-- The semantic outputs do not depend on which independent binding ran first. -/
example (event : pairGraph.EventId) :
    canonicalResult.outputs event = reverseResult.outputs event := by
  fin_cases event <;>
    simp [canonicalResult, reverseResult, firstAccepted, secondAccepted,
      Vegas.EventGraph.Config.complete, Function.update]

/-- Scheduling metadata exposes both genuine chronological orders. -/
example : (pairGraph.publicObserve canonicalResult).completionOrder = [0, 1] := by
  simp [canonicalResult, firstAccepted, pairInitial, Vegas.EventGraph.Config.initial]

example : (pairGraph.publicObserve reverseResult).completionOrder = [1, 0] := by
  simp [reverseResult, secondAccepted, pairInitial, Vegas.EventGraph.Config.initial]

/-- Neither final public observation exposes the two private binding values. -/
example (event : pairGraph.EventId) :
    (pairGraph.publicObserve canonicalResult).store (.inr event) = none := by
  fin_cases event <;> rfl

example (event : pairGraph.EventId) :
    (pairGraph.publicObserve reverseResult).store (.inr event) = none := by
  fin_cases event <;> rfl

end

end VegasTests.EventGraph
