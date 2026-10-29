/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphScheduling
import Vegas.Expr.Simple

/-! # Exact chance scheduling and a visible-coin policy obstruction

Compiler-generated chance graphs retain their full source configuration law
under every public scheduler. In a graph with concurrent events, an actual
strategic callback can respond to an intervening public sample.
-/

noncomputable section

namespace VegasTests.ChanceScheduling

open Vegas EventGraph GameTheory.Math.Probability

private abbrev parallelOrder : EventOrder where
  eventCount := 2
  predecessors _ := ∅
  predecessor_lt := by simp

private def fairBool : RationalLaw Bool where
  entries := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

private def coin {Field : Type} [DecidableEq Field]
    (layout : Field → EventField Bool simpleExpr) : EventCode layout (.publicData .bool) :=
  .sample (L := simpleExpr) BaseTy.bool {
    schema := []
    code := .weighted fairBool
    reads := fun ref => nomatch ref
    readFields := ∅
    reads_mem := fun ref => nomatch ref
  }

private def chanceSource : SourceProgram Bool simpleExpr [] ∅ :=
  .sample (payload := .bool) 0 (by decide) (.weighted fairBool) <|
  .sample (payload := .bool) 1 (by decide) (.weighted fairBool) <| .ret []

private abbrev chanceGraph := toEventGraph chanceSource
private def chanceProfile : SourceProgram.BehavioralProfile chanceSource := fun _ => PUnit.unit

/-- Adaptive public scheduling preserves the complete chance configuration law. -/
example (scheduler : chanceGraph.PublicScheduler) :
    (chanceGraph.terminalOutcomes scheduler (compileEventProfile chanceSource chanceProfile)
      (encodeInputs (Env.empty (CellVal simpleExpr)))).map (terminalConfig chanceSource) =
      SourceProgram.run chanceSource chanceProfile (Env.empty (CellVal simpleExpr)) :=
  scheduled_terminalConfig_law chanceSource scheduler chanceProfile _

private abbrev mixedOutputs : Fin 2 → EventField Bool simpleExpr :=
  Fin.cases (.publicData .bool) fun _ => .binding false .bool

private abbrev mixedGraph : Vegas.EventGraph Bool simpleExpr where
  inputCount := 0
  order := parallelOrder
  inputLayout := Fin.elim0
  outputLayout := mixedOutputs
  nodes := Fin.cases (coin _) fun tail =>
    Fin.cases (.bind (L := simpleExpr) false BaseTy.bool)
      (fun impossible => Fin.elim0 impossible) tail
  reads_available := by
    intro event field member
    fin_cases event
    · change field ∈ (coin _).readFields at member
      simp [coin, EventCode.readFields] at member
    · change field ∈ (∅ : Finset _) at member
      exact False.elim (Finset.notMem_empty field member)
  payoffs := []

private abbrev mixedInitial : mixedGraph.Config := Config.initial (fun input => nomatch input)

private theorem mixedReady (event : mixedGraph.EventId) : mixedInitial.cut.Ready event := by
  simp [mixedInitial, Config.initial, EventOrder.Cut.Ready, EventOrder.Cut.empty,
    mixedGraph, parallelOrder]

private def visibleCoinPolicy : mixedGraph.BehavioralProfile := fun who event =>
  Fin.cases
    (fun actor _ _ => False.elim (by
      change (none : Option Bool) = some who at actor
      cases actor))
    (fun tail => Fin.cases
      (fun _ observation _ =>
        PMF.pure (some (.success ((observation.store (.inr 0)).getD false))))
      (fun impossible => Fin.elim0 impossible) tail) event

private abbrev sampledTrue : mixedGraph.Config :=
  mixedInitial.complete 0 (mixedReady 0) PUnit.unit true

private theorem initially_active (who : Bool) : who ∉ mixedInitial.defaulted := by
  change who ∉ (∅ : Finset Bool)
  simp

private theorem sampled_active (who : Bool) : who ∉ sampledTrue.defaulted := by
  change who ∉ (∅ : Finset Bool)
  simp

/-- The obstructing coin result has positive mass in the original evaluator. -/
private theorem trueSupported : true ∈ fairBool.denote.support := by
  rw [RationalLaw.denote, PMF.support_map]
  refine ⟨⟨1, by change (1 : Nat) < 2; decide⟩, ?_, rfl⟩
  rw [PMF.mem_support_iff, RationalLaw.indexLaw, PMF.ofFintype_apply]
  norm_num [fairBool, RationalLaw.entryMass]

private theorem sampleSupported :
    sampledTrue ∈ (mixedInitial.step 0 (mixedReady 0) PUnit.unit).support := by
  rw [mixedInitial.step_eq_map_of_eval 0 (mixedReady 0) PUnit.unit fairBool.denote
    (by rfl), PMF.support_map]
  exact ⟨true, trueSupported, rfl⟩

private theorem before_sample :
    visibleCoinPolicy false 1 rfl (mixedGraph.playerObserve false mixedInitial)
      (initially_active false) = PMF.pure (some (PublicationResult.success false)) := by rfl

private theorem after_sample :
    visibleCoinPolicy false 1 rfl (mixedGraph.playerObserve false sampledTrue)
      (sampled_active false) = PMF.pure (some (PublicationResult.success true)) := by rfl

/-- A supported public sample changes the actual active player's action law. -/
example : ∃ next ∈ (mixedInitial.step 0 (mixedReady 0) PUnit.unit).support,
    ∃ active : false ∉ next.defaulted,
      visibleCoinPolicy false 1 rfl (mixedGraph.playerObserve false next) active ≠
        visibleCoinPolicy false 1 rfl (mixedGraph.playerObserve false mixedInitial)
          (initially_active false) := by
  refine ⟨sampledTrue, sampleSupported, sampled_active false, ?_⟩
  rw [before_sample, after_sample]
  intro same
  have mass := congrArg
    (fun law : PMF (Option (PublicationResult Bool)) => law (some (.success true))) same
  simp at mass

end VegasTests.ChanceScheduling
