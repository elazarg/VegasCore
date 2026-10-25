/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.SchedulerErasure
import Vegas.Expr.Simple

/-! # Chance-aware scheduling and visible-coin policy obstruction

Independent chance nodes have the same terminal store law under every adaptive
public scheduler. A strategic policy can still react to a ready public coin;
normalizing completion order does not erase the sampled public value.
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

private abbrev chanceGraph : Vegas.EventGraph Bool simpleExpr where
  inputCount := 0
  order := parallelOrder
  inputLayout := Fin.elim0
  outputLayout _ := .publicData .bool
  nodes _ := coin _
  reads_available := by
    intro event field member
    simp [coin, EventCode.readFields] at member
  payoffs := []

private def chanceProfile : chanceGraph.BehavioralProfile :=
  fun _ event actor _ => by
    change (none : Option Bool) = some _ at actor
    cases actor

private theorem chanceIndependent : chanceGraph.ReadyIndependent chanceProfile :=
  readyIndependent_of_ownerless chanceProfile (fun _ => rfl)

/-- Actual adaptive scheduler independence for two nondegenerate chance nodes. -/
example (scheduler : chanceGraph.PublicScheduler) :
    (chanceGraph.runPolicies scheduler (chanceGraph.normalizeProfile chanceProfile)
      (fun input => nomatch input)).map Config.store =
    (chanceGraph.runPolicies chanceGraph.canonicalScheduler
      (chanceGraph.normalizeProfile chanceProfile) (fun input => nomatch input)).map
        Config.store :=
  chanceIndependent.runPolicies_store_eq_canonical scheduler _

private abbrev chanceInitial : chanceGraph.Config := Config.initial (fun input => nomatch input)

private theorem chanceReady (event : chanceGraph.EventId) :
    chanceInitial.cut.Ready event := by
  simp [chanceInitial, Config.initial, EventOrder.Cut.Ready, EventOrder.Cut.empty,
    chanceGraph, parallelOrder]

/-- The local law retains the cut, typed store and original own-action recall. -/
example :
    (policyStepThen chanceProfile chanceInitial 0 1 (chanceReady 0) (chanceReady 1)
      (by decide)).map chanceGraph.semanticKey =
    (policyStepThen chanceProfile chanceInitial 1 0 (chanceReady 1) (chanceReady 0)
      (by decide)).map chanceGraph.semanticKey :=
  chanceIndependent.policyStepThen_map_semanticKey_comm chanceInitial 0 1
    (chanceReady 0) (chanceReady 1) (by decide)

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
    (fun actor _ => False.elim (by
      change (none : Option Bool) = some who at actor
      cases actor))
    (fun tail => Fin.cases
      (fun _ observation =>
        PMF.pure (.success ((observation.store (.inr 0)).getD false)))
      (fun impossible => Fin.elim0 impossible) tail) event

private abbrev sampledTrue : mixedGraph.Config :=
  mixedInitial.complete 0 (mixedReady 0) PUnit.unit true

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

private theorem normalized_before :
    normalizedAction visibleCoinPolicy mixedInitial 1 =
      PMF.pure (PublicationResult.success false) := by rfl

private theorem normalized_after :
    normalizedAction visibleCoinPolicy sampledTrue 1 =
      PMF.pure (PublicationResult.success true) := by rfl

/-- Even without a dependency edge, the actual normalized binding kernel sees
an intervening public sample. Action stability therefore remains necessary. -/
example : ¬ mixedGraph.ReadyIndependent visibleCoinPolicy := by
  intro independent
  have same := independent.normalizedAction_complete mixedInitial 1 0 (mixedReady 1)
    (mixedReady 0) (by decide) PUnit.unit true
  change normalizedAction visibleCoinPolicy sampledTrue 1 =
    normalizedAction visibleCoinPolicy mixedInitial 1 at same
  rw [normalized_before, normalized_after] at same
  have mass := congrArg
    (fun law : PMF (PublicationResult Bool) => law (.success true)) same
  simp at mass

/-- The observation change used by the obstruction occurs on actual support. -/
example : ∃ next ∈ (mixedInitial.step 0 (mixedReady 0) PUnit.unit).support,
    normalizedAction visibleCoinPolicy next 1 ≠
      normalizedAction visibleCoinPolicy mixedInitial 1 := by
  refine ⟨sampledTrue, sampleSupported, ?_⟩
  rw [normalized_before, normalized_after]
  intro same
  have mass := congrArg
    (fun law : PMF (PublicationResult Bool) => law (.success true)) same
  simp at mass

end VegasTests.ChanceScheduling
