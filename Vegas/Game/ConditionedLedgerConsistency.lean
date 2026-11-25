module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedLedgerFiber
public import Vegas.Game.ConditionedLedgerReach

@[expose] public section

/-! # Kreps–Wilson consistency for locally selected ledger assessments -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol EventGraphRuntime
open GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {Signal : Type*}
  {signal : State L setup.context → Signal}
  {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
  {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}
  (menu : (application setup timeouts leaks).ResponseMenu)
  (allSupported : ∀ key, key ∈ (setup.initialDistribution.map signal).support)
  (read : Player → (application setup timeouts leaks).Info → Signal)
  (observed : ∀ draw ∈ setup.initialDistribution.support,
    ∀ execution : (application setup timeouts leaks).Execution,
    State.Invariant (graph := setup.informationGraph) (setup.eventInputs draw)
      execution.application → ∀ who,
      read who (some (execution.logs who,
        execution.observe (application setup timeouts leaks) who)) = signal draw)

local notation "law" k => Vegas.initialDistribution (setup.conditionInitial signal k)
local notation "globalModel" => menu.information (Vegas.initialDistribution setup) horizon scheduler
local notation "C" k => menu.information (law k) horizon scheduler
local notation "A" => ledger_componentAssessment menu allSupported read observed
local notation "cs" => ledger_componentSite menu allSupported read observed

private theorem ledger_componentAssessment_bayes
    (components : ∀ key, (C key).BehavioralAssessment)
    (bayes : ∀ key, InformationModel.BehavioralAssessment.IsBayesConsistent (C key)
      (components key) (menu.decisionInformationAntichain (law key) horizon scheduler)) :
    InformationModel.BehavioralAssessment.IsBayesConsistent (globalModel) (A components)
      (menu.decisionInformationAntichain (Vegas.initialDistribution setup) horizon scheduler) := by
  classical
  intro who site positive
  let key := read who site.1
  let localSite := cs who site
  let e := Equiv.ofBijective
    (menu.infoHistoryOfInitialSupportSubset (scheduler := scheduler) (horizon := horizon)
      (setup.conditionInitial_ledgerSupport signal key (allSupported key)) who site.1)
    ⟨menu.infoHistoryOfInitialSupportSubset_injective _ who site.1,
      ledgerInfoHistory_component_surjective menu allSupported read observed who site⟩
  have reach (h : (C key).InformationHistory who site.1) :
      (globalModel).historyReachWeight (A components).strategy (e h).1 =
        (setup.initialDistribution.map signal) key * (C key).historyReachWeight
          (components key).strategy h.1 := by
    obtain ⟨⟨state, trace⟩, view⟩ := h
    cases state with
    | none =>
      have active := InformationModel.InformationSite.active (M := C key) localSite
        ⟨⟨none, trace⟩, view⟩
      cases active
    | some control =>
      exact ledger_component_historyReachWeight menu read observed (allSupported key)
        (fun k => (components k).strategy) trace
  have mass : (globalModel).informationMass (A components).strategy who site =
      (setup.initialDistribution.map signal) key *
        (C key).informationMass (components key).strategy who localSite := by
    unfold InformationModel.informationMass
    rw [← e.tsum_eq, ← ENNReal.tsum_mul_left]
    apply tsum_congr reach
  have localPositive : 0 < (C key).informationMass (components key).strategy who localSite := by
    apply pos_iff_ne_zero.mpr
    intro zero
    exact positive.ne' (mass.trans (by rw [zero, mul_zero]))
  intro h
  obtain ⟨t, rfl⟩ := e.surjective h
  change ((components key).belief who localSite).map e (e t) = _
  refine (pmf_map_apply_of_injective _ e.injective t).trans ?_
  refine (bayes key who localSite localPositive t).trans ?_
  exact (ENNReal.mul_div_mul_left _ _ ((PMF.mem_support_iff _ _).mp (allSupported key))
    (PMF.apply_ne_top _ _)).symm.trans (congrArg₂ (· / ·) (reach t).symm mass.symm)

/-- If each observed component has a consistent raw assessment, one sequence of
fully mixed Bayes assessments converges to their locally selected raw assessment. -/
theorem ledger_componentAssessment_consistent
    (components : ∀ key, (C key).BehavioralAssessment)
    (consistent : ∀ key, (components key).IsSequentiallyConsistent
      (menu.decisionInformationAntichain (law key) horizon scheduler)) :
    (A components).IsSequentiallyConsistent
      (menu.decisionInformationAntichain (Vegas.initialDistribution setup) horizon scheduler) := by
  classical
  choose approximation regular converges using fun key => (consistent key).exists_sequence
  refine ⟨fun n => A (fun key => approximation key n), ?_, ?_, ?_⟩
  · intro n
    constructor
    · intro who site choice
      apply (PMF.mem_support_iff _ _).mpr
      change menu.signalStrategy read _ who site.1 choice ≠ 0
      rw [menu.signalStrategy_apply]
      exact (PMF.mem_support_iff _ _).mp ((regular (read who site.1) n).1 who
        (cs who site) _)
    · exact ledger_componentAssessment_bayes menu allSupported read observed _
        (fun key => (regular key n).2)
  · intro who site choice
    simp only [ledger_componentAssessment, ReactiveApplication.ResponseMenu.signalStrategy_apply]
    exact (converges (read who site.1)).1 who (cs who site) _
  · intro who site h
    let emb := menu.infoHistoryOfInitialSupportSubset (scheduler := scheduler)
      (horizon := horizon) (setup.conditionInitial_ledgerSupport signal (read who site.1)
        (allSupported _)) who site.1
    obtain ⟨t, rfl⟩ := ledgerInfoHistory_component_surjective menu allSupported read observed
      who site h
    change Filter.Tendsto (fun n => (PMF.map emb _ (emb t))) Filter.atTop (nhds (PMF.map emb _
      (emb t)))
    have atom (p : PMF ((C (read who site.1)).InformationHistory who site.1)) :
        (p.map emb) (emb t) = p t := pmf_map_apply_of_injective p
          (menu.infoHistoryOfInitialSupportSubset_injective _ who site.1) t
    simp only [atom]
    exact (converges (read who site.1)).2 who (cs who site) t

end Vegas.SourceProgram.Setup
