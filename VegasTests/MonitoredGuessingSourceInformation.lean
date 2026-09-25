/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingSourceKernel

/-! # The receiver's fair prior and the sender's observed final decision -/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open GameTheory.Protocol.ExecutionProtocol

theorem drawn_bob_view (bit other : Bool) :
    (startConfig bit).view bob = (startConfig other).view bob := by
  apply Prod.ext
  · apply sourceObserve_congr
    · intro name ty ref
      cases ref with | there ref => cases ref with | there ref => cases ref
    · intro name ty ref
      cases ref with | there ref => cases ref with | there ref => cases ref
    · intro name ty ref
      cases ref with | there ref => cases ref with | there ref => cases ref
    · intro name ty ref
      cases ref with
      | there ref => cases ref with
        | here => rfl
        | there ref => cases ref
  · rfl

theorem drawn_bob_info (bit other : Bool) :
    sourceModel.infoOf bob (SourcePath.drawn bit).history.trace =
      sourceModel.infoOf bob (SourcePath.drawn other).history.trace := by
  rw [source_info, source_info]
  exact congrArg (fun view => (some (.inl view) : sourceModel.InfoState bob))
    (drawn_bob_view bit other)

def sourceBobSite : sourceModel.InformationSite bob :=
  sourceModel.informationSite bob (SourcePath.drawn false).history
    (.reveal bob 1 false) id (by rw [source_info]; exact ⟨rfl, false, rfl⟩)

def sourceAliceSite (bit guess : Bool) : sourceModel.InformationSite alice :=
  sourceModel.informationSite alice (SourcePath.guessed bit guess).history
    (.reveal alice 0 false) id (by rw [source_info]; exact ⟨rfl, false, rfl⟩)

theorem source_bob_history (site : sourceModel.InformationSite bob)
    (history : sourceModel.InformationHistory bob site.1) :
    ∃ bit, history.1 = (SourcePath.drawn bit).history := by
  have active := InformationModel.InformationSite.active sourceModel site history
  obtain ⟨path, same⟩ := source_history_complete history.1.trace
  change history.1 = path.history at same
  rw [same] at active
  cases path with
  | drawn bit => exact ⟨bit, same⟩
  | _ => cases active

theorem source_bob_site (site : sourceModel.InformationSite bob) : site = sourceBobSite := by
  obtain ⟨history, _, _, _⟩ := site.2
  obtain ⟨bit, same⟩ := source_bob_history site history
  apply Subtype.ext
  exact history.2.symm.trans ((congrArg (fun h => sourceModel.infoOf bob h.trace) same).trans
    (drawn_bob_info bit false))

theorem source_alice_history (site : sourceModel.InformationSite alice)
    (history : sourceModel.InformationHistory alice site.1) :
    ∃ bit guess, history.1 = (SourcePath.guessed bit guess).history := by
  have active := InformationModel.InformationSite.active sourceModel site history
  obtain ⟨path, same⟩ := source_history_complete history.1.trace
  change history.1 = path.history at same
  rw [same] at active
  cases path with
  | guessed bit guess => exact ⟨bit, guess, same⟩
  | _ => cases active

theorem source_alice_site (site : sourceModel.InformationSite alice) :
    ∃ bit guess, site = sourceAliceSite bit guess := by
  obtain ⟨history, _, _, _⟩ := site.2
  obtain ⟨bit, guess, same⟩ := source_alice_history site history
  exact ⟨bit, guess, Subtype.ext
    (history.2.symm.trans (congrArg (fun h => sourceModel.infoOf alice h.trace) same))⟩

theorem source_no_watcher_site (site : sourceModel.InformationSite watcher) : False := by
  obtain ⟨history, _, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active sourceModel site history
  obtain ⟨path, same⟩ := source_history_complete history.1.trace
  change history.1 = path.history at same
  rw [same] at active
  cases path <;> cases active

def sourceAliceObservations : sourceModel.InfoState alice → Bool × Bool
  | some (.inr (.inl view)) =>
      (((view.1.cells _ _ (.there .here)).getD .failure).getD false,
        (view.1.cells _ _ .here).isSuccess)
  | _ => (false, false)

theorem source_alice_observations (bit guess : Bool) :
    sourceAliceObservations
      (sourceModel.infoOf alice (SourcePath.guessed bit guess).history.trace) =
      (bit, guess) := by
  rw [source_info]
  cases guess <;> rfl

theorem source_alice_history_unique (bit guess : Bool)
    (history : sourceModel.InformationHistory alice (sourceAliceSite bit guess).1) :
    history.1 = (SourcePath.guessed bit guess).history := by
  obtain ⟨other, decision, same⟩ := source_alice_history (sourceAliceSite bit guess) history
  have observed := congrArg sourceAliceObservations history.2
  change sourceAliceObservations (sourceModel.infoOf alice history.1.trace) =
    sourceAliceObservations
      (sourceModel.infoOf alice (SourcePath.guessed bit guess).history.trace) at observed
  rw [same, source_alice_observations, source_alice_observations] at observed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj observed
  exact same

def sourceBobHistory (bit : Bool) : sourceModel.InformationHistory bob sourceBobSite.1 :=
  ⟨(SourcePath.drawn bit).history, drawn_bob_info bit false⟩

theorem sourceBobHistory_injective : Function.Injective sourceBobHistory := by
  intro bit other same
  have stateSame := congrArg (fun history => decodeSource history.1.state) same
  change SourcePath.drawn bit = SourcePath.drawn other at stateSame
  exact SourcePath.drawn.inj stateSame

def sourceBobHistories : Bool ≃ sourceModel.InformationHistory bob sourceBobSite.1 :=
  Equiv.ofBijective sourceBobHistory ⟨sourceBobHistory_injective, fun history => by
    obtain ⟨bit, same⟩ := source_bob_history sourceBobSite history
    exact ⟨bit, Subtype.ext same.symm⟩⟩

theorem source_reach_bob (profile : Profile sourceModel.behavioralSignature) (bit : Bool) :
    sourceModel.historyReachProbability profile (SourcePath.drawn bit).history = 1 / 2 := by
  classical
  unfold InformationModel.historyReachProbability
  rw [show (SourcePath.drawn bit).history.trace.length = 1 by
    simp [SourcePath.history, SourcePath.trace, Trace.length]]
  rw [← FinDist.prob_map_of_injective History.state source_state_injective]
  change ((sourceModel.runBehavioralFrom profile 1 sourceArena.initHistory).map
    History.state).prob _ = _
  rw [source_run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, FinDist.pure_bind,
    initHistory, sourceKernel]
  change (((FinDist.uniformOfFintype (α := Bool)).map initialState).map
    (fun state => (some (.inl (sourceSetup.initialConfig state)) : sourceArena.State))).prob _ = _
  rw [FinDist.map_comp]
  change ((FinDist.uniformOfFintype (α := Bool)).map
    (fun bit => (SourcePath.drawn bit).state)).prob (SourcePath.drawn bit).state = _
  have injective : Function.Injective (fun bit => (SourcePath.drawn bit).state) := by
    intro first second same
    have decoded := congrArg decodeSource same
    exact SourcePath.drawn.inj decoded
  rw [FinDist.prob_map_of_injective _ injective, FinDist.prob_uniformOfFintype]
  norm_num

theorem source_mass_bob (profile : Profile sourceModel.behavioralSignature) :
    sourceModel.informationMass profile bob sourceBobSite = 1 := by
  unfold InformationModel.informationMass
  rw [← sourceBobHistories.sum_comp]
  change (∑ bit : Bool, sourceModel.historyReachProbability profile
    (SourcePath.drawn bit).history) = _
  simp only [source_reach_bob, Fintype.sum_bool]
  norm_num

theorem source_consistent_bob (assessment : sourceModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent sourceAntichain) :
    assessment.belief bob sourceBobSite =
      (FinDist.uniformOfFintype (α := Bool)).map sourceBobHistory := by
  classical
  obtain ⟨sequence, approximates, converges⟩ := consistent
  apply FinDist.ext_of_prob
  intro history
  obtain ⟨bit, rfl⟩ := sourceBobHistories.surjective history
  change (assessment.belief bob sourceBobSite).prob (sourceBobHistory bit) =
    ((FinDist.uniformOfFintype (α := Bool)).map sourceBobHistory).prob (sourceBobHistory bit)
  have each (n : Nat) :
      ((sequence n).belief bob sourceBobSite).prob (sourceBobHistory bit) = 1 / 2 := by
    rw [(approximates n).2 bob sourceBobSite (by rw [source_mass_bob]; norm_num)]
    change sourceModel.historyReachProbability (sequence n).strategy
      (SourcePath.drawn bit).history / sourceModel.informationMass
        (sequence n).strategy bob sourceBobSite = _
    rw [source_reach_bob, source_mass_bob, div_one]
  rw [FinDist.prob_map_of_injective _ sourceBobHistory_injective,
    FinDist.prob_uniformOfFintype, Fintype.card_bool]
  have limit := converges.2 bob sourceBobSite (sourceBobHistory bit)
  simp_rw [each] at limit
  convert tendsto_nhds_unique limit tendsto_const_nhds using 1
  norm_num

end VegasTests.MonitoredGuessing
