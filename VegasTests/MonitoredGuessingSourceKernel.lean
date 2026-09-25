/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingSource

/-! # Behavioral kernels and source policies of the guessing game -/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def sourceChoice (profile : Profile sourceModel.behavioralSignature) (who : Player)
    (info : sourceModel.InfoState who) : FinDist (Option (sourceArena.Action who)) :=
  (profile who info).map Subtype.val

def sourceKernel (profile : Profile sourceModel.behavioralSignature) :
    sourceArena.State → FinDist sourceArena.State
  | none => sourceSetup.initialLaw.map (fun state => some (.inl (sourceSetup.initialConfig state)))
  | some (.inl config) =>
      (sourceChoice profile bob (some (.inl (config.view bob)))).map fun choice =>
        some (.inr (.inl (revealSuccessor 2 (.there .here) config
          (OwnAction.disclosure choice))))
  | some (.inr (.inl config)) =>
      (sourceChoice profile alice (some (.inr (.inl (config.view alice))))).map fun choice =>
        some (.inr (.inr (revealSuccessor 3 (.there .here) config
          (OwnAction.disclosure choice))))
  | some (.inr (.inr config)) => FinDist.pure (some (.inr (.inr config)))

theorem source_chooser_kernel (profile : Profile sourceModel.behavioralSignature)
    (history : sourceArena.History) (running : ¬ sourceArena.terminal history.state) :
    (sourceModel.singleMoverChooser sourceSingle
      profile history running).bind (sourceArena.step history.state) =
        sourceKernel profile history.state := by
  have marginal (who : Player) := sourceModel.singleMoverJoint_marginal
    sourceSingle profile history running who
  have marginalState (who : Player) :
      (sourceModel.singleMoverJoint sourceSingle profile history running).map
        (fun joint => joint.1 who) =
      (profile who (sourceSetup.protocolObserve who history.state)).map Subtype.val := by
    rw [marginal, source_info]
  have project (who : Player) (f : Option (sourceArena.Action who) → sourceArena.State) :
      (sourceModel.singleMoverChooser sourceSingle profile history running).map
        (fun joint => f (joint.1 who)) =
      (sourceChoice profile who (sourceSetup.protocolObserve who history.state)).map f := by
    exact (FinDist.map_comp f (fun joint => joint.1 who)
      (sourceModel.singleMoverJoint sourceSingle profile history running)).symm.trans
        (congrArg (FinDist.map f) (marginalState who))
  rcases history with ⟨state, trace⟩
  rcases state with _ | state
  · change (sourceModel.singleMoverChooser sourceSingle profile _ running).bind
      (fun _ => sourceKernel profile none) = sourceKernel profile none
    exact FinDist.bind_const _ _
  rcases state with config | config | config
  all_goals try exact (running trivial).elim
  all_goals
    conv_lhs =>
      arg 2
      ext joint
      simp only [sourceArena, Setup.executionProtocol, Setup.protocolStep,
        sourceSetup, sourceProgram, ProtocolState.step, ProtocolState.entry,
        Sum.elim_inl, Sum.elim_inr, FinDist.map_pure]
  all_goals conv_lhs => rw [← FinDist.map_eq_bind]
  all_goals dsimp only [sourceKernel]
  · exact project bob (fun choice => some (.inr (.inl
      (revealSuccessor 2 (.there .here) config (OwnAction.disclosure choice)))))
  · exact project alice (fun choice => some (.inr (.inr
      (revealSuccessor 3 (.there .here) config (OwnAction.disclosure choice)))))

theorem source_run_states (profile : Profile sourceModel.behavioralSignature)
    (fuel : Nat) (history : sourceArena.History) :
    (sourceModel.runBehavioralFrom profile fuel history).map History.state =
      (fun law => law.bind (sourceKernel profile))^[fuel] (FinDist.pure history.state) := by
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
    sourceModel sourceSingle]
  apply runRandomizedFor_map_state
  · intro state stopped
    rcases state with _ | config | config | config
    all_goals try contradiction
    rfl
  · exact source_chooser_kernel profile

def sourcePolicy (guess opening : FinDist Bool) (who : Player) :
    BehavioralPolicy who sourceProgram :=
  (fun _ _ => guess, (fun _ _ => opening, PUnit.unit))

theorem sourcePolicy_admitted (guess opening : FinDist Bool) (who : Player) :
    (sourcePolicy guess opening who).Admitted sourceProgram sourceAdmission := trivial

def sourceProfile (guess opening : FinDist Bool) : Profile sourceModel.behavioralSignature :=
  fun who => sourceSetup.toProtocolBehavioralPolicy sourceAdmission who
    (sourcePolicy guess opening who) (sourcePolicy_admitted guess opening who)

def uniformSourceProfile : Profile sourceModel.behavioralSignature :=
  sourceProfile (FinDist.uniformOfFintype (α := Bool)) (FinDist.uniformOfFintype (α := Bool))

theorem uniformSourceProfile_full (who : Player) (info : sourceModel.InfoState who) :
    (uniformSourceProfile who info).FullSupport := by
  intro choice
  suffices choice.val ∈ ((uniformSourceProfile who info).map Subtype.val).support by
    obtain ⟨other, supported, same⟩ := FinDist.support_map .. ▸ this
    exact (Subtype.ext same) ▸ supported
  rw [uniformSourceProfile, sourceProfile, Setup.toProtocolBehavioralPolicy_map_val]
  rcases choice with ⟨action, legal⟩
  change sourceSetup.protocolMenu sourceAdmission who info action at legal
  cases info with
  | none => exact FinDist.mem_support_pure.mpr legal
  | some info =>
      rcases info with current | current | current
      all_goals fin_cases who <;> cases action
      all_goals
        have allowed := legal
        dsimp [Setup.protocolMenu, sourceSetup, sourceProgram, ProtocolView.menu,
          ProtocolView.actor, ProtocolView.available] at allowed
        simp_all [sourceSetup, sourceProgram, BehavioralPolicy.protocolAction,
          sourcePolicy, FinDist.support_map, FinDist.mem_support_uniformOfFintype,
          alice, bob, watcher, eq_comm]

theorem uniformSourceProfile_fullyMixed :
    (InformationModel.BehavioralAssessment.ofStrategy uniformSourceProfile).IsFullyMixed :=
  fun who site => uniformSourceProfile_full who site.1

def sourceDecisionLaw (profile : Profile sourceModel.behavioralSignature)
    (who : Player) (info : sourceModel.InfoState who) : FinDist Bool :=
  (sourceChoice profile who info).map OwnAction.disclosure

theorem profile_guess_law (guess opening : FinDist Bool) (bit : Bool) :
    sourceDecisionLaw (sourceProfile guess opening) bob
      (sourceModel.infoOf bob (SourcePath.drawn bit).history.trace) = guess := by
  rw [source_info]
  unfold sourceDecisionLaw sourceChoice sourceProfile
  rw [Setup.toProtocolBehavioralPolicy_map_val]
  change (guess.map (fun value => some (.reveal bob 1 value))).map OwnAction.disclosure = _
  rw [FinDist.map_comp]
  exact FinDist.map_id _

theorem profile_opening_law (guess opening : FinDist Bool) (bit decision : Bool) :
    sourceDecisionLaw (sourceProfile guess opening) alice
      (sourceModel.infoOf alice (SourcePath.guessed bit decision).history.trace) = opening := by
  rw [source_info]
  unfold sourceDecisionLaw sourceChoice sourceProfile
  rw [Setup.toProtocolBehavioralPolicy_map_val]
  change (opening.map (fun value => some (.reveal alice 0 value))).map OwnAction.disclosure = _
  rw [FinDist.map_comp]
  exact FinDist.map_id _

end VegasTests.MonitoredGuessing
