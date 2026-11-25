module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.IntendedAuthenticOpening
public import Vegas.Game.SourceServiceContinuation
public import Vegas.Compile.PrescribedProfile
public import Vegas.Pending.CanonicalOutcomePublication

@[expose] public section

/-! # Prescribed graph continuations at genuine intended histories

The existing source restriction and compiler continuation laws determine the
complete prescribed readout from every genuine intended history. In particular,
the canonical public-phase continuation potential has empty default set. Neither
positive reach probability nor an equilibrium hypothesis is needed.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- Decoding a genuine intended history forces the authoritative graph default
set to be empty; no native source-prefix hypothesis is inferred from a view. -/
theorem SourceResidual.clear_of_intended_history
    {profile : BehavioralProfile setup.program} {rank : Nat}
    {origin : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank origin)
    (wellFormed : setup.WellFormed) (history : setup.intendedProtocol.History)
    (state : history.state = sourceServicePrefix? setup rank origin) : origin.defaulted = ∅ := by
  let point := residual.lift (ProtocolState.entry residual.program residual.source)
  have decoded : sourceServicePrefix? setup rank origin = some point := residual.decode
  have historyState : history.state = some point := state.trans decoded
  have intended := setup.intendedState_trace wellFormed history.trace
  rw [historyState] at intended
  have defaults := decodeSourcePrefix?_defaults rank setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) origin.store
    (decodeHistory setup.program origin.history) origin.defaults point decoded
  change origin.defaults.defaulted = ∅
  rw [← defaults]
  exact Finset.eq_empty_iff_forall_notMem.mpr fun who =>
    ProtocolState.not_excluded_of_intended who setup.program point intended

/-- The canonical prescribed continuation from a genuine intended history has
the intended full source readout, including its source action and default history. -/
theorem SourceResidual.prescribed_readout_distribution_of_intended_history [Finite Player]
    (wellFormed : setup.WellFormed)
    (admission : CommitmentInterface setup.program)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel admission).behavioralSignature)
    (agrees : (setup.intendedRestriction admission).ExtendsProfile intended target)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program
      (setup.decodeBehavioralProfile admission target who))
    {rank : Nat} {origin : setup.informationGraph.Config}
    (residual : SourceResidual setup (setup.decodeBehavioralProfile admission target) rank origin)
    {inputs : setup.informationGraph.Inputs} (reachable : origin.Reachable inputs)
    (history : setup.intendedProtocol.History)
    (state : history.state = sourceServicePrefix? setup rank origin) :
    (setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan
        (compilePrescribedProfile setup.program setup.informationDependencies
          (setup.decodeBehavioralProfile admission target))
        setup.informationGraph.canonicalScheduler) origin.remaining origin).map
      (fun final => decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program)
        final.store final.history) =
      (setup.continuationDistribution (setup.intendedOpeningProfile intended) history.state).map
        some := by
  have clean := Config.NoBindingDefaults.of_clear
    (residual.clear_of_intended_history wellFormed history state)
  have repaired : setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan
        (compilePrescribedProfile setup.program setup.informationDependencies
          (setup.decodeBehavioralProfile admission target))
        setup.informationGraph.canonicalScheduler) origin.remaining origin =
      setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (compileEventProfile setup.program
          (setup.decodeBehavioralProfile admission target))
          setup.informationGraph.canonicalScheduler) origin.remaining origin :=
    runPlan_canonical_prescribed_compile_of_reachable setup.program _ submits origin.remaining
      origin reachable clean
  refine (congrArg (PMF.map _) repaired).trans ?_
  have sourceDistribution := residual.runPlan_readout_distribution
  have sourceState := congrArg
    (fun point => (setup.continuationDistribution (setup.decodeBehavioralProfile admission target)
      point).map some) state.symm
  exact sourceDistribution.trans (sourceState.trans (congrArg (PMF.map some)
    (setup.continuationDistribution_eq_of_intended_extension wellFormed admission intended target
      agrees history)))

/-- The public-phase canonical potential is derived from a genuine intended
history and the existing compiler continuation law. It is not a caller premise. -/
theorem SourceResidual.prescribed_defaultDistribution_of_intended_history [Finite Player]
    (wellFormed : setup.WellFormed)
    (admission : CommitmentInterface setup.program)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel admission).behavioralSignature)
    (agrees : (setup.intendedRestriction admission).ExtendsProfile intended target)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program
      (setup.decodeBehavioralProfile admission target who))
    {rank : Nat} {origin : setup.informationGraph.Config}
    (residual : SourceResidual setup (setup.decodeBehavioralProfile admission target) rank origin)
    {inputs : setup.informationGraph.Inputs} (reachable : origin.Reachable inputs)
    (history : setup.intendedProtocol.History)
    (state : history.state = sourceServicePrefix? setup rank origin) :
    EventGraphRuntime.outcomeDistribution
      (compilePrescribedProfile setup.program setup.informationDependencies
        (setup.decodeBehavioralProfile admission target)) EventGraph.Config.defaulted origin =
        PMF.pure ∅ := by
  let profile := compilePrescribedProfile setup.program setup.informationDependencies
    (setup.decodeBehavioralProfile admission target)
  let run := setup.informationGraph.runPlan
    (setup.informationGraph.policyPlan profile setup.informationGraph.canonicalScheduler)
      origin.remaining origin
  let read := fun final : setup.informationGraph.Config =>
    decodeConfig? setup.program setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) [] (outputEmbedding setup.program)
      final.store final.history
  have sourceDistribution := residual.prescribed_readout_distribution_of_intended_history
    wellFormed admission
    intended target agrees submits reachable history state
  change run.map read = _ at sourceDistribution
  have finalClear (final : setup.informationGraph.Config) (member : final ∈ run.support) :
      final.defaulted = ∅ := by
    have terminal := setup.informationGraph.runPlan_terminal
      (setup.informationGraph.policyPlan profile setup.informationGraph.canonicalScheduler)
      origin.remaining origin final le_rfl member
    let output := terminalConfig setup.program ⟨final, terminal⟩
    have chosen : some output ∈ ((setup.continuationDistribution
        (setup.intendedOpeningProfile intended) history.state).map some).support := by
      rw [← sourceDistribution]
      exact (PMF.mem_support_map_iff _ _ _).mpr
        ⟨final, member, decodeConfig?_terminal setup.program ⟨final, terminal⟩⟩
    obtain ⟨source, supported, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp chosen
    have sourceEq : source = output := Option.some.inj equal
    subst source
    have targetMember : output ∈ (setup.continuationDistribution
        (setup.decodeBehavioralProfile admission target) history.state).support := by
      rw [setup.continuationDistribution_eq_of_intended_extension wellFormed admission intended
        target
        agrees history]
      exact supported
    exact (setup.continuation_clean_of_intended_extension wellFormed admission intended target
      agrees history output targetMember).1
  change run.map EventGraph.Config.defaulted = PMF.pure ∅
  calc
    _ = run.map (fun _ => ∅) := map_congr_on_support run finalClear
    _ = _ := pmf_map_fun_const _ _

/-- Forgetting additional source-order prerequisites preserves the canonical
clean continuation potential at a genuine intended source prefix. -/
theorem SourceResidual.prescribed_defaultDistribution_fromSequential [Finite Player]
    (deps : setup.dataflowGraph.Dependencies)
    (wellFormed : setup.WellFormed)
    (admission : CommitmentInterface setup.program)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel admission).behavioralSignature)
    (agrees : (setup.intendedRestriction admission).ExtendsProfile intended target)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program
      (setup.decodeBehavioralProfile admission target who))
    {rank : Nat} {origin : setup.informationGraph.Config}
    (residual : SourceResidual setup (setup.decodeBehavioralProfile admission target) rank origin)
    {inputs : setup.informationGraph.Inputs} (reachable : origin.Reachable inputs)
    (history : setup.intendedProtocol.History)
    (state : history.state = sourceServicePrefix? setup rank origin) :
    EventGraphRuntime.outcomeDistribution
      (compilePrescribedProfile setup.program deps
        (setup.decodeBehavioralProfile admission target)) EventGraph.Config.defaulted
      ((setup.dataflowGraph.withDependencies deps).fromSequentialConfig origin) = PMF.pure ∅ := by
  let graph := setup.dataflowGraph.withDependencies deps
  let profile := compilePrescribedProfile setup.program deps
    (setup.decodeBehavioralProfile admission target)
  have law := residual.prescribed_defaultDistribution_of_intended_history wellFormed admission
    intended
    target agrees submits reachable history state
  have transported := congrArg (PMF.map EventGraph.Config.defaulted)
    (graph.runPlan_canonical_fromSequential profile origin.remaining origin)
  simp only [PMF.map_comp, Function.comp_def, graph.fromSequentialConfig_defaulted] at transported
  exact transported.symm.trans law


end Vegas
