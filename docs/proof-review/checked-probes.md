# Checked proof-review experiments

These are isolated review experiments, not production APIs. Run the ordinary
project build, then python scripts/check-proof-review-probes.py to replay
all seven with the central Lake options. The runner writes only temporary files.
The [main review](../proof-review.md) states the scope and interpretation.

## ProportionalBayesProbe

<!-- probe: ProportionalBayesProbe -->
```lean
import GameTheoryExtensions.Analysis.Protocol.PublicScheduling

noncomputable section

namespace ProofReview

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open scoped ENNReal

theorem proportional_scale_ne_top
    {ι : Type} [Fintype ι] {E T : ExecutionProtocol ι}
    (M : InformationModel E) (N : InformationModel T)
    (raw : (i : ι) → M.BehavioralPolicy i) (source : (i : ι) → N.BehavioralPolicy i)
    (project : E.History → T.History) [DecidableEq T.History]
    (who : ι) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
    (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
      N.infoOf who (project history).trace = sourceSite.1)
    (scale : ℝ≥0∞)
    (fiber : ∀ history : N.InformationHistory who sourceSite.1,
      scale * N.historyReachWeight source history.1 =
        ∑' original : M.InformationHistory who rawSite.1,
          if project original.1 = history.1 then M.historyReachWeight raw original.1 else 0)
    (rawAntichain : rawSite.IsHistoryAntichain)
    (sourcePositive : 0 < N.informationMass source who sourceSite) : scale ≠ ∞ := by
  have mass := M.informationMass_projection_of_proportional_reach N raw source project who
    rawSite sourceSite maps scale fiber
  have productFinite : scale * N.informationMass source who sourceSite ≠ ∞ := by
    rw [← mass]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one raw who rawSite rawAntichain)
  exact (ENNReal.lt_top_of_mul_ne_top_left productFinite sourcePositive.ne').ne

theorem bayesBelief_lift_map_without_finite
    {ι Pub Token View : Type} [Fintype ι] {E : ExecutionProtocol ι}
    (S : PublicScheduler E Pub Token View) (M : InformationModel E)
    (profile : ∀ i, M.BehavioralPolicy i)
    (full : ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
      choice ∈ (profile i site.1).support)
    (antichainM : M.DecisionInformationAntichain)
    (antichainN : (S.model M).DecisionInformationAntichain)
    (nonterminal : ∀ i (site : M.InformationSite i), site.AllNonterminal)
    (recoverable : ∀ i (site : M.InformationSite i)
      (h h' : M.InformationHistory i site.1), S.pubTrace h.1.trace = S.pubTrace h'.1.trace)
    (who : ι) (site : (S.model M).InformationSite who) :
    ((S.model M).bayesBelief (S.liftProfile M profile) who site (antichainN who site)
        ((S.model M).informationMass_pos_of_fullSupport _
          (S.liftProfile_fullSupport M profile full) who site)).map
        (S.eraseHistory M who site) =
      M.bayesBelief profile who (S.sourceSite M who site) (antichainM who _)
        (M.informationMass_pos_of_fullSupport profile full who _) := by
  classical
  obtain ⟨witness, _, _⟩ := site.2
  have scalePositive : 0 < S.fiberMass M who site (S.erase witness.1) := by
    rw [PublicScheduler.fiberMass]
    exact (S.likelihood_pos witness.1.trace).trans_le
      (ENNReal.le_tsum (f := fun x : S.fiberOver M who site (S.erase witness.1) =>
        S.likelihood x.1.1.trace) ⟨witness, rfl⟩)
  have fiber (history : M.InformationHistory who (S.sourceSite M who site).1) :
      S.fiberMass M who site (S.erase witness.1) * M.historyReachWeight profile history.1 =
        ∑' original : (S.model M).InformationHistory who site.1,
          if S.erase original.1 = history.1 then
            (S.model M).historyReachWeight (S.liftProfile M profile) original.1 else 0 := by
    have summand (x : (S.model M).InformationHistory who site.1) :
        (if S.erase x.1 = history.1 then
            (S.model M).historyReachWeight (S.liftProfile M profile) x.1 else 0) =
          M.historyReachWeight profile history.1 *
            (S.fiberOver M who site history.1).indicator (fun x => S.likelihood x.1.trace) x := by
      rw [Set.indicator_apply]
      change _ = _ * if S.erase x.1 = history.1 then S.likelihood x.1.trace else 0
      split_ifs with erased
      · rw [S.historyReachWeight_lift M profile _ x.1 rfl, erased]
      · rw [mul_zero]
    rw [tsum_congr summand, ENNReal.tsum_mul_left, ← tsum_subtype]
    change _ = M.historyReachWeight profile history.1 * S.fiberMass M who site history.1
    rw [S.fiberMass_congr M who site nonterminal recoverable history
      (S.eraseHistory M who site witness), mul_comm]
    rfl
  have finite := proportional_scale_ne_top (S.model M) M
    (S.liftProfile M profile) profile S.erase who site (S.sourceSite M who site)
    (fun x member => S.erase_mem M who site ⟨x, member⟩)
    (S.fiberMass M who site (S.erase witness.1)) fiber (antichainN who site)
    (M.informationMass_pos_of_fullSupport profile full who _)
  exact InformationModel.bayesBelief_projection_of_proportional_reach (S.model M) M
    (S.liftProfile M profile) profile S.erase who site (S.sourceSite M who site)
    (fun x member => S.erase_mem M who site ⟨x, member⟩)
    (S.fiberMass M who site (S.erase witness.1)) fiber scalePositive.ne' finite
    (antichainN who site) (antichainM who _) _

end ProofReview
```

## ExpectationContractionProbe

<!-- probe: ExpectationContractionProbe -->
```lean
import GameTheory.Math.Probability.ExpectationAlgebra

noncomputable section

namespace ProofReview

open GameTheory.Math.Probability

theorem abs_expect_le_expect_abs {Outcome : Type*} (law : PMF Outcome)
    (value : Outcome → ℝ) (integrable : PayoffIntegrable law value) :
    |expect law value| ≤ expect law (fun outcome => |value outcome|) := by
  have summable : Summable (fun outcome => ‖(law outcome).toReal * value outcome‖) := by
    simpa only [PayoffIntegrable, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg] using integrable
  simpa only [expect, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg] using norm_tsum_le_tsum_norm summable

theorem abs_expect_sub_le_expect_abs_sub {Outcome : Type*} (law : PMF Outcome)
    (first second : Outcome → ℝ)
    (firstIntegrable : PayoffIntegrable law first)
    (secondIntegrable : PayoffIntegrable law second) :
    |expect law first - expect law second| ≤
      expect law (fun outcome => |first outcome - second outcome|) := by
  rw [← expect_sub firstIntegrable secondIntegrable]
  exact abs_expect_le_expect_abs law _ (payoffIntegrable_sub firstIntegrable secondIntegrable)

end ProofReview
```

## DiscretePushforwardProbe

<!-- probe: DiscretePushforwardProbe -->
```lean
import GameTheory.Math.Probability.Measure

noncomputable section

namespace ProofReview

open GameTheory.Math.Probability MeasureTheory

theorem aemeasurable_of_pmf_pushforward
    {Source Target Value : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target] [MeasurableSingletonClass Target]
    [MeasurableSpace Value] [Nonempty Value]
    (measure : Measure Source) (law : PMF Target) (project : Source → Target)
    (measurable : Measurable project) (pushforward : measure.map project = law.toMeasure)
    (value : Target → Value) : AEMeasurable (value ∘ project) measure := by
  have full : law.toMeasure law.supportᶜ = 0 :=
    (law.toMeasure_apply_eq_zero_iff law.support_countable.measurableSet.compl).2
      (by
        apply Set.disjoint_left.mpr
        intro outcome supported outside
        exact outside supported)
  have mapped : AEMeasurable value (measure.map project) := by
    rw [pushforward]
    exact aemeasurable_of_countable_full_set law.toMeasure value law.support
      law.support_countable full
  exact mapped.comp_measurable measurable

theorem lintegral_of_pmf_pushforward
    {Source Target : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target] [MeasurableSingletonClass Target]
    (measure : Measure Source) (law : PMF Target) (project : Source → Target)
    (measurable : Measurable project) (pushforward : measure.map project = law.toMeasure)
    (value : Target → ENNReal) :
    (∫⁻ source, value (project source) ∂measure) = ∫⁻ target, value target ∂law.toMeasure := by
  have mapped : AEMeasurable value (measure.map project) := by
    rw [pushforward]
    exact aemeasurable_of_pmf_pushforward law.toMeasure law id measurable_id (by simp) value
  rw [← pushforward]
  exact (lintegral_map' mapped measurable.aemeasurable).symm

end ProofReview
```

## SupportOrderProbe

<!-- probe: SupportOrderProbe -->
```lean
import GameTheoryExtensions.Math.Probability.Expectation

noncomputable section

namespace VegasProofReview

open GameTheory.Math.Probability

/-- Cross-support utility order with slack survives two independent averages.
No carrier or support finiteness assumption is needed. -/
theorem expect_support_order_add {α β : Type*}
    (left : PMF α) (right : PMF β) (first : α → ℝ) (second : β → ℝ)
    (leftIntegrable : PayoffIntegrable left first)
    (rightIntegrable : PayoffIntegrable right second) (slack : ℝ)
    (ordered : ∀ a ∈ left.support, ∀ b ∈ right.support, second b ≤ first a + slack) :
    expect right second ≤ expect left first + slack := by
  have averaged := expect_mono (μ := left)
    (f := fun _ => expect right second) (g := fun a => first a + slack)
    (fun a supported => expect_le_const right second rightIntegrable (first a + slack)
      (ordered a supported)) (payoffIntegrable_constant left _)
    (payoffIntegrable_add leftIntegrable (payoffIntegrable_constant left slack))
  simpa only [expect_constant,
    expect_add leftIntegrable (payoffIntegrable_constant left slack)] using averaged

/-- The exact duplicated phase lemma becomes a zero-slack specialization. -/
theorem phase_support_order {α β : Type*}
    (left : PMF α) (right : PMF β) (first : α → ℝ) (second : β → ℝ)
    (leftIntegrable : PayoffIntegrable left first)
    (rightIntegrable : PayoffIntegrable right second)
    (ordered : ∀ a ∈ left.support, ∀ b ∈ right.support, second b ≤ first a) :
    expect right second ≤ expect left first := by
  simpa only [add_zero] using expect_support_order_add left right first second
    leftIntegrable rightIntegrable 0 (by simpa only [add_zero] using ordered)

end VegasProofReview
```

## ReducedEventOpponentFrame

<!-- probe: ReducedEventOpponentFrame -->
```lean
/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventInvariant
import Vegas.Pending.AcceptedEventOwnership

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Applying an accepted focal-authored packet cannot consume an event owned
by another player. This is the unchanged completion-set proof using the earlier owner. -/
theorem handle_opponent_completed_iff
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (message : Message Player (Payload graph))
    (event : graph.EventId) (owner : Player)
    (actor : graph.actor? event = some owner) (different : owner ≠ message.sender)
    (accepted : handle runtime state message = some next) :
    event ∈ next.config.cut.completed ↔ event ∈ state.config.cut.completed := by
  obtain ⟨completed, addressed, completedActor⟩ :=
    handle_event_actor runtime state next message accepted
  obtain ⟨stepped, steppedAddress, ready, action, member⟩ :=
    handle_config_mem_step runtime state next message accepted
  have same : stepped = completed := Option.some.inj (steppedAddress.symm.trans addressed)
  subst stepped
  have other : event ≠ completed := by
    intro same
    subst event
    rw [completedActor] at actor
    exact different (Option.some.inj actor.symm)
  rw [EventGraph.Config.step_cut state.config _ ready action next.config member,
    EventOrder.Cut.mem_complete]
  simp [other]

end Vegas.EventGraphRuntime
```

## RuntimeKernelProbes

<!-- probe: RuntimeKernelProbes -->
```lean
import Vegas.Pending.SuffixExclusionRecord
import Vegas.Pending.ReactiveCountAudit

noncomputable section

namespace ProofReview.Runtime

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
theorem public_record_iff_suffix_zero (state : RecoveryState graph) :
    PublicExclusionRecord state ↔ SuffixExclusionRecord 0 ∅ state := by
  classical
  constructor
  · intro valid
    refine ⟨valid.receipts, ?_, ?_⟩
    · intro event impossible
      omega
    · intro owner
      simpa only [Finset.notMem_empty, false_or, Nat.zero_le, true_and] using
        valid.excluded owner
  · intro valid
    refine ⟨valid.receipts, ?_⟩
    intro owner
    simpa only [Finset.notMem_empty, false_or, Nat.zero_le, true_and] using
      valid.excluded owner

theorem drainFuel_preserves (predicate : RecoveryState graph → Prop)
    (preserves : ∀ before after, RecoveryState.AutomaticStep before after →
      predicate before → predicate after)
    (fuel : Nat) (state : RecoveryState graph) (valid : predicate state) :
    predicate (RecoveryState.drainFuel fuel state) := by
  have closed : ∀ {before after},
      Relation.ReflTransGen RecoveryState.AutomaticStep before after →
      predicate before → predicate after := by
    intro before after path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact id
    | @head before middle moved _ ih =>
      exact fun initial => ih (preserves before middle moved initial)
  exact closed (RecoveryState.drainFuel_trace fuel state) valid

theorem earlier_inputs_congr {Principal : Type} [DecidableEq Principal]
    {app : ReactiveApplication Principal} {before after : app.Execution}
    (beforeValid : before.InputSerialsInOrder app)
    (afterValid : after.InputSerialsInOrder app)
    (prefixOf : before.network.inputs <+: after.network.inputs)
    (message : Message Principal app.Payload) (present : message ∈ before.network.inputs)
    (other : Message Principal app.Payload) :
    (other ∈ after.network.inputs ∧ other.sender = message.sender ∧
      other.id.2 < message.id.2) ↔
    (other ∈ before.network.inputs ∧ other.sender = message.sender ∧
      other.id.2 < message.id.2) := by
  constructor
  · rintro ⟨member, owner, lower⟩
    refine ⟨beforeValid.mem_of_prefix afterValid prefixOf member ?_, owner, lower⟩
    rw [owner]
    exact lower.trans (beforeValid.serial_lt present)
  · rintro ⟨member, owner, lower⟩
    exact ⟨prefixOf.subset member, owner, lower⟩

end ProofReview.Runtime
```

## ParameterProtocolProbe

<!-- probe: ParameterProtocolProbe -->
```lean
import Vegas.Game.SourceProtocolNash
import Vegas.Game.ProgramPaymentNash

noncomputable section

namespace ProofReview

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem parameter_protocol_payoff_law
    {Player : Type} [DecidableEq Player] [Fintype Player]
    {L : IExpr} [IExpr.ResultTypes L] {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (profile : Profile (setup.informationModel admission).behavioralSignature) :
    ((setup.informationModel admission).runBehavioral profile
      (instructionCount setup.program + 1)).map
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun terminal => utility (setup.parameterOutcome parameter terminal) who)) =
    ((setup.parameterGameForm parameter).play
      (setup.decodeBehavioralProfile admission profile)).map utility := by
  have law :
      ((setup.informationModel admission).runBehavioral profile
        (instructionCount setup.program + 1)).map
        (fun final => setup.protocolReadout final.state) =
      (setup.run (setup.decodeBehavioralProfile admission profile)).map some :=
    setup.runBehavioralFrom_readout admission profile _ _ (Nat.le_refl _)
  have valued := congrArg (PMF.map (fun output : Option (State L setup.program.terminalCtx) =>
    fun who => output.elim 0
      (fun terminal => utility (setup.parameterOutcome parameter terminal) who))) law
  change _ =
    (setup.parameterRun parameter (setup.decodeBehavioralProfile admission profile)).map utility
  rw [← setup.run_map_parameterOutcome, PMF.map_comp]
  simpa only [PMF.map_comp, Function.comp_def, Option.elim_some] using valued

end ProofReview
```
