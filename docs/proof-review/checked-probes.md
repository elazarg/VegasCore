# Checked proof-review experiments

These are isolated review experiments, not production APIs. Run the ordinary
project build, then python scripts/check-proof-review-probes.py to replay
all nineteen with the central Lake options. The runner writes only temporary files.
The [main review](../proof-review.md) states the scope and interpretation.
The twelve candidate modules below have exact axiom guards for all 32 public
probe theorems. The complete compiler-tail migrations are checked in their actual owning modules.

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
  exact InformationModel.bayesBelief_projection_of_proportional_reach (S.model M) M
    (S.liftProfile M profile) profile S.erase who site (S.sourceSite M who site)
    (fun x member => S.erase_mem M who site ⟨x, member⟩)
    (S.fiberMass M who site (S.erase witness.1)) fiber scalePositive.ne'
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
import Vegas.Pending.ExclusionEvidence
import Vegas.Pending.ReactiveCountAudit

noncomputable section

namespace ProofReview.Runtime

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
theorem exclusion_evidence_zero_iff (state : RecoveryState graph) :
    ExclusionEvidence 0 ∅ state ↔ state.native.ReceiptsComplete ∧
      ∀ owner, owner ∈ state.excluded ↔ ∃ event : graph.EventId,
        graph.actor? event = some owner ∧ state.native.PublicFailure event := by
  classical
  constructor
  · intro valid
    exact ⟨valid.receipts, valid.excluded_zero⟩
  · rintro ⟨receipts, excluded⟩
    refine ⟨receipts, ?_, ?_⟩
    · intro event impossible
      omega
    · intro owner
      simpa only [Finset.notMem_empty, false_or, Nat.zero_le, true_and] using
        excluded owner


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

## NormalizedWeightsProbe

<!-- probe: NormalizedWeightsProbe -->
```lean
import GameTheoryExtensions.Math.Probability.ProductTransport

noncomputable section

namespace ProofReview.NormalizedWeights

open Finset GameTheory.Math.Probability

theorem unit_payoff_half_l1 {α : Type*} [Fintype α]
    (p q payoff : α → ℝ) (mass : ∑ a, p a = ∑ a, q a)
    (unit : ∀ a, 0 ≤ payoff a ∧ payoff a ≤ 1) :
    |∑ a, p a * payoff a - ∑ a, q a * payoff a| ≤
      (∑ a, |p a - q a|) / 2 := by
  have centered : ∑ a, p a * payoff a - ∑ a, q a * payoff a =
      ∑ a, (p a - q a) * (payoff a - 1 / 2) := by
    rw [← sum_sub_distrib]
    calc
      _ = ∑ a, ((p a - q a) * (payoff a - 1 / 2) + (p a - q a) / 2) := by
        apply sum_congr rfl
        intro a _
        ring
      _ = _ := by
        rw [sum_add_distrib, ← sum_div, sum_sub_distrib, mass, sub_self, zero_div, add_zero]
  rw [centered]
  calc
    _ ≤ ∑ a, |(p a - q a) * (payoff a - 1 / 2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |p a - q a| / 2 := by
      apply sum_le_sum
      intro a _
      have interval : |payoff a - 1 / 2| ≤ 1 / 2 :=
        abs_le.mpr ⟨by linarith [(unit a).1], by linarith [(unit a).2]⟩
      rw [abs_mul]
      calc
        _ ≤ |p a - q a| * (1 / 2) :=
          mul_le_mul_of_nonneg_left interval (abs_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [sum_div]

theorem contamination_ratio {α : Type*} [Fintype α] {m s : α → ℝ} {η : ℝ}
    (m_nonneg : ∀ a, 0 ≤ m a) (s_nonneg : ∀ a, 0 ≤ s a)
    (m_pos : 0 < ∑ a, m a) (small : ∑ a, s a ≤ η * ∑ a, m a) :
    ∑ a, |(m a + s a) / ∑ b, (m b + s b) - m a / ∑ b, m b| ≤
      2 * η / (1 + η) := by
  let M := ∑ a, m a
  let S := ∑ a, s a
  have S_nonneg : 0 ≤ S := sum_nonneg fun a _ => s_nonneg a
  have ratio_nonneg : 0 ≤ S / M := div_nonneg S_nonneg m_pos.le
  have ratio_small : S / M ≤ η := (div_le_iff₀ m_pos).mpr small
  have positive : 0 < 1 + S / M := by linarith
  have close : ∑ a, |(m a + s a) - m a| ≤ (S / M) * M := by
    simp only [add_sub_cancel_left, abs_of_nonneg (s_nonneg _)]
    change S ≤ S / M * M
    rw [div_mul_cancel₀ _ m_pos.ne']
  have lower : (1 + S / M) * M ≤ ∑ a, (m a + s a) := by
    rw [sum_add_distrib]
    change (1 + S / M) * M ≤ M + S
    rw [add_mul, one_mul, div_mul_cancel₀ _ m_pos.ne']
  have bound := sum_abs_div_sum_sub_div_sum_le m_nonneg m_pos close positive lower
  have eta_nonneg : 0 ≤ η := ratio_nonneg.trans ratio_small
  have improved : 2 * (S / M) / (1 + S / M) ≤ 2 * η / (1 + η) := by
    rw [div_le_div_iff₀ positive (by linarith : 0 < 1 + η)]
    nlinarith
  exact bound.trans improved

end ProofReview.NormalizedWeights

/-- info: 'ProofReview.NormalizedWeights.unit_payoff_half_l1' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.NormalizedWeights.unit_payoff_half_l1

/-- info: 'ProofReview.NormalizedWeights.contamination_ratio' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.NormalizedWeights.contamination_ratio
```

## ConvergenceReuseProbe

<!-- probe: ConvergenceReuseProbe -->
```lean
import GameTheoryExtensions.Math.Probability.ActionSplitting
import GameTheoryExtensions.Analysis.Protocol.Perturbation

noncomputable section

namespace ProofReview.ConvergenceReuse

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter

theorem perturb_converges {Player : Type} {E : ExecutionProtocol Player}
    {M : InformationModel E} (reference : M.BehavioralAssessment)
    (profile : ∀ who, M.BehavioralPolicy who) (weight : Nat → ℝ)
    (nonnegative : ∀ n, 0 ≤ weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0)) (who : Player) (info : M.InfoState who) :
    PMFConvergesPointwise
      (fun n => (reference.perturb profile (weight n) (nonnegative n)
        (atMostOne n)).strategy who info) (profile who info) := by
  exact pmfConvergesPointwise_mix_zero weight nonnegative atMostOne vanishes
    (reference.strategy who info) (profile who info)

theorem split_converges {Raw Normal : Type} [Fintype Raw]
    (project : Raw → Normal) (canonical : Normal → Raw)
    (retract : ∀ action, project (canonical action) = action)
    (sequence : Nat → PMF Normal) (law : PMF Normal)
    (converges : PMFConvergesPointwise sequence law)
    (weight : Nat → ℝ) (nonnegative : ∀ n, 0 ≤ weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0)) :
    PMFConvergesPointwise
      (fun n => (sequence n).bind
        (PMF.splitKernel project canonical retract (weight n) (nonnegative n) (atMostOne n)))
      (law.map canonical) := by
  change PMFConvergesPointwise _ (law.bind fun action => PMF.pure (canonical action))
  apply converges.bind
  intro action
  exact pmfConvergesPointwise_mix_zero weight nonnegative atMostOne vanishes
    (PMF.fiberUniform project canonical retract action) (PMF.pure (canonical action))

theorem update_coordinate_converges {Player : Type} [DecidableEq Player]
    {E : ExecutionProtocol Player} {M : InformationModel E}
    (reference : ∀ player, M.BehavioralPolicy player) (who : Player)
    (policy : M.BehavioralPolicy who) (info : M.InfoState who) (weight : Nat → ℝ)
    (nonnegative : ∀ n, 0 ≤ weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0)) :
    PMFConvergesPointwise
      (fun n => Profile.update (sig := M.behavioralSignature) reference who
        (fun observed => mix (weight n) (nonnegative n) (atMostOne n)
          (reference who observed) (policy observed)) who info)
      (Profile.update (sig := M.behavioralSignature) reference who policy who info) := by
  simpa only [Profile.update_same] using
    pmfConvergesPointwise_mix_zero weight nonnegative atMostOne vanishes
      (reference who info) (policy info)

theorem bind_component_update {Player : Type} [DecidableEq Player]
    {Source Target : Player → Type}
    (component : ∀ who, Source who → PMF (Target who))
    (weights : ∀ who, PMF (Source who)) (who : Player) (alternative : PMF (Source who)) :
    (fun player => (Profile.update
      (sig := {Strategy := fun player => PMF (Source player), Outcome := Unit})
      weights who alternative player).bind (component player)) =
      Profile.update
        (sig := {Strategy := fun player => PMF (Target player), Outcome := Unit})
        (fun player => (weights player).bind (component player)) who
        (alternative.bind (component who)) := by
  exact Profile.map_update
    (sig := {Strategy := fun player => PMF (Source player), Outcome := Unit})
    (target := {Strategy := fun player => PMF (Target player), Outcome := Unit})
    (fun player law => law.bind (component player)) weights who alternative

end ProofReview.ConvergenceReuse

/-- info: 'ProofReview.ConvergenceReuse.perturb_converges' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.ConvergenceReuse.perturb_converges

/-- info: 'ProofReview.ConvergenceReuse.split_converges' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.ConvergenceReuse.split_converges

/-- info: 'ProofReview.ConvergenceReuse.update_coordinate_converges' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.ConvergenceReuse.update_coordinate_converges

/-- info: 'ProofReview.ConvergenceReuse.bind_component_update' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.ConvergenceReuse.bind_component_update
```

## PosteriorNaturalityProbe

<!-- probe: PosteriorNaturalityProbe -->
```lean
import GameTheoryExtensions.Math.Probability.NestedPosterior

noncomputable section

namespace ProofReview.PosteriorNaturality

open GameTheory.Math.Probability

theorem posterior_map_readout {A B Info : Type*} (law : PMF A)
    (read : A → B) (observe : B → Info) (observed : Info) :
    (fiberPosterior law (observe ∘ read) observed).map read =
      fiberPosterior (law.map read) observe observed := by
  classical
  by_cases present : observed ∈ (law.map (observe ∘ read)).support
  · exact map_fiberPosterior_readout law read observe observed present
  · have absentImage : observed ∉ ((law.map read).map observe).support := by
      simpa only [PMF.map_comp] using present
    rw [fiberPosterior_of_not_mem_support law (observe ∘ read) present,
      fiberPosterior_of_not_mem_support (law.map read) observe absentImage]

theorem accumulated_observation_mass {A B : Type} (law : PMF A)
    (old next : A → Bool) (field : A → B) (value : B)
    (same : ∀ point ∈ law.support,
      next point = true ↔ old point = true ∧ field point = value) :
    (law.map next) true = (law.map old) true *
      ((fiberPosterior law old true).map field) value := by
  classical
  let read := fun point => (old point, field point)
  let joint := law.map read
  have posterior : (fiberPosterior law old true).map read =
      fiberPosterior joint Prod.fst true := by
    exact posterior_map_readout law read Prod.fst true
  have conditional : ((fiberPosterior joint Prod.fst true).map Prod.snd) =
      (fiberPosterior law old true).map field := by
    rw [← posterior, PMF.map_comp]
    rfl
  have marginal : joint.map Prod.fst = law.map old := by
    simp only [joint, PMF.map_comp, read, Function.comp_def]
  have atom : joint (true, value) = (law.map next) true := by
    rw [PMF.map_apply, PMF.map_apply]
    apply tsum_congr
    intro point
    by_cases supported : point ∈ law.support
    · have fiber := same point supported
      simp only [read, Prod.mk.injEq]
      have predicates : (true = old point ∧ value = field point) =
          (true = next point) := by
        apply propext
        simpa only [eq_comm] using fiber.symm
      by_cases condition : true = next point
      · rw [ite_eq_left (Eq.mpr predicates condition), ite_eq_left condition]
      · rw [ite_eq_right (fun original => condition (Eq.mp predicates original)),
          ite_eq_right condition]
    · have zero := (PMF.apply_eq_zero_iff law point).mpr supported
      simp only [zero, ite_self]
  have balance := mul_fiberPosterior_map_snd_apply joint true value
  rw [marginal, conditional, atom] at balance
  exact balance.symm


end ProofReview.PosteriorNaturality

/-- info: 'ProofReview.PosteriorNaturality.posterior_map_readout' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.PosteriorNaturality.posterior_map_readout

/-- info: 'ProofReview.PosteriorNaturality.accumulated_observation_mass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.PosteriorNaturality.accumulated_observation_mass
```

## SourcePublicSplice

<!-- probe: SourcePublicSplice -->
```lean
import Vegas.Game.OnePacketSpliceForced
import Vegas.Game.OnePacketConditionalPrior

noncomputable section

namespace ProofReview.SourcePublicSplice

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [DecidableEq (CellTy Player L)]
  {p w : ProtocolState setup.program}

theorem initial_public_cells_eq {mine others : State L setup.context}
    (mineCells : InitialCellsAt mine p) (otherCells : InitialCellsAt others w)
    (agree : PublicCellsAgree setup p w) {name : VarId} {kind : CellTy Player L}
    (source : HasVar setup.context name kind) (publicKind : (cellField kind).IsPublic) :
    mine.get source = others.get source :=
  agree name kind publicKind _ _ (mineCells source) (otherCells source)

theorem initial_public_inputs_eq {mine others : State L setup.context}
    (mineCells : InitialCellsAt mine p) (otherCells : InitialCellsAt others w)
    (agree : PublicCellsAgree setup p w) (input : (graph setup).InputId)
    (publicField : (graph setup).fieldPublic (.inl input)) :
    setup.eventInputs mine input = setup.eventInputs others input := by
  obtain ⟨name, kind, source, found⟩ :=
    (ContextRefs.initial_coversPrefix setup.program).1 input
  have same : inputId source = input := Sum.inl.inj found
  subst input
  have publicKind : (cellField kind).IsPublic := by
    change (inputLayout setup.context (inputId source)).IsPublic at publicField
    rwa [inputLayout_inputId source] at publicField
  have cellEq := initial_public_cells_eq mineCells otherCells agree source publicKind
  have firstValue := encodeInputs_get mine source
  have secondValue := encodeInputs_get others source
  change cast _ (setup.eventInputs mine (inputId source)) = _ at firstValue
  change cast _ (setup.eventInputs others (inputId source)) = _ at secondValue
  have valuesEq := firstValue.trans ((congrArg cellValue cellEq).trans secondValue.symm)
  have back := congrArg (fun value =>
    cast (congrArg EventGraph.EventField.Value (inputLayout_inputId source)).symm value) valuesEq
  simpa only [cast_cast, cast_eq] using back

theorem drawn_splicePoint_given_public {Public : Type*}
    (signal : State L setup.context → Public)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : ∀ (first second : State L setup.context),
      (∀ input, (graph setup).fieldPublic (.inl input) →
        setup.eventInputs first input = setup.eventInputs second input) →
      signal first = signal second)
    (agree : PublicCellsAgree setup p w) {r : Player}
    (drawnP : ∃ initial ∈ setup.initialLaw.support, InitialCellsAt initial p)
    (drawnW : ∃ initial ∈ setup.initialLaw.support, InitialCellsAt initial w) :
    ∃ initial ∈ setup.initialLaw.support,
      InitialCellsAt initial (ProtocolState.splicePoint setup.program r p w) := by
  obtain ⟨mine, mineMember, mineCells⟩ := drawnP
  obtain ⟨others, othersMember, otherCells⟩ := drawnW
  have sameSignal := observable mine others (initial_public_inputs_eq mineCells otherCells agree)
  exact ⟨_, setup.splice_mem_support signal independent r mineMember othersMember sameSignal,
    initialCellsAt_splicePoint mineCells otherCells⟩

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

theorem forcedAgent_of_splice_given_public {Public : Type*}
    (signal : State L setup.context → Public) (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : ∀ (first second : State L setup.context),
      (∀ input, (graph setup).fieldPublic (.inl input) →
        setup.eventInputs first input = setup.eventInputs second input) →
      signal first = signal second)
    (covered : BindingFieldsCovered bounds)
    {who : Player} {current : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some current))
    {p w : ProtocolState setup.program}
    (decodedP : decodedPoint setup current.execution.application.config = some p)
    {second : setup.intendedProtocol.History} (secondState : second.state = some w)
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program w)
    (staticW : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) w)
    (readyOwn : ∀ event, current.execution.application.config.cut.Ready event →
      ∀ owner payload binding checks outputEq codeEq,
        nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
          owner = who)
    {r : Player}
    (succeed : CommitmentCellsSucceed setup p (ProtocolState.splicePoint setup.program r p w))
    {control : (application setup leaks).Control}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (isPrefix : TracePrefix prior trace) (different : r ≠ who) :
    forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon scheduler
      r ((application setup leaks).observe r (some control)) := by
  have publicAgree := publicCellsAgree_of_observe sameView
  have shape := ProtocolState.sameShape_of_observe_eq who setup.program p w sameView
  let q := ProtocolState.splicePoint setup.program r p w
  have publicAgreeQ : PublicCellsAgree setup p q := publicCellsAgree_splicePoint publicAgree
  have succeedQ : CommitmentCellsSucceed setup p q := succeed
  let swap := HiddenSwap.ofPairs (betweenPairs publicAgreeQ succeedQ)
    (betweenHandlePairs setup p q current.execution.application.accepted)
  -- The swap toward the splice is guarded at the end of the history.
  have drawnP : ∃ initial ∈ setup.initialLaw.support, InitialCellsAt initial p := by
    obtain ⟨initial, member, _, point, pointEq, found⟩ := decoded_initialCellsAt trace current rfl
    rw [decodedP, Option.some.injEq] at pointEq
    subst pointEq
    exact ⟨initial, member, found⟩
  have drawn := drawn_splicePoint_given_public signal independent observable publicAgree
    (r := r) drawnP
    (exists_initialCellsAt second.trace secondState)
  have staticP := decodedPoint_staticAt decodedP
  have guarded : SwapGuardState setup swap (swapAllowed swap) (some current) :=
    swapGuardState_of_agree drawn trace decodedP
      (fun event active owner payload binding checks outputEq codeEq view =>
        cell?_splicePoint_eq_of_agree (bindingCellsAgree_of_decoded (event := event)
          (owner := owner) (payload := payload) (binding := binding) (checks := checks)
          (outputEq := outputEq) (codeEq := codeEq) wellFormed secondState who sameView trace
          decodedP staticW readyOwn active view)) rfl
  have bounded := bounded_betweenHandlePairs (p := p) (q := q)
    (betweenPairs publicAgreeQ succeedQ) current.execution.application.accepted covered
  have fixes : swap.Fixes r :=
    fixes_between_of_visible (fun name _ visible => cell?_splicePoint_of_visible publicAgree name
      visible) (fun _ _ accepted => accepted_owner_of_trace trace accepted)
  -- The image of the end of the history is forced for `r`.
  have forcedEnd : ForcedState setup leaks r (some (swap.control current)) := by
    refine (forcedState_iff_decodedPoint _).mpr ⟨_, ?_,
      forcedPoint_splice shape staticP staticW
        (intended_of_history wellFormed second.trace w secondState) (Ne.symm different)⟩
    change decodedPoint setup (current.execution.application.config.swap
      (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgreeQ succeedQ))) = _
    rw [decodedPoint_betweenPairs, decodedP, Option.map_some]
  -- So is the image of the prefix, which carries `r`'s information there.
  have guardedPrior := swapGuardState_of_tracePrefix swap (initialClosed_swapAllowed swap) bounded
    isPrefix guarded
  have forcedPrior := forcedState_image_of_tracePrefix swap (initialClosed_swapAllowed swap)
    bounded r prior isPrefix guarded forcedEnd
  let symmetry := onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler swap
    (initialClosed_swapAllowed swap) bounded
  refine ⟨⟨_, symmetry.mapTrace prior guardedPrior⟩, ?_, forcedPrior⟩
  change (onePacketInformation setup leaks bounds horizon scheduler).infoOf r
    (symmetry.mapTrace prior guardedPrior) = _
  rw [onePacket_infoOf]
  exact observe_swap_of_fixes swap (initialClosed_swapAllowed swap) bounded fixes prior
    guardedPrior


end ProofReview.SourcePublicSplice

/-- info: 'ProofReview.SourcePublicSplice.initial_public_cells_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.SourcePublicSplice.initial_public_cells_eq

/-- info: 'ProofReview.SourcePublicSplice.initial_public_inputs_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.SourcePublicSplice.initial_public_inputs_eq

/-- info: 'ProofReview.SourcePublicSplice.drawn_splicePoint_given_public' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.SourcePublicSplice.drawn_splicePoint_given_public

/-- info: 'ProofReview.SourcePublicSplice.forcedAgent_of_splice_given_public' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.SourcePublicSplice.forcedAgent_of_splice_given_public
```

## PublicSignalPreserved

<!-- probe: PublicSignalPreserved -->
```lean
import Vegas.Game.OnePacketOwnerKeyedLate

noncomputable section

namespace ProofReview.PublicSignalPreserved

open Vegas Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

theorem splice_public_initial_inputs (who : Player) (mine others : State L setup.context)
    (input : (graph setup).InputId) (publicField : (graph setup).fieldPublic (.inl input)) :
    setup.eventInputs (splice who mine others) input = setup.eventInputs others input := by
  obtain ⟨name, kind, source, found⟩ :=
    (ContextRefs.initial_coversPrefix setup.program).1 input
  have same : inputId source = input := Sum.inl.inj found
  subst input
  have publicKind : (cellField kind).IsPublic := by
    change (inputLayout setup.context (inputId source)).IsPublic at publicField
    rwa [inputLayout_inputId source] at publicField
  have cellEq : (splice who mine others).get source = others.get source := by
    cases kind with
    | publicData payload => rfl
    | privateInput owner payload => exact publicKind.elim
    | commitment owner payload => exact publicKind.elim
    | publication payload => rfl
  have firstValue := encodeInputs_get (splice who mine others) source
  have secondValue := encodeInputs_get others source
  change cast _ (setup.eventInputs (splice who mine others) (inputId source)) = _ at firstValue
  change cast _ (setup.eventInputs others (inputId source)) = _ at secondValue
  have valuesEq := firstValue.trans ((congrArg cellValue cellEq).trans secondValue.symm)
  have back := congrArg (fun value =>
    cast (congrArg EventGraph.EventField.Value (inputLayout_inputId source)).symm value) valuesEq
  simpa only [cast_cast, cast_eq] using back

theorem public_signal_preserved {Public : Type*} (signal : State L setup.context → Public)
    (observable : ∀ (first second : State L setup.context),
      (∀ input, (graph setup).fieldPublic (.inl input) →
        setup.eventInputs first input = setup.eventInputs second input) →
      signal first = signal second)
    (who : Player) (mine others : State L setup.context) :
    signal (splice who mine others) = signal others :=
  observable _ _ (splice_public_initial_inputs who mine others)

end ProofReview.PublicSignalPreserved

/-- info: 'ProofReview.PublicSignalPreserved.splice_public_initial_inputs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.PublicSignalPreserved.splice_public_initial_inputs

/-- info: 'ProofReview.PublicSignalPreserved.public_signal_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.PublicSignalPreserved.public_signal_preserved
```

## TerminalAuditBounds

<!-- probe: TerminalAuditBounds -->
```lean
import GameTheoryExtensions.Analysis.Protocol.TerminalAudit
import GameTheory.Protocol.BehavioralTerminal

noncomputable section

namespace ProofReview.TerminalAuditBounds

open GameTheory GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player Observation : Type}
  {E : ExecutionProtocol Player} (M : InformationModel E)

theorem terminal_audit_payoff_bound
    (base : E.History → Player → ℝ) (observe : E.History → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (who : Player) {bound : ℝ}
    (bounded : ∀ final, E.terminal final.state → |base final who| ≤ bound) :
    ∀ final, E.terminal final.state →
      |TerminalAudit.utility base observe audit deposit final who| ≤ bound + |deposit who| := by
  intro final terminal
  have collected := TerminalAudit.charge_mem_Icc observe audit final who
  calc
    |TerminalAudit.utility base observe audit deposit final who| ≤
        |base final who| + |TerminalAudit.charge observe audit final who * deposit who| :=
      by simpa only [TerminalAudit.utility, sub_zero, zero_sub, abs_neg] using
        abs_sub_le (base final who) 0 (TerminalAudit.charge observe audit final who * deposit who)
    _ = |base final who| + TerminalAudit.charge observe audit final who * |deposit who| := by
      rw [abs_mul, abs_of_nonneg collected.1]
    _ ≤ bound + |deposit who| := by
      have charged := mul_le_mul_of_nonneg_right collected.2 (abs_nonneg (deposit who))
      linarith [bounded final terminal]

theorem terminal_audit_continuation_integrable [Fintype Player] [DecidableEq Player]
    (assessment : M.BehavioralAssessment) (certificate : E.WellFoundedHistories)
    {who : Player} (site : M.InformationSite who)
    (base : E.History → Player → ℝ) (observe : E.History → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    {bound : ℝ}
    (bounded : ∀ final, E.terminal final.state → |base final who| ≤ bound)
    (alternative : M.BehavioralPolicy who) :
    (assessment.continuationContext certificate site
      (fun final => TerminalAudit.utility base observe audit deposit final who)).IntegrableAt
        alternative :=
  assessment.continuationContext_integrable_of_bounded_terminal certificate site _
    (bound + |deposit who|)
    (terminal_audit_payoff_bound base observe audit deposit who bounded) alternative

end ProofReview.TerminalAuditBounds

/-- info: 'ProofReview.TerminalAuditBounds.terminal_audit_payoff_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.TerminalAuditBounds.terminal_audit_payoff_bound

/-- info: 'ProofReview.TerminalAuditBounds.terminal_audit_continuation_integrable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.TerminalAuditBounds.terminal_audit_continuation_integrable
```

## OwnTrafficLocalityProbe

<!-- probe: OwnTrafficLocalityProbe -->
```lean
import Vegas.Game.RecoveryCountIncentives

noncomputable section

namespace ProofReview.Runtime

open Interaction GameTheory.Protocol GameTheory.Math.Probability Vegas Vegas.EventGraphRuntime

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- A verdict using earlier same-author inputs is locally testable from actual recall. -/
theorem own_verdict_iff_outputs
    (verdict : List (Message Principal app.Payload) → Message Principal app.Payload → Bool)
    (congruent : ∀ left right message,
      (∀ other, (other ∈ left ∧ other.sender = message.sender ∧ other.id.2 < message.id.2) ↔
        (other ∈ right ∧ other.sender = message.sender ∧ other.id.2 < message.id.2)) →
      verdict left message = verdict right message)
    (execution : app.Execution) (recalled : execution.InputRecall app) (who : Principal) :
    (∀ message ∈ execution.network.inputs, message.sender = who →
      verdict execution.network.inputs message = true) ↔
      ∀ message ∈ app.outputs (execution.recall who),
        verdict (app.outputs (execution.recall who)) message = true := by
  classical
  have localVerdict (message : Message Principal app.Payload) (owner : message.sender = who) :
      verdict execution.network.inputs message =
        verdict (app.outputs (execution.recall who)) message := by
    apply congruent
    intro other
    simpa only [owner] using recalled.earlier_inputs_iff_outputs message other
  constructor
  · intro clean message present
    rw [← recalled who] at present
    obtain ⟨member, owner⟩ := List.mem_filter.mp present
    have owned : message.sender = who := by simpa using owner
    rw [← localVerdict message owned]
    exact clean message member owned
  · intro clean message member owner
    rw [localVerdict message owner]
    apply clean
    rw [← recalled who]
    exact List.mem_filter.mpr ⟨member, by simpa using owner⟩

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- An observed clean own-output record supplies every history in the actual fiber. -/
theorem owner_clean_of_local_past
    (menu : (runtime.recoveryApplication leaks).ResponseMenu)
    (initial : PMF (runtime.recoveryApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.recoveryApplication leaks).Scheduler) (who : Player)
    (site : (menu.information initial horizon scheduler).InformationSite who)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (atSite : site.1 = some (past, view))
    (clean : ∀ message ∈ (runtime.recoveryApplication leaks).outputs past,
      countPermits ((runtime.recoveryApplication leaks).outputs past) message = true)
    (history : (menu.information initial horizon scheduler).InformationHistory who site.1) :
    ReactiveApplication.executionInvariant (Recovery.OwnerCountClean runtime leaks who)
      history.1.state := by
  let app := runtime.recoveryApplication leaks
  have observed := (menu.info initial horizon scheduler who history.1.trace).symm.trans
    (history.2.trans atSite)
  cases stateEq : history.1.state with
  | none => trivial
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, stateEq, active, ↓reduceIte] at observed
        have pair := Option.some.inj observed
        have recallEq : control.execution.recall who = past := congrArg Prod.fst pair
        have recalled := app.history_inputRecall initial horizon scheduler
          (stateEq ▸ menu.toRawTrace initial horizon scheduler history.1.trace)
        apply (own_verdict_iff_outputs app countPermits
          (fun left right message same => countPermits_congr left right message same)
          control.execution recalled who).mpr
        rw [recallEq]
        exact clean
      · simp [ReactiveApplication.observe, stateEq, active] at observed

/-- Without InputRecall, an empty local output list can omit an earlier violation. -/
theorem missing_recall_obstruction {Payload : Type} (payload : Payload) :
    let first : Message Unit Payload := ⟨((), 0), payload⟩
    let second : Message Unit Payload := ⟨((), 1), payload⟩
    let permitted := fun (inputs : List (Message Unit Payload)) message =>
      ¬ ∃ other ∈ inputs, other.sender = message.sender ∧ other.id.2 < message.id.2
    (∀ message ∈ ([] : List (Message Unit Payload)), permitted [] message) ∧
      ¬ ∀ message ∈ [first, second], permitted [first, second] message := by
  intro first second permitted
  refine ⟨by simp, ?_⟩
  intro clean
  have noEarlier := clean second (by simp)
  exact noEarlier ⟨first, by simp, rfl, by change (0 : Nat) < 1; decide⟩

end ProofReview.Runtime

/-- info: 'ProofReview.Runtime.own_verdict_iff_outputs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.Runtime.own_verdict_iff_outputs

/-- info: 'ProofReview.Runtime.owner_clean_of_local_past' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.Runtime.owner_clean_of_local_past

/-- info: 'ProofReview.Runtime.missing_recall_obstruction' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.Runtime.missing_recall_obstruction
```

## HandlerCertificateProjectionProbe

<!-- probe: HandlerCertificateProjectionProbe -->
```lean
import Vegas.Pending.ReactiveEventStability

noncomputable section

namespace ProofReview.Runtime

open Vegas Vegas.EventGraph Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Exact commitment certificates already contain vacant-handle evidence. -/
theorem certificate_vacant (runtime : EventGraphRuntime graph) (state next : State graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (accepted : handle runtime state ⟨id, .commitment event candidate⟩ = some next) :
    state.accepted (.inr event) = none := by
  obtain ⟨_ready, _timely, _owner, _payload, _outputEq, _codeEq, _view, _sender,
    _handleOwner, vacant, _unused, _nextEq⟩ :=
    (handle_commitment_iff runtime state next id event candidate).mp accepted
  exact vacant

/-- Commitment graph support and physical frames are projections of the same certificate. -/
theorem commitment_step_from_certificate
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (accepted : handle runtime state ⟨id, .commitment event candidate⟩ = some next) :
    ∃ (ready : state.config.cut.Ready event) (action : graph.Action event),
      next.config ∈ (state.config.step event ready action).support ∧
        next.clock = state.clock ∧
        next.activatedAt = State.refreshActivated next.config state.clock state.activatedAt := by
  obtain ⟨ready, _timely, owner, payload, outputEq, codeEq, _view, _sender,
    _handleOwner, _vacant, _unused, nextEq⟩ :=
    (handle_commitment_iff runtime state next id event candidate).mp accepted
  rw [nextEq]
  let result := state.bindingResult candidate payload
  refine ⟨ready, cast (congrArg EventField.Action outputEq.symm) result, ?_, rfl, rfl⟩
  change state.config.complete event ready
    (cast (congrArg EventField.Action outputEq.symm) result)
    (cast (congrArg EventField.Value outputEq.symm) result) ∈
      (state.config.step event ready
        (cast (congrArg EventField.Action outputEq.symm) result)).support
  rw [state.config.step_eq_map_of_code event ready outputEq (.bind owner payload)
    codeEq result (PMF.pure result) rfl]
  simp

/-- The opening projection retains the actual action and deferred-check result. -/
theorem opening_step_from_certificate
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (raw : Raw L)
    (accepted : handle runtime state ⟨id, .opening event candidate raw⟩ = some next) :
    ∃ (ready : state.config.cut.Ready event) (action : graph.Action event),
      next.config ∈ (state.config.step event ready action).support ∧
        next.clock = state.clock ∧
        next.activatedAt = State.refreshActivated next.config state.clock state.activatedAt ∧
        ∃ (owner : Player) (payload : L.Ty)
          (binding : FieldRef graph.layout (.binding owner payload))
          (checks : List (GuardCheck graph.layout payload))
          (outputEq : graph.outputLayout event = .publication payload)
          (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
            (graph.nodes event) = .resolve owner payload binding checks),
          nodeView graph event = .resolve owner payload binding checks outputEq codeEq ∧
            action = cast (congrArg EventField.Action outputEq.symm) true := by
  obtain ⟨ready, _timely, owner, payload, binding, checks, outputEq, codeEq, _value,
    result, view, _sender, _handleOwner, _associated, _rawEq, _verified, _stored,
    resolved, nextEq⟩ :=
    (handle_opening_iff runtime state next id event candidate raw).mp accepted
  rw [nextEq]
  refine ⟨ready, cast (congrArg EventField.Action outputEq.symm) true, ?_, rfl, rfl,
    owner, payload, binding, checks, outputEq, codeEq, view, rfl⟩
  change state.config.complete event ready
    (cast (congrArg EventField.Action outputEq.symm) true)
    (cast (congrArg EventField.Value outputEq.symm) result) ∈
      (state.config.step event ready
        (cast (congrArg EventField.Action outputEq.symm) true)).support
  rw [state.config.step_eq_map_of_code event ready outputEq
    (.resolve owner payload binding checks) codeEq true (PMF.pure result)]
  · simp
  · rw [EventCode.resolve_eval?, resolved]
    rfl

end ProofReview.Runtime

/-- info: 'ProofReview.Runtime.certificate_vacant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.Runtime.certificate_vacant

/-- info: 'ProofReview.Runtime.commitment_step_from_certificate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.Runtime.commitment_step_from_certificate

/-- info: 'ProofReview.Runtime.opening_step_from_certificate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.Runtime.opening_step_from_certificate
```

## RecordedEntryPrefix

<!-- probe: RecordedEntryPrefix -->
```lean
import Vegas.Game.OnePacketFirstActivation

noncomputable section

namespace ProofReview.RecordedEntryPrefix

open Vegas Vegas.SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

theorem recordsEntry_transition_from_prefix (who : Player)
    (entry : (application setup leaks).PlayerEntry)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (before after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (holds : RecordsEntry setup leaks who entry before)
    (reached : after ∈ ((application setup leaks).transition initial horizon scheduler before
      joint).support) :
    RecordsEntry setup leaks who entry after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨next, rfl, recalls⟩ := (application setup leaks).transition_recall_prefix
        initial horizon scheduler control after joint reached
      obtain ⟨earlier, later, split⟩ := holds
      obtain ⟨tail, retained⟩ := recalls who
      refine ⟨earlier, later ++ tail, ?_⟩
      rw [← retained, split]
      simp only [List.append_assoc, List.cons_append]

end ProofReview.RecordedEntryPrefix

/-- info: 'ProofReview.RecordedEntryPrefix.recordsEntry_transition_from_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.RecordedEntryPrefix.recordsEntry_transition_from_prefix
```

## SourceRawSupport

<!-- probe: SourceRawSupport -->
```lean
import Vegas.Source.CommitRecoveryState

noncomputable section
namespace ProofReview.SourceRawSupport
open Vegas Vegas.SourceProgram GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

theorem raw_step_result (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) (target : CommitRecoveryState program)
    (supported : target ∈ (state.step joint).support) :
    ∃ result : {result : ProtocolState program × Finset Player // state.excluded ⊆ result.2},
      result.1 ∈ (ProtocolState.recoveryStep program state.point state.excluded joint).support ∧
        target = (state.install result.1 result.2).close := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  refine ⟨result, ?_, rfl⟩
  rw [← map_val_pmfToSubtype
    (ProtocolState.recoveryStep program state.point state.excluded joint)
    (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
      state.excluded joint result supported)]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
end ProofReview.SourceRawSupport

/-- info: 'ProofReview.SourceRawSupport.raw_step_result' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.SourceRawSupport.raw_step_result
```

## SourceRawConsumers

<!-- probe: SourceRawConsumers -->
```lean
import Vegas.Source.CommitRecoveryAttemptReset
import Vegas.Source.CommitRecoveryControl
import Vegas.Source.CommitRecoveryProjection
import Vegas.Source.CommitRecoveryOwnHistory

noncomputable section
namespace ProofReview.SourceRawConsumers
open Vegas Vegas.SourceProgram GameTheory.Math.Probability
open GameTheory.Protocol
open Vegas.SourceProgram.CommitRecoveryState
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

theorem control_increases (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (running : ¬ ProtocolState.terminal program state.point)
    (supported : next ∈ (state.step joint).support) : state.control < next.control := by
  obtain ⟨result, rawMember, rfl⟩ := state.step_raw_result joint next supported
  have consumed := ProtocolState.recoveryStep_remaining program state.point state.excluded joint
    result.1 running rawMember
  let after := state.install result.1 result.2
  change state.control < after.close.control
  have beforeBound := ProtocolState.remaining_le_instructionCount program state.point
  by_cases retries : after.Finished ∧ after.NewFailure ∧ after.Survives
  · rw [close_of_retry after retries.1 retries.2.1 retries.2.2]
    change state.generation * (instructionCount program + 1) +
        (instructionCount program - ProtocolState.remaining program state.point) <
      (state.generation + 1) * (instructionCount program + 1) +
        (instructionCount program - ProtocolState.remaining program after.retry.point)
    rw [Nat.add_mul]
    omega
  · have rank := after.close_remaining_le retries
    have generation : after.close.generation = state.generation := by
      unfold close
      split
      · split
        · split
          · exact (retries ⟨by assumption, by assumption, by assumption⟩).elim
          · rfl
        · rfl
      · split <;> rfl
    unfold Vegas.SourceProgram.CommitRecoveryState.control
    rw [generation]
    change ProtocolState.remaining program after.close.point ≤
      ProtocolState.remaining program result.1.1 at rank
    change ProtocolState.remaining program result.1.1 + 1 =
      ProtocolState.remaining program state.point at consumed
    omega

theorem potential_decreases [Fintype Player] (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (running : ¬ ProtocolState.terminal program state.point)
    (supported : next ∈ (state.step joint).support) : next.potential < state.potential := by
  obtain ⟨result, rawMember, rfl⟩ := state.step_raw_result joint next supported
  have consumed := ProtocolState.recoveryStep_remaining program state.point state.excluded joint
    result.1 running rawMember
  let after := state.install result.1 result.2
  change after.close.potential < state.potential
  have beforeCard := Finset.card_le_univ (s := state.entryExcluded)
  have afterCard := Finset.card_le_univ (s := after.excluded)
  by_cases retries : after.Finished ∧ after.NewFailure ∧ after.Survives
  · rw [close_of_retry after retries.1 retries.2.1 retries.2.2]
    have increased := after.retry_entry_card retries.2.1
    have budget : Fintype.card Player - after.retry.entryExcluded.card + 1 ≤
        Fintype.card Player - state.entryExcluded.card := by
      change Fintype.card Player - after.excluded.card + 1 ≤
        Fintype.card Player - state.entryExcluded.card
      change state.entryExcluded.card + 1 ≤ after.excluded.card at increased
      change after.excluded.card ≤ Fintype.card Player at afterCard
      omega
    have scaled := Nat.mul_le_mul_right (instructionCount program + 1) budget
    have bound := ProtocolState.remaining_le_instructionCount program after.retry.point
    dsimp only [potential]
    nlinarith
  · have entries := Finset.card_le_card after.entryExcluded_close
    have budget : Fintype.card Player - after.close.entryExcluded.card ≤
        Fintype.card Player - state.entryExcluded.card := by
      change state.entryExcluded.card ≤ after.close.entryExcluded.card at entries
      omega
    have scaled := Nat.mul_le_mul_right (instructionCount program + 1) budget
    have rank := after.close_remaining_le retries
    change ProtocolState.remaining program result.1.1 + 1 =
      ProtocolState.remaining program state.point at consumed
    change ProtocolState.remaining program after.close.point ≤
      ProtocolState.remaining program result.1.1 at rank
    dsimp only [potential]
    omega

theorem clear_step_projects (state : CommitRecoveryState program) (clear : state.excluded = ∅)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (supported : next ∈ (state.step joint).support) (nextClear : next.excluded = ∅) :
    next.point ∈ (ProtocolState.step program state.point
      (fun who => (joint who).map (·.action))).support := by
  obtain ⟨result, rawMember, rfl⟩ := state.step_raw_result joint next supported
  have resultClear : result.1.2 = ∅ := by
    simpa only [close_excluded, install] using nextClear
  have noFailure : ¬ (state.install result.1 result.2).NewFailure := by
    simp only [NewFailure, install, resultClear, Finset.empty_sdiff,
      Finset.not_nonempty_empty, not_false_eq_true]
  rw [close_point_of_no_new_failure _ noFailure]
  have sourceLaw : (ProtocolState.recoveryStep program state.point state.excluded joint).map
      Prod.fst = ProtocolState.step program state.point
        (fun who => (joint who).map (·.action)) := by
    rw [clear]
    exact ProtocolState.recoveryStep_empty_point program state.point joint
  rw [← sourceLaw]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result.1, rawMember, rfl⟩

theorem own_history_preserved {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (who : Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : IsLegalJoint state.Active state.available joint)
    (next : CommitRecoveryState program) (supported : next ∈ (state.step joint).support)
    (survives : who ∉ next.excluded) :
    ProtocolState.history program next.point who =
      ProtocolState.history program state.point who ++ ((joint who).map (·.action)).toList := by
  have before : who ∉ state.excluded := fun excluded =>
    survives (state.step_excluded_monotone joint next supported excluded)
  obtain ⟨result, rawMember, rfl⟩ := state.step_raw_result joint next supported
  rw [close_history]
  exact ProtocolState.recoveryStep_own_history who program state.point state.excluded joint
    legal before result.1 rawMember
end ProofReview.SourceRawConsumers

/-- info: 'ProofReview.SourceRawConsumers.control_increases' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.SourceRawConsumers.control_increases

/-- info: 'ProofReview.SourceRawConsumers.potential_decreases' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.SourceRawConsumers.potential_decreases

/-- info: 'ProofReview.SourceRawConsumers.clear_step_projects' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.SourceRawConsumers.clear_step_projects

/-- info: 'ProofReview.SourceRawConsumers.own_history_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.SourceRawConsumers.own_history_preserved
```

## TimingSettlement

<!-- probe: TimingSettlement -->
```lean
import Vegas.Game.SourceServiceTurnSettlement
import GameTheoryExtensions.Math.Probability.Expectation

noncomputable section

namespace ProofReview.TimingRetention

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Enforcement
open GameTheory.Math.Probability Interaction EventGraphRuntime

private theorem branch_lower {α β : Type} (timing : PMF α) (index : α)
    (branch : α → PMF β) (outcome : β) :
    (timing index).toReal * (branch index outcome).toReal ≤
      ((timing.bind branch) outcome).toReal := by
  rw [← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
  rw [PMF.bind_apply]
  exact ENNReal.le_tsum (f := fun other => timing other * (branch other) outcome) index

private theorem bind_right_lower {α β : Type} (initial : PMF α)
    (source target : α → PMF β) (factor : ℝ)
    (lower : ∀ state ∈ initial.support, ∀ outcome,
      factor * (source state outcome).toReal ≤ (target state outcome).toReal)
    (outcome : β) :
    factor * ((initial.bind source) outcome).toReal ≤
      ((initial.bind target) outcome).toReal := by
  simpa only [one_mul] using bind_supported_domination initial initial source target
    1 factor (by norm_num) (fun _ => by simp) lower outcome

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

theorem overriddenTurnProfile_fix_roundsFrom_bind_lower {β : Type}
    (initial : PMF (EventGraphRuntime.State (serviceGraph setup mode)))
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (horizon : Nat)
    (bound : (serviceGraph setup mode).EventId → Nat) {turns : Nat}
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (override : Player → Option (serviceApplication setup mode deadline leaks).Policy)
    (event : (serviceGraph setup mode).EventId)
    (readout : (serviceApplication setup mode deadline leaks).Execution → PMF β) :
    ∀ outcome, (1 - timing.deferral event) *
      ((((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (overriddenTurnProfile bound turns (timing.fix event 0) profile override) horizon).bind
          readout) outcome).toReal ≤
      ((((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (overriddenTurnProfile bound turns timing profile override) horizon).bind readout)
          outcome).toReal := by
  let app := serviceApplication setup mode deadline leaks
  intro outcome
  have nonneg := deferral_nonneg timing event
  cases owned : (serviceGraph setup mode).actor? event with
  | none =>
      have same : overriddenTurnProfile (deadline := deadline) (leaks := leaks) bound turns
          (timing.fix event 0) profile override =
          overriddenTurnProfile bound turns timing profile override := by
        funext who
        unfold overriddenTurnProfile
        rw [serviceTurnPolicy_fix_of_not_owner bound timing profile event 0 who
          (by rw [owned]; exact fun absurd => by cases absurd)]
      rw [same]
      exact mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith)
  | some owner =>
      cases overridden : override owner with
      | some policy =>
          have same : overriddenTurnProfile (deadline := deadline) (leaks := leaks) bound turns
              (timing.fix event 0) profile override =
              overriddenTurnProfile bound turns timing profile override := by
            funext who
            unfold overriddenTurnProfile
            by_cases isOwner : who = owner
            · subst isOwner
              simp only [overridden, Option.getD_some]
            · rw [serviceTurnPolicy_fix_of_not_owner bound timing profile event 0 who
                (by rw [owned]; exact fun equal => isOwner (Option.some.inj equal).symm)]
          rw [same]
          exact mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith)
      | none =>
          let base := overriddenTurnProfile (deadline := deadline) (leaks := leaks) bound turns
            timing profile override
          let member := fun slot : Fin (turns + 1) =>
            serviceTurnPolicy setup mode deadline leaks bound turns (timing.fix event slot) profile
              owner
          have fixed (slot : Fin (turns + 1)) :
              overriddenTurnProfile (deadline := deadline) (leaks := leaks) bound turns
                (timing.fix event slot) profile override =
                Function.update base owner (member slot) := by
            funext who
            by_cases isOwner : who = owner
            · subst isOwner
              simp only [Function.update_self, member, overriddenTurnProfile, overridden,
                Option.getD_none]
            · rw [Function.update_of_ne isOwner]
              simp only [base, overriddenTurnProfile]
              rw [serviceTurnPolicy_fix_of_not_owner bound timing profile event slot who
                (by rw [owned]; exact fun equal => isOwner (Option.some.inj equal).symm)]
          have mixed : base = Function.update base owner
              (app.policyMixture (timing event owner owned) member).policy := by
            funext who
            by_cases isOwner : who = owner
            · subst isOwner
              rw [Function.update_self, serviceTurnPolicy_eq_timingMixture bound timing profile
                event who owned]
              simp only [base, overriddenTurnProfile, overridden, Option.getD_none]
            · rw [Function.update_of_ne isOwner]
          rw [fixed 0]
          change (1 - timing.deferral event) *
            (((app.roundsFrom initial scheduler (Function.update base owner (member 0))
              horizon).bind readout) outcome).toReal ≤
            (((app.roundsFrom initial scheduler base horizon).bind readout) outcome).toReal
          unfold ReactiveApplication.roundsFrom
          rw [PMF.bind_bind, PMF.bind_bind]
          apply bind_right_lower
          intro state _ value
          conv_rhs => rw [mixed]
          rw [← app.runRounds_policyMixture scheduler (timing event owner owned) member
            owner base horizon (ReactiveApplication.Execution.initial app state)]
          have prior : (app.policyMixture (timing event owner owned) member).posterior
              ((ReactiveApplication.Execution.initial app state).recall owner) =
                timing event owner owned :=
            app.policyMixture_posterior_of_agree _ _ app.silentPolicy _
              fun before entry member => by
                have empty := List.prefix_nil.mp member
                simp at empty
          rw [prior, PMF.bind_bind]
          have factor : 1 - timing.deferral event = (timing event owner owned 0).toReal := by
            unfold TurnTiming.deferral
            split
            · rename_i absent
              rw [owned] at absent
              cases absent
            · rename_i who ownedWho
              have same : who = owner := Option.some.inj (ownedWho.symm.trans owned)
              subst same
              ring
          rw [factor]
          exact branch_lower (timing event owner owned) 0
            (fun slot => (app.runRounds scheduler (Function.update base owner (member slot))
              horizon (ReactiveApplication.Execution.initial app state)).bind readout) value

private theorem retention_nonneg {turns : Nat} (timing : TurnTiming setup turns mode)
    (event : (serviceGraph setup mode).EventId) : 0 ≤ 1 - timing.deferral event := by
  unfold TurnTiming.deferral
  split
  · norm_num
  · simpa only [sub_sub_cancel] using
      (ENNReal.toReal_nonneg (a := timing event _ _ 0))

theorem overriddenTurnProfile_roundsFrom_bind_product_lower {β : Type}
    (initial : PMF (EventGraphRuntime.State (serviceGraph setup mode)))
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (horizon : Nat)
    (bound : (serviceGraph setup mode).EventId → Nat) {turns : Nat}
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (override : Player → Option (serviceApplication setup mode deadline leaks).Policy)
    (readout : (serviceApplication setup mode deadline leaks).Execution → PMF β) :
    ∀ outcome, (∏ event, (1 - timing.deferral event)) *
      ((((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (overriddenTurnProfile bound turns (firstTurnTiming setup turns mode) profile override)
          horizon).bind readout) outcome).toReal ≤
      ((((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (overriddenTurnProfile bound turns timing profile override) horizon).bind readout)
          outcome).toReal := by
  have general : ∀ (events : List (serviceGraph setup mode).EventId), events.Nodup →
      ∀ current : TurnTiming setup turns mode, ∀ outcome,
      ((events.map fun event => 1 - current.deferral event).prod) *
        ((((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
          (overriddenTurnProfile bound turns (current.fixFirst events) profile override)
            horizon).bind readout) outcome).toReal ≤
        ((((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
          (overriddenTurnProfile bound turns current profile override) horizon).bind readout)
            outcome).toReal := by
    intro events
    induction events with
    | nil => intro _ current outcome; simp [TurnTiming.fixFirst]
    | cons event rest ih =>
        intro distinct current outcome
        obtain ⟨absent, restDistinct⟩ := List.nodup_cons.mp distinct
        have step := overriddenTurnProfile_fix_roundsFrom_bind_lower initial scheduler horizon
          bound current profile override event readout outcome
        have later := ih restDistinct (current.fix event 0) outcome
        have sameWeights :
            (rest.map fun other => 1 - (current.fix event 0).deferral other).prod =
              (rest.map fun other => 1 - current.deferral other).prod := by
          congr 1
          apply List.map_congr_left
          intro other member
          rw [current.fix_deferral_of_ne event other 0 fun same => absent (same ▸ member)]
        rw [sameWeights] at later
        have scaled := mul_le_mul_of_nonneg_left later (retention_nonneg current event)
        simpa only [List.map_cons, List.prod_cons, TurnTiming.fixFirst, mul_assoc] using
          scaled.trans step
  have all := general (List.finRange _) (List.nodup_finRange _) timing
  rw [timing.fixFirst_all, ← Fin.prod_univ_def] at all
  exact all

theorem overriddenTurnProfile_roundsFrom_bind_product_within {β : Type}
    (initial : PMF (EventGraphRuntime.State (serviceGraph setup mode)))
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (horizon : Nat)
    (bound : (serviceGraph setup mode).EventId → Nat) {turns : Nat}
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (override : Player → Option (serviceApplication setup mode deadline leaks).Policy)
    (readout : (serviceApplication setup mode deadline leaks).Execution → PMF β) :
    PMF.WithinTV (1 - ∏ event, (1 - timing.deferral event))
      (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (overriddenTurnProfile bound turns timing profile override) horizon).bind readout)
      (((serviceApplication setup mode deadline leaks).roundsFrom initial scheduler
        (overriddenTurnProfile bound turns (firstTurnTiming setup turns mode) profile override)
          horizon).bind readout) := by
  apply PMF.WithinTV.symm
  apply PMF.WithinTV.of_domination
  · exact Finset.prod_le_one₀ (fun event _ => retention_nonneg timing event)
      (fun event _ => by linarith [deferral_nonneg timing event])
  · exact overriddenTurnProfile_roundsFrom_bind_product_lower initial scheduler horizon
      bound timing profile override readout

theorem sourceServiceTurnPolicy_execution_settlement_product_lawError
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceLaw setup mode deadline leaks horizon scheduler bound turns profile)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    PMF.WithinTV (1 - ∏ event, (1 - timing.deferral event))
      (((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (serviceTurnPolicy setup mode deadline leaks bound turns timing profile)
          horizon).bind
          (fun execution =>
            (TerminalAudit.settlement (serviceBaseUtility setup mode deadline leaks utility)
              ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
              (serviceSourceAudit setup mode deadline leaks sample) deposit
                ((serviceApplication setup mode deadline leaks).finished execution)).map
              fun payoffs => (serviceSourceReadout setup mode deadline leaks
                ((serviceApplication setup mode deadline leaks).finished execution), payoffs)))
      ((setup.run profile).map (fun state => (some state, utility state))) := by
  rw [← sourceServiceFirstTurn_settlement_law contract timely profile terminal sample
    authentic utility deposit]
  exact overriddenTurnProfile_roundsFrom_bind_product_within (serviceInitialLaw setup mode)
    scheduler horizon bound timing profile (fun _ => none) _

end ProofReview.TimingRetention

/-- info: 'ProofReview.TimingRetention.overriddenTurnProfile_fix_roundsFrom_bind_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.TimingRetention.overriddenTurnProfile_fix_roundsFrom_bind_lower

/-- info: 'ProofReview.TimingRetention.overriddenTurnProfile_roundsFrom_bind_product_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.TimingRetention.overriddenTurnProfile_roundsFrom_bind_product_lower

/-- info: 'ProofReview.TimingRetention.overriddenTurnProfile_roundsFrom_bind_product_within' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.TimingRetention.overriddenTurnProfile_roundsFrom_bind_product_within

/-- info: 'ProofReview.TimingRetention.sourceServiceTurnPolicy_execution_settlement_product_lawError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ProofReview.TimingRetention.sourceServiceTurnPolicy_execution_settlement_product_lawError
```
