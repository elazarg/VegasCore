/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.RefinementKernelGame
import Vegas.Machine.Audited
import Vegas.Machine.MessageInFlight
import Vegas.Runtime.CodecMachine
import Vegas.Frontier.SourceAdequacy
import Vegas.Frontier.Games.ProgramAPI
import GameTheory.Concepts.Transport.Corners
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import Math.ProbabilityMassFunction

/-!
# Runtime trace adequacy

Runtime-general proof interfaces connecting profile-indexed event-batch laws on
implementation machines to checked-program game surfaces.
-/

namespace Vegas

namespace WFProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}

section Strategic

variable [Fintype Player]

/-- Primitive compiled machine used as the specification runtime for a checked
program. -/
noncomputable abbrev PrimitiveSpecMachine
    (program : WFProgram Player L) :=
  ToEventGraph.PrimitiveMachine (ToEventGraph.compile program.core)

/-- A strategy-indexed game surface realized by primitive traces.

The surface specifies the strategy-indexed game to preserve and the canonical
primitive-trace kernel that realizes that game on the compiled specification
machine. Behavioral, pure, and product mixed-pure frontier play are canonical
instances, but the abstraction itself is exactly trace adequacy for a game
surface. -/
structure TraceGameSurface
    (program : WFProgram Player L) [FiniteDomains program] where
  game : GameTheory.KernelGame Player
  traceKernel :
    (∀ player, game.Strategy player) →
      PMF
        ((ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core)).EventBatchTrace)
  traceKernel_udist :
    ∀ profile,
      (traceKernel profile).bind
          (fun trace =>
            PMF.pure
              (Machine.eventBatchTraceUtility
                (ToEventGraph.PrimitiveMachine
                  (ToEventGraph.compile program.core))
                (fun _ => 0) trace)) =
        game.udist profile

/-- Payoff-vector law induced by a distribution over strategy profiles.

This is the utility-distribution view of a correlated profile law; it is the
right object for comparing trace/runtime presentations when the outcome
carriers differ but utilities agree. -/
noncomputable def correlatedUtilityLaw
    (G : GameTheory.KernelGame Player) (profileLaw : PMF G.Profile) :
    PMF (GameTheory.Payoff Player) :=
  profileLaw.bind G.udist

/-- Canonical primitive event-batch trace distribution extracted from the
checked program's behavioral frontier run. -/
noncomputable def behavioralFrontierEventBatchTraceKernel
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    PMF
      ((ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).EventBatchTrace) :=
  PMF.map
    ((program.frontierSemantics.behavioral.view).boundedHistoryTrace
      program.frontierSemantics.horizon)
    (program.frontierSemantics.behavioralHistoryKernel profile)

/-- Primitive event-batch trace distribution induced by a pure frontier
profile through its degenerate behavioral realization. -/
noncomputable def pureFrontierEventBatchTraceKernel
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    PMF
      ((ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).EventBatchTrace) :=
  behavioralFrontierEventBatchTraceKernel program
    ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
      program.frontierSemantics.horizon profile)

/-- Primitive event-batch trace distribution induced by a product mixed-pure
frontier profile through the canonical Kuhn behavioral realization. -/
noncomputable def mixedPureFrontierEventBatchTraceKernel
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.MixedPureFrontierProfile) :
    PMF
      ((ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).EventBatchTrace) :=
  behavioralFrontierEventBatchTraceKernel program
    (program.mixedPureToBehavioralFrontierProfile profile)

/-- The canonical behavioral frontier primitive-trace kernel has the same
joint utility distribution as the checked behavioral frontier game. -/
theorem behavioralFrontierEventBatchTraceKernel_udist
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    (behavioralFrontierEventBatchTraceKernel program profile).bind
        (fun trace =>
          PMF.pure
            (Machine.eventBatchTraceUtility
              (ToEventGraph.PrimitiveMachine
                (ToEventGraph.compile program.core))
              (fun _ => 0) trace)) =
      program.behavioralFrontierGame.udist profile := by
  classical
  let M :=
    ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core)
  let semantics := program.frontierSemantics
  change
    (PMF.map
        ((semantics.behavioral.view).boundedHistoryTrace
          semantics.horizon)
        (semantics.behavioralHistoryKernel profile)).bind
      (fun trace =>
        PMF.pure (Machine.eventBatchTraceUtility M (fun _ => 0) trace)) =
      program.behavioralFrontierGame.udist profile
  rw [PMF.bind_map]
  change
    (semantics.behavioralHistoryKernel profile).bind
      (fun history : semantics.BehavioralHistory =>
        PMF.pure
          (Machine.eventBatchTraceUtility M (fun _ => 0)
            ((semantics.behavioral.view).boundedHistoryTrace
              semantics.horizon history))) =
      program.behavioralFrontierGame.udist profile
  change
    PMF.map semantics.behavioralHistoryUtility
        (semantics.behavioralHistoryKernel profile) =
      program.behavioralFrontierGame.udist profile
  change semantics.behavioralHistoryKernelGame.udist profile =
      program.behavioralFrontierGame.udist profile
  exact semantics.behavioralHistoryKernelGame_udist profile

/-- The pure frontier primitive-trace kernel has the same joint utility
distribution as the checked pure frontier game. -/
theorem pureFrontierEventBatchTraceKernel_udist
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    (pureFrontierEventBatchTraceKernel program profile).bind
        (fun trace =>
          PMF.pure
            (Machine.eventBatchTraceUtility
              (ToEventGraph.PrimitiveMachine
                (ToEventGraph.compile program.core))
              (fun _ => 0) trace)) =
      program.pureFrontierGame.udist profile := by
  simpa [pureFrontierEventBatchTraceKernel] using
    (behavioralFrontierEventBatchTraceKernel_udist program
        ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
          program.frontierSemantics.horizon profile)).trans
      (program.pureToBehavioralFrontierUdist profile)

/-- The product mixed-pure frontier primitive-trace kernel has the same joint
utility distribution as the checked product mixed-pure frontier game. -/
theorem mixedPureFrontierEventBatchTraceKernel_udist
    (program : WFProgram Player L) [FiniteDomains program]
    (profile : program.MixedPureFrontierProfile) :
    (mixedPureFrontierEventBatchTraceKernel program profile).bind
        (fun trace =>
          PMF.pure
            (Machine.eventBatchTraceUtility
              (ToEventGraph.PrimitiveMachine
                (ToEventGraph.compile program.core))
              (fun _ => 0) trace)) =
      program.mixedPureFrontierGame.udist profile := by
  have hbehavioral :
      program.behavioralFrontierGame.udist
          (program.mixedPureToBehavioralFrontierProfile profile) =
        program.mixedPureFrontierGame.udist profile := by
    change
      (program.behavioralFrontierGame.outcomeKernel
          (program.mixedPureToBehavioralFrontierProfile profile)).bind
          (fun outcome =>
            PMF.pure
              (program.behavioralFrontierGame.utility outcome)) =
        (program.mixedPureFrontierGame.outcomeKernel profile).bind
          (fun outcome =>
            PMF.pure
              (program.mixedPureFrontierGame.utility outcome))
    rw [program.mixedPureToBehavioralFrontierProfile_outcomeKernel profile]
    rfl
  simpa [mixedPureFrontierEventBatchTraceKernel] using
    (behavioralFrontierEventBatchTraceKernel_udist program
        (program.mixedPureToBehavioralFrontierProfile profile)).trans
      hbehavioral

/-- Behavioral frontier play as a primitive-trace game surface. -/
noncomputable def behavioralFrontierTraceSurface
    (program : WFProgram Player L) [FiniteDomains program] :
    TraceGameSurface program where
  game := program.behavioralFrontierGame
  traceKernel := behavioralFrontierEventBatchTraceKernel program
  traceKernel_udist := behavioralFrontierEventBatchTraceKernel_udist program

/-- Pure frontier play as a primitive-trace game surface. -/
noncomputable def pureFrontierTraceSurface
    (program : WFProgram Player L) [FiniteDomains program] :
    TraceGameSurface program where
  game := program.pureFrontierGame
  traceKernel := pureFrontierEventBatchTraceKernel program
  traceKernel_udist := pureFrontierEventBatchTraceKernel_udist program

/-- Product mixed-pure frontier play as a primitive-trace game surface. -/
noncomputable def mixedPureFrontierTraceSurface
    (program : WFProgram Player L) [FiniteDomains program] :
    TraceGameSurface program where
  game := program.mixedPureFrontierGame
  traceKernel := mixedPureFrontierEventBatchTraceKernel program
  traceKernel_udist := mixedPureFrontierEventBatchTraceKernel_udist program

/-- A specification-side event-batch law family whose primitive trace
distribution realizes a trace game surface. -/
structure TraceSpecEventBatchLaw
    (program : WFProgram Player L) [FiniteDomains program]
    (surface : TraceGameSurface program) where
  specLaw :
    (∀ player, surface.game.Strategy player) →
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).EventBatchLaw
  legal :
    ∀ profile,
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).IsLegalEventBatchLaw
        (specLaw profile)
  trace_eq :
    ∀ profile,
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).eventBatchTraceDist
        (specLaw profile) program.frontierSemantics.horizon =
        surface.traceKernel profile

namespace TraceSpecEventBatchLaw

variable {program : WFProgram Player L} [FiniteDomains program]
variable {surface : TraceGameSurface program}

/-- Forget a trace-adequate spec law to the generic profile-indexed law family
used by machine refinement. -/
noncomputable def toFamily
    (law : TraceSpecEventBatchLaw program surface) :
    (ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core)).EventBatchLawFamily
      surface.game.Strategy where
  law := law.specLaw
  legal := law.legal

/-- Primitive trace game induced by a trace-adequate frontier law. -/
noncomputable def traceGame
    (law : TraceSpecEventBatchLaw program surface) :
    GameTheory.KernelGame Player :=
  Machine.eventBatchTraceKernelGame
    (ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core))
    surface.game.Strategy law.toFamily (fun _ => 0)
    program.frontierSemantics.horizon

/-- The explicit spec law has the same joint utility distribution as its
frontier surface. -/
theorem traceGame_udist_surface
    (law : TraceSpecEventBatchLaw program surface)
    (profile : ∀ player, surface.game.Strategy player) :
    law.traceGame.udist profile =
      surface.game.udist profile := by
  change
    ((ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).eventBatchTraceDist
        (law.specLaw profile) program.frontierSemantics.horizon).bind
      (fun trace =>
        PMF.pure
          (Machine.eventBatchTraceUtility
            (ToEventGraph.PrimitiveMachine
              (ToEventGraph.compile program.core))
            (fun _ => 0) trace)) =
      surface.game.udist profile
  rw [law.trace_eq profile]
  exact surface.traceKernel_udist profile

end TraceSpecEventBatchLaw

/-- A runtime refinement plus trace-adequate specification and implementation
law families for one trace game surface.

The refinement itself only relates primitive machines.  The trace game surface
and spec law witness provide the game-facing obligation: running the
specification primitive machine under that law realizes the surface game.
Runtime backends then prove only compatibility of their
implementation law with this spec law. -/
structure RuntimeTraceAdequacy
    (program : WFProgram Player L) [FiniteDomains program]
    (surface : TraceGameSurface program)
    {Impl : Machine Player}
    (R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))) where
  spec : TraceSpecEventBatchLaw program surface
  impl : Impl.EventBatchLawFamily surface.game.Strategy
  compatible :
    ∀ profile,
      R.EventBatchLawCompatible
        (impl.law profile) (spec.specLaw profile)

namespace RuntimeTraceAdequacy

variable {program : WFProgram Player L} [FiniteDomains program]
variable {surface : TraceGameSurface program}
variable {Impl : Machine Player}
variable {R :
    Machine.StochasticRefinement Impl
    (ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core))}

/-- Identity runtime adequacy for a trace-adequate primitive specification
law. This is the canonical smoke-test bridge: no runtime behavior is added,
so compatibility is reflexive event-batch-law compatibility. -/
noncomputable def identity
    (law : TraceSpecEventBatchLaw program surface) :
    RuntimeTraceAdequacy program surface
      (Machine.StochasticRefinement.refl (PrimitiveSpecMachine program)) where
  spec := law
  impl := law.toFamily
  compatible := by
    intro profile
    exact
      Machine.StochasticRefinement.refl_eventBatchLawCompatible
        (PrimitiveSpecMachine program) (law.specLaw profile)

/-- Audited runtime adequacy for any trace-adequate primitive specification
law. The implementation runtime executes one administrative audit tick before
each specification event batch, and the audited refinement erases those ticks. -/
noncomputable def audited
    (law : TraceSpecEventBatchLaw program surface) :
    RuntimeTraceAdequacy program surface
      (Machine.audited.refinement (PrimitiveSpecMachine program)) where
  spec := law
  impl :=
    (Machine.audited.liftEventBatchLawFamily
      (PrimitiveSpecMachine program) law.toFamily).impl
  compatible := by
    intro profile
    exact
      (Machine.audited.liftEventBatchLawFamily
        (PrimitiveSpecMachine program) law.toFamily).compatible profile

/-- Codec runtime adequacy for any trace-adequate primitive specification law.
The implementation runtime stores the primitive graph store through a
`ValueCodec` wire store and erases that wire layer by refinement. -/
noncomputable def codec
    (valueCodec : Runtime.ValueCodec L)
    (law : TraceSpecEventBatchLaw program surface) :
    RuntimeTraceAdequacy program surface
      (Runtime.ValueCodec.refinement valueCodec
        (ToEventGraph.primitiveMachineSpec
          (ToEventGraph.compile program.core))) where
  spec := law
  impl :=
    (Runtime.ValueCodec.liftEventBatchLawFamily valueCodec
      (ToEventGraph.primitiveMachineSpec
        (ToEventGraph.compile program.core)) law.toFamily).impl
  compatible := by
    intro profile
    exact
      (Runtime.ValueCodec.liftEventBatchLawFamily valueCodec
        (ToEventGraph.primitiveMachineSpec
          (ToEventGraph.compile program.core)) law.toFamily).compatible
        profile

/-- Message-in-flight runtime adequacy for any trace-adequate primitive
specification law. The implementation drains pending messages before each
projected primitive event batch, so sends/deliveries are erased by refinement
without changing the source trace law. -/
noncomputable def messageInFlight
    (Message : Player → Type)
    (law : TraceSpecEventBatchLaw program surface) :
    RuntimeTraceAdequacy program surface
      (Machine.messageInFlight.refinement (PrimitiveSpecMachine program)
        Message) where
  spec := law
  impl :=
    (Machine.messageInFlight.liftEventBatchLawFamily
      (PrimitiveSpecMachine program) Message law.toFamily).impl
  compatible := by
    intro profile
    exact
      (Machine.messageInFlight.liftEventBatchLawFamily
        (PrimitiveSpecMachine program) Message law.toFamily).compatible
        profile

/-- Generic refinement lift induced by the bridge's explicit spec and
implementation law families. -/
noncomputable def lift
    (bridge : RuntimeTraceAdequacy program surface R) :
    R.EventBatchLawFamilyLift surface.game.Strategy bridge.spec.toFamily where
  impl := bridge.impl
  compatible := bridge.compatible

variable {Mid Low : Machine Player}
variable {Rmid :
    Machine.StochasticRefinement Mid
    (ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core))}
variable {Rlow : Machine.StochasticRefinement Low Mid}

/-- The composed law-family lift induced by lowering a runtime bridge through
one more implementation layer. -/
noncomputable def lowerLift
    (bridge : RuntimeTraceAdequacy program surface Rmid)
    (lower :
      Rlow.EventBatchLawFamilyLift surface.game.Strategy bridge.impl) :
    (Rmid.compose Rlow).EventBatchLawFamilyLift surface.game.Strategy
      bridge.spec.toFamily :=
  Machine.StochasticRefinement.EventBatchLawFamilyLift.compose
    bridge.lift lower

/-- Lower an existing runtime adequacy bridge through one more implementation
layer. This is the tower-composition operation for runtime trace adequacy:
the lower law family implements the bridge's current implementation law
family, and refinement composition collapses both implementation layers back
to the same primitive specification machine. -/
noncomputable def lowerImpl
    (bridge : RuntimeTraceAdequacy program surface Rmid)
    (lower :
      Rlow.EventBatchLawFamilyLift surface.game.Strategy bridge.impl) :
    RuntimeTraceAdequacy program surface (Rmid.compose Rlow) where
  spec := bridge.spec
  impl := (lowerLift bridge lower).impl
  compatible := (lowerLift bridge lower).compatible

@[simp] theorem lowerLift_impl
    (bridge : RuntimeTraceAdequacy program surface Rmid)
    (lower :
      Rlow.EventBatchLawFamilyLift surface.game.Strategy bridge.impl) :
    (lowerLift bridge lower).impl = lower.impl :=
  rfl

@[simp] theorem lowerImpl_impl
    (bridge : RuntimeTraceAdequacy program surface Rmid)
    (lower :
      Rlow.EventBatchLawFamilyLift surface.game.Strategy bridge.impl) :
    (lowerImpl bridge lower).impl = lower.impl :=
  rfl

/-- Compose the codec runtime rung with a message-in-flight layer below it.
This is the reusable two-rung backend shape: typed primitive machine, wire-store
codec machine, then a pending-message runtime wrapper. -/
noncomputable def codecMessageInFlight
    (valueCodec : Runtime.ValueCodec L)
    (Message : Player → Type)
    (law : TraceSpecEventBatchLaw program surface) :
    RuntimeTraceAdequacy program surface
      ((Runtime.ValueCodec.refinement valueCodec
        (ToEventGraph.primitiveMachineSpec
          (ToEventGraph.compile program.core))).compose
        (Machine.messageInFlight.refinement
          (valueCodec.codecMachine
            (ToEventGraph.primitiveMachineSpec
              (ToEventGraph.compile program.core))) Message)) :=
  (RuntimeTraceAdequacy.codec valueCodec law).lowerImpl
    (Machine.messageInFlight.liftEventBatchLawFamily
      (valueCodec.codecMachine
        (ToEventGraph.primitiveMachineSpec
          (ToEventGraph.compile program.core))) Message
      (RuntimeTraceAdequacy.codec valueCodec law).impl)

/-- Specification primitive trace game realized by the strategy law family. -/
noncomputable def specTraceGame
    (bridge : RuntimeTraceAdequacy program surface R) :
    GameTheory.KernelGame Player :=
  bridge.spec.traceGame

/-- Implementation primitive trace game realized by the lifted runtime law
family. -/
noncomputable def implTraceGame
    (bridge : RuntimeTraceAdequacy program surface R) :
    GameTheory.KernelGame Player :=
  Machine.eventBatchTraceKernelGame
    Impl surface.game.Strategy bridge.lift.impl
    (fun _ => 0) program.frontierSemantics.horizon

/-- The implementation trace game has the same joint utility distribution as
the surface game. -/
theorem implTraceGame_udist_surface
    (bridge : RuntimeTraceAdequacy program surface R)
    (profile : ∀ player, surface.game.Strategy player) :
    bridge.implTraceGame.udist profile =
      surface.game.udist profile := by
  have hproject :=
    (R.eventBatchTraceMorphism
      bridge.lift (fun _ => 0)
      program.frontierSemantics.horizon).udist_preserved profile
  exact
    hproject.symm.trans
      (bridge.spec.traceGame_udist_surface profile)

/-- The implementation trace game and the frontier surface share the same
profile type by construction (both are indexed by `surface.game.Strategy`), so
`implTraceGame_udist_surface` is exactly the identity-`stratMap` case of a
`KernelGame.Morphism`. This is the reusable handle for the generic
`GameTheory.KernelGame` morphism corollaries (expected-utility and Nash
transport) instead of re-deriving them by hand. -/
noncomputable def implTraceGame_morphism_surface
    (bridge : RuntimeTraceAdequacy program surface R) :
    GameTheory.KernelGame.Morphism surface.game bridge.implTraceGame where
  stratMap := fun _ => id
  udist_preserved := bridge.implTraceGame_udist_surface

/-- The reverse-direction identity morphism, used for the direction of Nash
invariance that pulls a surface Nash profile back from the implementation
trace game. -/
noncomputable def surface_morphism_implTraceGame
    (bridge : RuntimeTraceAdequacy program surface R) :
    GameTheory.KernelGame.Morphism bridge.implTraceGame surface.game where
  stratMap := fun _ => id
  udist_preserved := fun profile => (bridge.implTraceGame_udist_surface profile).symm

/-- Runtime trace adequacy identifies the implementation trace game and its
frontier surface up to utility-distribution game isomorphism. -/
noncomputable def implTraceGame_bisimulation_surface
    (bridge : RuntimeTraceAdequacy program surface R) :
    GameTheory.KernelGame.Bisimulation bridge.implTraceGame surface.game where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := fun profile =>
    (bridge.implTraceGame_udist_surface profile).symm

/-- Expected-utility game isomorphism induced by runtime trace adequacy. -/
noncomputable def implTraceGame_equivalence_surface
    (bridge : RuntimeTraceAdequacy program surface R) :
    GameTheory.KernelGame.EUGameIsomorphism
      bridge.implTraceGame surface.game where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := fun profile =>
    (bridge.implTraceGame_udist_surface profile).symm
  eu_preserved :=
    bridge.surface_morphism_implTraceGame.toEUMorphism.eu_preserved

/-- Runtime trace adequacy induces a standard one-way strategic refinement:
surface-game profiles realize implementation trace-game profiles with the same
payoff-vector law, and every implementation unilateral deviation is matched by
the identical surface unilateral deviation. -/
noncomputable def implTraceGame_nashDeviationSimulation
    (bridge : RuntimeTraceAdequacy program surface R) :
    GameTheory.KernelGame.NashDeviationSimulation
      surface.game bridge.implTraceGame (GameTheory.Payoff Player) where
  viewG := { observe := fun _ => surface.game.utility }
  viewH := { observe := fun _ => bridge.implTraceGame.utility }
  rel := fun surfaceProfile implProfile =>
    surfaceProfile = implProfile
  law_eq := by
    intro surfaceProfile implProfile hrel _
    subst implProfile
    change surface.game.udist surfaceProfile =
      bridge.implTraceGame.udist surfaceProfile
    exact (bridge.implTraceGame_udist_surface surfaceProfile).symm
  simulate_target_deviation := by
    intro surfaceProfile implProfile hrel player implAlternative
    subst implProfile
    refine ⟨implAlternative, ?_⟩
    change surface.game.udist
        (Function.update surfaceProfile player implAlternative) =
      bridge.implTraceGame.udist
        (Function.update surfaceProfile player implAlternative)
    exact
      (bridge.implTraceGame_udist_surface
        (Function.update surfaceProfile player implAlternative)).symm

/-- Preference-parametric Nash transport induced by runtime trace adequacy.
This is the strategic-refinement form of runtime preservation; expected-utility
Nash corollaries add boundedness assumptions separately. -/
theorem implTraceGame_nashFor_of_surface_nashFor
    (bridge : RuntimeTraceAdequacy program surface R)
    {prefΩ :
      Player → PMF (GameTheory.Payoff Player) →
        PMF (GameTheory.Payoff Player) → Prop}
    {profile : ∀ player, surface.game.Strategy player}
    (hNash :
      surface.game.IsNashFor
        (GameTheory.GameForm.observedPref
          bridge.implTraceGame_nashDeviationSimulation.viewG prefΩ)
        profile) :
    bridge.implTraceGame.IsNashFor
        (GameTheory.GameForm.observedPref
          bridge.implTraceGame_nashDeviationSimulation.viewH prefΩ)
        profile :=
  bridge.implTraceGame_nashDeviationSimulation
    |>.target_nash_of_source_nash rfl hNash

/-- Trace adequacy preserves the payoff-vector law induced by any correlated
distribution over the shared strategy-profile space. -/
theorem implTraceGame_correlatedUtilityLaw_surface
    (bridge : RuntimeTraceAdequacy program surface R)
    (profileLaw : PMF surface.game.Profile) :
    correlatedUtilityLaw bridge.implTraceGame profileLaw =
      correlatedUtilityLaw surface.game profileLaw := by
  unfold correlatedUtilityLaw
  exact
    Math.ProbabilityMassFunction.bind_congr_on_support
      profileLaw bridge.implTraceGame.udist surface.game.udist
      (fun profile _ => bridge.implTraceGame_udist_surface profile)

/-- Expected utilities agree between a trace-adequate implementation law and
the frontier surface under bounded-utility hypotheses. -/
theorem implTraceGame_eu_surface_of_bounded
    (bridge : RuntimeTraceAdequacy program surface R)
    {CImpl CFrontier : Player → ℝ}
    (hbdImpl :
      ∀ player trace,
        |Machine.eventBatchTraceUtility Impl (fun _ => 0) trace player| ≤
          CImpl player)
    (hbdFrontier :
      ∀ player outcome,
        |surface.game.utility outcome player| ≤ CFrontier player)
    (profile : ∀ player, surface.game.Strategy player) (player : Player) :
    bridge.implTraceGame.eu profile player =
      surface.game.eu profile player :=
  bridge.implTraceGame_morphism_surface.eu_preserved_of_bounded
    (fun who ω => hbdFrontier who ω) (fun who ω => hbdImpl who ω) profile player

/-- Correlated expected utilities agree between a trace-adequate implementation
law and the frontier surface under bounded-utility hypotheses. -/
theorem implTraceGame_correlatedEu_surface_of_bounded
    (bridge : RuntimeTraceAdequacy program surface R)
    {CImpl CFrontier : Player → ℝ}
    (hbdImpl :
      ∀ player trace,
        |Machine.eventBatchTraceUtility Impl (fun _ => 0) trace player| ≤
          CImpl player)
    (hbdFrontier :
      ∀ player outcome,
        |surface.game.utility outcome player| ≤ CFrontier player)
    (profileLaw : PMF surface.game.Profile) (player : Player) :
    bridge.implTraceGame.correlatedEu profileLaw player =
      surface.game.correlatedEu profileLaw player := by
  rw [bridge.implTraceGame.correlatedEu_eq_expect_eu_of_bounded
    profileLaw player (hbdImpl player)]
  rw [surface.game.correlatedEu_eq_expect_eu_of_bounded
    profileLaw player (hbdFrontier player)]
  exact
    Math.ProbabilityMassFunction.expect_congr_on_support
      profileLaw
      (fun profile => bridge.implTraceGame.eu profile player)
      (fun profile => surface.game.eu profile player)
      (fun profile _ =>
        bridge.implTraceGame_eu_surface_of_bounded
          hbdImpl hbdFrontier profile player)

/-- Correlated-equilibrium status is invariant between a trace-adequate
implementation trace game and its frontier surface. -/
theorem implTraceGame_correlatedEq_iff_surface_correlatedEq
    (bridge : RuntimeTraceAdequacy program surface R)
    (profileLaw : PMF surface.game.Profile) :
    bridge.implTraceGame.IsCorrelatedEq profileLaw ↔
      surface.game.IsCorrelatedEq profileLaw := by
  let equivalence := bridge.implTraceGame_equivalence_surface
  have hrealize : equivalence.realize profileLaw = profileLaw := by
    unfold GameTheory.KernelGame.EUGameIsomorphism.realize
    change PMF.map (fun profile => profile) profileLaw = profileLaw
    exact PMF.map_id profileLaw
  simpa only [hrealize] using equivalence.correlatedEq_iff profileLaw

/-- Coarse-correlated-equilibrium status is invariant between a trace-adequate
implementation trace game and its frontier surface. -/
theorem implTraceGame_coarseCorrelatedEq_iff_surface_coarseCorrelatedEq
    (bridge : RuntimeTraceAdequacy program surface R)
    (profileLaw : PMF surface.game.Profile) :
    bridge.implTraceGame.IsCoarseCorrelatedEq profileLaw ↔
      surface.game.IsCoarseCorrelatedEq profileLaw := by
  let equivalence := bridge.implTraceGame_equivalence_surface
  have hrealize : equivalence.realize profileLaw = profileLaw := by
    unfold GameTheory.KernelGame.EUGameIsomorphism.realize
    change PMF.map (fun profile => profile) profileLaw = profileLaw
    exact PMF.map_id profileLaw
  simpa only [hrealize] using equivalence.coarseCorrelatedEq_iff profileLaw

/-- Nash status is invariant between a trace-adequate implementation trace game
and its frontier surface. -/
theorem implTraceGame_nash_iff_surface_nash
    (bridge : RuntimeTraceAdequacy program surface R)
    (profile : ∀ player, surface.game.Strategy player) :
    bridge.implTraceGame.IsNash profile ↔ surface.game.IsNash profile := by
  let equivalence := bridge.implTraceGame_equivalence_surface
  have hprofile : equivalence.profileEquiv profile = profile := by
    funext player
    rfl
  simpa only [hprofile] using equivalence.nash_iff profile

/-- The whole Nash equilibrium set is invariant between a trace-adequate
implementation trace game and its frontier surface. -/
theorem implTraceGame_nashSet_eq_surface_nashSet
    (bridge : RuntimeTraceAdequacy program surface R) :
    {profile : surface.game.Profile |
      bridge.implTraceGame.IsNash profile} =
    {profile : surface.game.Profile |
      surface.game.IsNash profile} := by
  ext profile
  exact bridge.implTraceGame_nash_iff_surface_nash profile

/-- Expected utilities agree between a trace-adequate specification law and
the frontier surface under bounded-utility hypotheses. -/
theorem specTraceGame_eu_surface_of_bounded
    (bridge : RuntimeTraceAdequacy program surface R)
    {CSpec CFrontier : Player → ℝ}
    (hbdSpec :
      ∀ player trace,
        |Machine.eventBatchTraceUtility
            (ToEventGraph.PrimitiveMachine
              (ToEventGraph.compile program.core))
            (fun _ => 0) trace player| ≤ CSpec player)
    (hbdFrontier :
      ∀ player outcome,
        |surface.game.utility outcome player| ≤ CFrontier player)
    (profile : ∀ player, surface.game.Strategy player) (player : Player) :
    bridge.specTraceGame.eu profile player =
      surface.game.eu profile player := by
  calc
    bridge.specTraceGame.eu profile player =
        Math.Probability.expect
          (bridge.specTraceGame.udist profile) (fun payoff => payoff player) := by
          exact
            (bridge.specTraceGame.expect_udist_eq_eu_of_bounded
              profile player (hbdSpec player)).symm
    _ =
        Math.Probability.expect
          (surface.game.udist profile)
          (fun payoff => payoff player) := by
          change
            Math.Probability.expect
              (bridge.spec.traceGame.udist profile)
              (fun payoff => payoff player) =
            Math.Probability.expect
              (surface.game.udist profile)
              (fun payoff => payoff player)
          rw [bridge.spec.traceGame_udist_surface profile]
    _ = surface.game.eu profile player := by
          exact
            surface.game.expect_udist_eq_eu_of_bounded
              profile player (hbdFrontier player)

/-- Specification trace games adequate for a trace game surface inherit that
surface game's Nash equilibria. -/
theorem specTraceGame_nash_of_surface_nash
    (bridge : RuntimeTraceAdequacy program surface R)
    {CSpec CFrontier : Player → ℝ}
    (hbdSpec :
      ∀ player trace,
        |Machine.eventBatchTraceUtility
            (ToEventGraph.PrimitiveMachine
              (ToEventGraph.compile program.core))
            (fun _ => 0) trace player| ≤ CSpec player)
    (hbdFrontier :
      ∀ player outcome,
        |surface.game.utility outcome player| ≤ CFrontier player)
    {profile : ∀ player, surface.game.Strategy player}
    (hNash : surface.game.IsNash profile) :
    bridge.specTraceGame.IsNash profile := by
  intro player alternative
  have hfrontier := hNash player alternative
  calc
    bridge.specTraceGame.eu profile player =
        surface.game.eu profile player :=
      bridge.specTraceGame_eu_surface_of_bounded
        hbdSpec hbdFrontier profile player
    _ ≥ surface.game.eu
          (Function.update profile player alternative) player :=
      hfrontier
    _ = bridge.specTraceGame.eu
          (Function.update profile player alternative) player :=
      (bridge.specTraceGame_eu_surface_of_bounded
        hbdSpec hbdFrontier
        (Function.update profile player alternative) player).symm

/-- A runtime refinement whose strategy-indexed laws adequately realize a trace
game surface gives every surface Nash profile to the implementation trace
game. -/
theorem implTraceGame_nash_of_surface_nash
    (bridge : RuntimeTraceAdequacy program surface R)
    {profile : ∀ player, surface.game.Strategy player}
    (hNash : surface.game.IsNash profile) :
    bridge.implTraceGame.IsNash profile :=
  (bridge.implTraceGame_nash_iff_surface_nash profile).mpr hNash

/-- A surface Nash-existence witness yields an implementation trace-game Nash
existence witness. -/
theorem implTraceGame_nash_exists
    (bridge : RuntimeTraceAdequacy program surface R)
    (hexists : ∃ profile, surface.game.IsNash profile) :
    ∃ profile, bridge.implTraceGame.IsNash profile := by
  rcases hexists with ⟨profile, hNash⟩
  exact ⟨profile, bridge.implTraceGame_nash_of_surface_nash hNash⟩

/-- A surface correlated-equilibrium witness yields an implementation
trace-game correlated-equilibrium witness. -/
theorem implTraceGame_correlatedEq_exists
    (bridge : RuntimeTraceAdequacy program surface R)
    (hexists :
      ∃ profileLaw : PMF surface.game.Profile,
        surface.game.IsCorrelatedEq profileLaw) :
    ∃ profileLaw : PMF surface.game.Profile,
      bridge.implTraceGame.IsCorrelatedEq profileLaw := by
  rcases hexists with ⟨profileLaw, hCorrelated⟩
  exact
    ⟨profileLaw,
      (bridge.implTraceGame_correlatedEq_iff_surface_correlatedEq
        profileLaw).mpr hCorrelated⟩

/-- A surface coarse-correlated-equilibrium witness yields an implementation
trace-game coarse-correlated-equilibrium witness. -/
theorem implTraceGame_coarseCorrelatedEq_exists
    (bridge : RuntimeTraceAdequacy program surface R)
    (hexists :
      ∃ profileLaw : PMF surface.game.Profile,
        surface.game.IsCoarseCorrelatedEq profileLaw) :
    ∃ profileLaw : PMF surface.game.Profile,
      bridge.implTraceGame.IsCoarseCorrelatedEq profileLaw := by
  rcases hexists with ⟨profileLaw, hCorrelated⟩
  exact
    ⟨profileLaw,
      (bridge.implTraceGame_coarseCorrelatedEq_iff_surface_coarseCorrelatedEq
        profileLaw).mpr hCorrelated⟩

end RuntimeTraceAdequacy

end Strategic

end WFProgram

end Vegas
