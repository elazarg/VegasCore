/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.QualifiedBinding.AnnotationMass
import Vegas.Game.SourceSwapPairs
import Vegas.Compile.CommitPrefixAdmittedAction

/-! # Literal native likelihood and selected source Nature mass -/

noncomputable section

namespace Vegas.PhaseProposalQualifiedBinding

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (values : ∀ who (key : setup.ProposalRecoveryComponent who),
    PMF (setup.CommitRecoveryValueChoice who key.1))

open scoped ENNReal

attribute [local implicit_reducible] InformationModel.InformationSite

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  nativeMenu nativeInitial implementation.horizon implementation.scheduler

/-- The actual trace's behavioral atoms and its transition mass form the
literal finite-history likelihood, before any source-coordinate partition. -/
private theorem sourceReplay_native_history_factor
    (profile : ∀ owner, ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).BehavioralPolicy owner)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight profile ⟨state, trace⟩).toReal =
      trace.transitionMass *
        ∏ owner, ((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).ownPlayReachProbability (profile owner)
            (((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).ownPlay owner trace) := by
  let model := (nativeMenu).information nativeInitial implementation.horizon
    implementation.scheduler
  obtain ⟨records, recordsEq, _provenance, chance, _nonnegative, mass, factor⟩ :=
    model.exists_continuation_ownPlay_factor
      (Trace.start : (nativeProtocol).Trace (nativeProtocol).init) trace
        (TracePrefix.start trace)
  have chanceEq : chance = trace.transitionMass := by
    simpa only [Trace.transitionMass_start, mul_one] using mass
  have recordsActual (owner : Player) : records owner = model.ownPlay owner trace := by
    simpa only [InfoSignals.ownPlay, List.append_nil] using (recordsEq owner).symm
  have exactFactor := factor profile
  simp only [Trace.length, Nat.sub_zero, chanceEq, recordsActual] at exactFactor
  exact exactFactor

/-- One actual command disintegrates against the posterior of the original
whole tape, including at zero command atoms. -/
private theorem sourceReplay_scheduler_density
    (past : List (nativeApplication).EnvironmentEntry)
    (view : (nativeApplication).EnvironmentView) (command : (nativeApplication).Command)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    implementation.scheduler past view command *
        ((nativeApplication).schedulerMixture implementation.prior
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime))).posterior
              (past ++ [⟨view, command⟩]) tape =
      ((nativeApplication).schedulerMixture implementation.prior
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime))).posterior past tape *
        ReservedEpoch.family implementation.runtime implementation.leaks
          (ReservedEpoch.packetCapacity implementation.runtime) tape past view command := by
  let mixture := (nativeApplication).schedulerMixture implementation.prior
    (ReservedEpoch.family implementation.runtime implementation.leaks
      (ReservedEpoch.packetCapacity implementation.runtime))
  let joint := (mixture.posterior past).bind fun selected =>
    mixture.respond selected (past, view)
  have marginal : joint.map Prod.fst = implementation.scheduler past view := rfl
  have density := mul_fiberPosterior_map_snd_apply joint command tape
  rw [marginal] at density
  have atom : joint (command, tape) = mixture.posterior past tape *
      ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape past view command := by
    exact bind_map_tag_apply (mixture.posterior past)
      (fun selected => ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) selected past view) command tape
  change implementation.scheduler past view command *
      mixture.posterior (past ++ [⟨view, command⟩]) tape = _
  rw [ReactiveApplication.SchedulerImplementation.posterior_snoc]
  exact density.trans atom

/-- Evaluate the existing transition kernel on the actual recorded path with
the original whole tape fixed. No new trace or support totalization is used. -/
private def sourceReplayFixedTransitionMass
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    ∀ {state : (nativeProtocol).State}, (nativeProtocol).Trace state → ℝ
  | _, .start => 1
  | after, @Trace.extend _ _ before _ prior joint _ _ =>
      sourceReplayFixedTransitionMass tape prior *
        ((nativeApplication).transition nativeInitial implementation.horizon
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime) tape) before joint after).toReal

private theorem sourceReplay_tape_step_density
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {before after : (nativeProtocol).State} (prior : (nativeProtocol).Trace before)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support) :
    ((nativeProtocol).step before ⟨joint, legal⟩) after *
        prefixTapeLaw setup implementation ⟨after, prior.extend joint legal moved⟩ tape =
      prefixTapeLaw setup implementation ⟨before, prior⟩ tape *
        (nativeApplication).transition nativeInitial implementation.horizon
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime) tape) before joint after := by
  cases before with
  | none =>
    change after ∈ ((nativeInitial).map fun state =>
      some (⟨implementation.horizon, none,
        ReactiveApplication.Execution.initial nativeApplication state⟩ :
          (nativeApplication).Control)).support at moved
    obtain ⟨state, _supported, rfl⟩ := PMF.support_map .. ▸ moved
    change _ * implementation.prior tape = implementation.prior tape * _
    exact mul_comm _ _
  | some control =>
    rcases control with ⟨remaining, actor, execution⟩
    cases actor with
    | some owner =>
      change after ∈ (PMF.pure (some (⟨remaining, none,
        execution.respond nativeApplication owner ((joint owner).getD ⟨none⟩)⟩ :
          (nativeApplication).Control))).support at moved
      cases (PMF.mem_support_pure_iff ..).mp moved
      simp only [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.transition,
        PMF.pure_apply, ↓reduceIte, prefixTapeLaw,
        ReactiveApplication.respond_environmentRecall, one_mul, mul_one]
    | none =>
      cases remaining with
      | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
      | succ remaining =>
        change after ∈ ((implementation.scheduler execution.environmentRecall
          (execution.observeEnvironment nativeApplication)).bind fun command =>
            (execution.environmentStep nativeApplication command).map fun next =>
              some (⟨remaining, command.actor? nativeApplication, next⟩ :
                (nativeApplication).Control)).support at moved
        obtain ⟨command, _chosen, supported⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
        obtain ⟨next, advanced, rfl⟩ := PMF.support_map .. ▸ supported
        change (nativeApplication).transition nativeInitial implementation.horizon
          implementation.scheduler (some ⟨remaining + 1, none, execution⟩) joint
            (some ⟨remaining, command.actor? nativeApplication, next⟩) * _ = _
        rw [(nativeApplication).transition_environment_apply nativeInitial
            implementation.horizon implementation.scheduler remaining execution next command
              advanced joint,
          (nativeApplication).transition_environment_apply nativeInitial
            implementation.horizon
              (ReservedEpoch.family implementation.runtime implementation.leaks
                (ReservedEpoch.packetCapacity implementation.runtime) tape) remaining execution
                  next command advanced joint]
        have recorded := (nativeApplication).environmentStep_environmentRecall execution next
          command advanced
        simp only [prefixTapeLaw, recorded]
        have density := sourceReplay_scheduler_density setup implementation
          execution.environmentRecall (execution.observeEnvironment nativeApplication) command tape
        let mixture := (nativeApplication).schedulerMixture implementation.prior
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime))
        calc
          _ = (implementation.scheduler execution.environmentRecall
              (execution.observeEnvironment nativeApplication) command *
                mixture.posterior (execution.environmentRecall ++
                  [⟨execution.observeEnvironment nativeApplication, command⟩]) tape) *
                    (execution.environmentStep nativeApplication command) next := by ac_rfl
          _ = _ := by rw [density]; ac_rfl

/-- The original tape posterior telescopes along the actual trace. All
initializer and public Nature atoms stay in the fixed-tape transition product. -/
private theorem sourceReplay_transition_tape_factor
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    trace.transitionMass * (prefixTapeLaw setup implementation ⟨state, trace⟩ tape).toReal =
      (implementation.prior tape).toReal *
        sourceReplayFixedTransitionMass setup implementation tape trace := by
  induction trace with
  | start =>
    change 1 * (implementation.prior tape).toReal = (implementation.prior tape).toReal * 1
    ring
  | @extend before after prior joint legal moved ih =>
    have density := congrArg ENNReal.toReal
      (sourceReplay_tape_step_density setup implementation tape prior joint legal moved)
    simp only [ENNReal.toReal_mul] at density
    rw [Trace.transitionMass_extend, sourceReplayFixedTransitionMass]
    calc
      _ = prior.transitionMass * _ := by ring
      _ = prior.transitionMass *
          ((prefixTapeLaw setup implementation ⟨before, prior⟩ tape).toReal * _) :=
            congrArg (prior.transitionMass * ·) density
      _ = _ := by rw [← mul_assoc, ih]; ring

/-- Literal native reach with its original whole tape is the fixed-tape
Nature product times every actual own-response product. -/
private theorem sourceReplay_native_tape_factor
    (profile : ∀ owner, ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).BehavioralPolicy owner)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight profile ⟨state, trace⟩).toReal *
          (prefixTapeLaw setup implementation ⟨state, trace⟩ tape).toReal =
      (implementation.prior tape).toReal *
        sourceReplayFixedTransitionMass setup implementation tape trace *
          ∏ owner, ((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).ownPlayReachProbability (profile owner)
              (((nativeMenu).information nativeInitial implementation.horizon
                implementation.scheduler).ownPlay owner trace) := by
  rw [sourceReplay_native_history_factor setup implementation profile trace]
  let own := ∏ owner, ((nativeMenu).information nativeInitial implementation.horizon
    implementation.scheduler).ownPlayReachProbability (profile owner)
      (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlay owner trace)
  change (trace.transitionMass * own) *
    (prefixTapeLaw setup implementation ⟨state, trace⟩ tape).toReal =
      (implementation.prior tape).toReal *
        sourceReplayFixedTransitionMass setup implementation tape trace * own
  calc
    _ = (trace.transitionMass *
        (prefixTapeLaw setup implementation ⟨state, trace⟩ tape).toReal) * own := by ring
    _ = _ := by rw [sourceReplay_transition_tape_factor setup implementation tape trace]

/-- Menu restriction preserves the literal product of reference-response atoms
at every original private input on the actual native trace. -/
private theorem sourceReplay_prescribed_own_atom
    (rates : PhaseProposalRates) (owner : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) :
    ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlayReachProbability
      (phaseProposalReferenceStrategy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan nativeInitial implementation.horizon
          implementation.scheduler values rates owner)
      (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlay owner trace) =
      (((nativeApplication).privateTranscriptFrom [] (control.execution.recall owner)).map
        (fun record => phaseProposalReferencePolicy setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan values rates owner
            record.1.1 record.1.2 record.2)).prod.toReal := by
  have own : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlay owner trace =
      (nativeApplication).recallOwnPlay (control.execution.recall owner) := by
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).ownPlay owner trace = _
    rw [← (nativeMenu).ownPlay_toRawTrace nativeInitial implementation.horizon
      implementation.scheduler owner trace, (nativeApplication).trace_ownPlay]
    rfl
  rw [own]
  exact (nativeMenu).ownPlayFrom_restrictPolicy nativeInitial implementation.horizon
    implementation.scheduler owner
      (phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner)
      (fun past view response supported => phaseProposalReferencePolicy_covered setup .concurrent
        implementation.runtime implementation.leaks implementation.bounds implementation.plan
          values rates owner past view response supported) [] (control.execution.recall owner)

/-- The prescribed native atom retains the whole initial law, original tape,
public Nature and each literal response probability at its actual input. -/
private theorem sourceReplay_prescribed_native_atom
    (rates : PhaseProposalRates)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) :
    (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight
      (phaseProposalReferenceStrategy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan nativeInitial implementation.horizon
          implementation.scheduler values rates) ⟨some control, trace⟩).toReal *
            (prefixTapeLaw setup implementation ⟨some control, trace⟩ tape).toReal =
      (implementation.prior tape).toReal *
        sourceReplayFixedTransitionMass setup implementation tape trace *
          ∏ owner, (((nativeApplication).privateTranscriptFrom []
            (control.execution.recall owner)).map (fun record =>
              phaseProposalReferencePolicy setup .concurrent implementation.runtime
                implementation.leaks implementation.bounds implementation.plan values rates owner
                  record.1.1 record.1.2 record.2)).prod.toReal := by
  rw [sourceReplay_native_tape_factor setup implementation
    (phaseProposalReferenceStrategy setup .concurrent implementation.runtime implementation.leaks
      implementation.bounds implementation.plan nativeInitial implementation.horizon
        implementation.scheduler values rates) tape trace]
  apply congrArg (fun product => (implementation.prior tape).toReal *
    sourceReplayFixedTransitionMass setup implementation tape trace * product)
  exact Finset.prod_congr rfl fun owner _ =>
    sourceReplay_prescribed_own_atom setup values implementation rates owner control trace

/-- At an actual counted input, the physical response atom separates into
its genuine class atom and the literal alias-script atom at that same input. -/
private theorem sourceReplay_counted_response_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L))
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner)) :
    phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner) response.val =
      phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner (execution.recall owner)
            (execution.observe nativeApplication owner)
              (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                implementation.bounds owner (execution.recall owner)
                  (execution.observe nativeApplication owner) response) *
        sourceReplayAliases setup implementation rates.aliases owner execution tag
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) (tag, some response.val) := by
  classical
  unfold phaseProposalReferencePolicy
  rw [pmf_map_apply_of_injective _ Subtype.val_injective response]
  unfold phaseProposalReferenceResponses PhaseProposal.splitResponseLaw
  rw [phaseProposalReferenceClasses_eq_of_counted setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan operational.completePending
      operational.outputValues operational.maximalPhases values fullValues rates waitPositive
        waitBelow slotPositive badPositive badBelow implementation.horizon implementation.scheduler
          remaining owner execution trace]
  rw [sourceReplayAliases_atom setup implementation rates.aliases owner execution tag _ response]
  exact bind_apply_of_unique_branch _ _ response
    (PhaseProposal.projectResponse implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner) response)
    (fun selected _ supported => (PMF.splitKernel_supported _ _ _ _ _ _ selected response
      supported).symm)

/-- A silent or noncommitment packet has no hidden preparation coordinate.
Its genuine class atom is exactly its mechanical packet atom, and its private
syntax contributes the alias atom at the actual counted input. -/
private theorem sourceReplay_noncommit_response_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L))
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (noncommit : ∀ material, response.val.transmission = some material →
      ∀ event handle, material.call.packet ≠ .commitment event handle) :
    phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner)
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) =
      foreignMechanicalAtom setup implementation rates execution owner response.val ∧
    phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner) response.val =
      foreignMechanicalAtom setup implementation rates execution owner response.val *
        sourceReplayAliases setup implementation rates.aliases owner execution tag
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) (tag, some response.val) := by
  classical
  let past := execution.recall owner
  let view := execution.observe nativeApplication owner
  let packet := fun action : (nativeApplication).Action => action.transmission.map
    (fun material => (PhaseCount.localEnvelope implementation.runtime implementation.leaks
      owner past view material).payload)
  let project := PhaseProposal.projectResponse implementation.runtime implementation.leaks
    implementation.bounds owner past view
  let classes := phaseProposalBaseClasses setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan values rates owner past view
  have preparation (action : (nativeApplication).Action)
      (same : packet action = packet response.val) :
      action.transmission.bind PhaseProposal.bindingPreparation = none := by
    cases transmitted : action.transmission with
    | none => simp only [Option.bind_none]
    | some material =>
        cases original : response.val.transmission with
        | none =>
            simp only [packet, transmitted, original, Option.map_some, Option.map_none,
              reduceCtorEq] at same
        | some fixed =>
            have calls := congrArg (fun selected => selected.map
              (fun entry : CommitAttemptPacket (serviceGraph setup .concurrent) =>
                entry.packet.call)) same
            have call : material.call.packet = fixed.call.packet := by
              simpa only [packet, transmitted, original, Option.map_some,
                PhaseCount.localEnvelope, PhaseCount.maskPacket_call, Option.some.injEq]
                using calls
            cases shape : material.call.packet with
            | commitment event handle =>
                exact False.elim (noncommit fixed original event handle (call.symm.trans shape))
            | opening event handle raw =>
                simp only [Option.bind_some, PhaseProposal.bindingPreparation, shape]
            | malformed raw =>
                simp only [Option.bind_some, PhaseProposal.bindingPreparation, shape]
  have unique (selected : PhaseProposal.ResponseClass implementation.runtime
      implementation.leaks implementation.bounds owner past view)
      (same : selected.val.2 = (project response).val.2) : selected = project response := by
    obtain ⟨other, represented⟩ := selected.property
    have packets := same
    rw [← represented] at packets
    change packet other.val = packet response.val at packets
    apply Subtype.ext
    rw [← represented]
    apply Prod.ext
    · exact (preparation other.val packets).trans
        (preparation response.val rfl).symm
    · exact packets
  have classAtom : (classes.map fun selected => selected.val.2) (project response).val.2 =
      classes (project response) := by
    rw [← pmf_bind_pure_eq_map,
      bind_apply_of_unique_branch classes (fun selected => PMF.pure selected.val.2)
        (project response).val.2 (project response)]
    · rw [PMF.pure_apply_self, mul_one]
    · intro selected _ supported
      exact unique selected ((PMF.mem_support_pure_iff ..).mp supported).symm
  have marginal : (classes.map fun selected => selected.val.2) =
      (phaseProposalBasePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner past view).map packet := by
    dsimp only [classes]
    rw [phaseProposalBaseClasses, PMF.map_comp,
      ← phaseProposalBaseResponses_map_val setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan values rates owner
          past view, PMF.map_comp]
    rfl
  have mechanical : foreignMechanicalAtom setup implementation rates execution owner response.val =
      classes (project response) := by
    dsimp only [foreignMechanicalAtom]
    rw [mechanicalForeignPolicy_packet_eq_base setup values implementation, ← marginal]
    change (classes.map fun selected => selected.val.2) (project response).val.2 * _ = _
    rw [classAtom]
    cases transmitted : response.val.transmission with
    | none => simp only [mul_one]
    | some material =>
        cases shape : material.call.packet with
        | commitment event handle => exact (noncommit material transmitted event handle shape).elim
        | opening event handle raw => simp only [shape, mul_one]
        | malformed raw => simp only [shape, mul_one]
  refine ⟨mechanical.symm, ?_⟩
  rw [sourceReplay_counted_response_atom setup values implementation operational fullValues rates
    waitPositive waitBelow slotPositive badPositive badBelow remaining owner execution trace tag
      response, mechanical]

/-- One actual proper foreign response charges its mapped ordinary draw once;
the preparation flag stays inside the mechanical atom and the alias stays at
the actual reconstructed input. -/
private theorem sourceReplay_proper_response_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (key : setup.ProposalRecoveryComponent owner)
    (query : phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
      implementation.plan owner event (execution.recall owner)
        (execution.observe nativeApplication owner) = some key)
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (sent : response.val.transmission = some material)
    (value : L.Val payload)
    (prepared : PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L))
    (serial : Nat) (packet : material.call.packet = .commitment event (owner, .prepared serial))
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L)) :
    phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner) response.val =
      foreignMechanicalAtom setup implementation rates execution owner response.val *
        ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
          owner payload binding choice.val.val)) value *
        sourceReplayAliases setup implementation rates.aliases owner execution tag
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) (tag, some response.val) := by
  unfold phaseProposalReferencePolicy
  rw [pmf_map_apply_of_injective _ Subtype.val_injective response,
    (foreign_binding_response_atom setup values implementation operational fullValues rates
      waitPositive waitBelow slotPositive badPositive badBelow remaining owner execution trace event
        payload binding request key query response material sent value prepared serial packet).2,
    sourceReplayAliases_atom setup implementation rates.aliases owner execution tag _ response]

/-- A proper counted SEND supplies its genuine typed query and its literal
draw atom at that actual input. Neither is an additional ledger premise. -/
private theorem sourceReplay_proper_callback_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (clean : ¬ PhaseProposal.GeneratedUnusableBindingAction implementation.runtime
      implementation.leaks owner response.val)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (sent : response.val.transmission = some material)
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent))
    (packet : material.call.packet = .commitment event handle)
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L)) :
    ∃ (payload : L.Ty)
      (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
      (key : setup.ProposalRecoveryComponent owner) (serial : Nat) (value : L.Val payload),
      handle = (owner, .prepared serial) ∧
      execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩ ∧
      phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
        implementation.plan owner event (execution.recall owner)
          (execution.observe nativeApplication owner) = some key ∧
      PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L) ∧
      phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner (execution.recall owner)
            (execution.observe nativeApplication owner)
            (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner (execution.recall owner)
                (execution.observe nativeApplication owner) response) =
        foreignMechanicalAtom setup implementation rates execution owner response.val *
          ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
            owner payload binding choice.val.val)) value ∧
      phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner (execution.recall owner)
            (execution.observe nativeApplication owner) response.val =
        foreignMechanicalAtom setup implementation rates execution owner response.val *
          ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
            owner payload binding choice.val.val)) value *
          sourceReplayAliases setup implementation rates.aliases owner execution tag
            (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner (execution.recall owner)
                (execution.observe nativeApplication owner) response) (tag, some response.val) := by
  classical
  have action : response.val = (⟨some material⟩ : (nativeApplication).Action) :=
    congrArg (fun selected => (⟨selected⟩ : (nativeApplication).Action)) sent
  have available : (⟨some material⟩ : (nativeApplication).Action) ∈
      PhaseCount.onePacketActions implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) := action ▸ response.property
  have initialEq : (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) = nativeInitial := PMF.map_comp _ _ _
  have counted : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon implementation.scheduler).Trace
          (some ⟨remaining, some owner, execution⟩) := by
    rw [initialEq]
    exact trace
  obtain ⟨coordinate, requested⟩ := PhaseCount.onePacket_request_of_nonsilent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
        remaining owner execution counted material available
  have named := PhaseCount.onePacket_event_of_request implementation.runtime implementation.leaks
    implementation.bounds implementation.plan (serviceGraph_revealRelaxedOrdered setup .concurrent)
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
        remaining owner execution counted coordinate requested material available
  rw [packet] at named
  have eventEq : coordinate.event = event := Option.some.inj named.symm
  have request := requested
  change execution.application.SeedRequest owner ⟨coordinate.attempt, coordinate.event⟩ at request
  rw [requested.1, eventEq] at request
  have permitted : PhaseCount.permits ((nativeApplication).outputs (execution.recall owner))
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (execution.recall owner) (execution.observe nativeApplication owner) material) = true := by
    rcases ((PhaseCount.mem_onePacketActions implementation.runtime implementation.leaks
      implementation.bounds owner _ _ _).mp available).2 with impossible |
        ⟨other, same, permitted⟩
    · cases impossible
    · cases Option.some.inj same
      exact permitted
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  have call : (PhaseCount.nativeMessage (PhaseCount.localEnvelope implementation.runtime
      implementation.leaks owner (execution.recall owner)
        (execution.observe nativeApplication owner) material)).payload.call =
      material.call.packet := PhaseCount.maskPacket_call _ _
  unfold CountCallCorrect at correct
  rw [call, packet] at correct
  obtain ⟨owned, _evidence, handleOwned, ⟨serial, slot⟩, _unused⟩ := correct
  change handle.1 = owner at handleOwned
  have handleEq : handle = (owner, .prepared serial) := Prod.ext handleOwned slot
  have owned' : bindingOwnedBy (serviceGraph setup .concurrent) owner event = true := owned
  obtain ⟨payload, binding⟩ : ∃ payload,
      (serviceGraph setup .concurrent).outputLayout event = .binding owner payload := by
    cases output : (serviceGraph setup .concurrent).outputLayout event with
    | binding actor payload =>
        have same : actor = owner := by
          simpa only [bindingOwnedBy, output, decide_eq_true_eq] using owned'
        subst actor
        exact ⟨payload, rfl⟩
    | publicData payload => simp only [bindingOwnedBy, output, Bool.false_eq_true] at owned'
    | privateInput actor payload =>
        simp only [bindingOwnedBy, output, Bool.false_eq_true] at owned'
    | publication payload => simp only [bindingOwnedBy, output, Bool.false_eq_true] at owned'
  have shape : response.val =
      (⟨some ⟨⟨.commitment event (owner, .prepared serial), material.call.opening⟩,
        material.evidence⟩⟩ : (nativeApplication).Action) := by
    rw [← handleEq, ← packet]
    exact action
  have usable : material.call.opening.bind (fun raw => raw.as? payload) ≠ none := by
    intro missing
    exact clean ⟨event, payload, serial, material.call.opening, material.evidence, binding,
      shape, missing⟩
  obtain ⟨value, decoded⟩ := Option.ne_none_iff_exists'.mp usable
  have prepared : PhaseProposal.bindingPreparation material =
      some (⟨payload, value⟩ : Raw L) := by
    simp only [PhaseProposal.bindingPreparation, packet, binding, decoded, Option.map_some]
  have rawTrace := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  obtain ⟨key, query, _positive⟩ := phaseProposalDomainValues_fullSupport_of_binding setup
    .concurrent implementation.runtime implementation.leaks operational.completePending
      implementation.plan operational.maximalPhases values fullValues implementation.horizon
        implementation.scheduler rawTrace owner rfl event payload binding request
  refine ⟨payload, binding, key, serial, value, handleEq, request, query, prepared, ?_, ?_⟩
  · exact (foreign_binding_response_atom setup values implementation operational fullValues rates
      waitPositive waitBelow slotPositive badPositive badBelow remaining owner execution trace event
        payload binding request key query response material sent value prepared serial
          (packet.trans (congrArg (Payload.commitment event) handleEq))).1
  · exact sourceReplay_proper_response_atom setup values implementation operational fullValues rates
      waitPositive waitBelow slotPositive badPositive badBelow remaining owner execution trace event
        payload binding request key query response material sent value prepared serial
          (packet.trans (congrArg (Payload.commitment event) handleEq)) tag

open Classical in
/-- At a genuine clean callback the class contains exactly its mechanical
factor and, only for a proper SEND, its literal updated queried draw. -/
private theorem sourceReplay_clean_callback_draw_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (clean : ¬ PhaseProposal.GeneratedUnusableBindingAction implementation.runtime
      implementation.leaks owner response.val)
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L)) :
    let draw := sourceReplayBindingDrawAtom setup values implementation owner
      (execution.recall owner) (execution.observe nativeApplication owner) response.val
    phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner)
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) =
        foreignMechanicalAtom setup implementation rates execution owner response.val * draw ∧
      phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner (execution.recall owner)
            (execution.observe nativeApplication owner) response.val =
        foreignMechanicalAtom setup implementation rates execution owner response.val * draw *
          sourceReplayAliases setup implementation rates.aliases owner execution tag
            (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner (execution.recall owner)
                (execution.observe nativeApplication owner) response) (tag, some response.val) := by
  classical
  dsimp only
  by_cases bindingPacket : ∃ (material : WitnessedSubmission (serviceGraph setup .concurrent))
      (event : (serviceGraph setup .concurrent).EventId)
      (handle : Handle (serviceGraph setup .concurrent)),
      response.val.transmission = some material ∧ material.call.packet = .commitment event handle
  · obtain ⟨material, event, handle, sent, packet⟩ := bindingPacket
    obtain ⟨payload, binding, key, serial, value, _handle, _request, queried, prepared,
      classAtom, responseAtom⟩ := sourceReplay_proper_callback_atom setup values implementation
        operational fullValues rates waitPositive waitBelow slotPositive badPositive badBelow
          remaining owner execution trace response clean material sent event handle packet tag
    have draw : sourceReplayBindingDrawAtom setup values implementation owner
        (execution.recall owner) (execution.observe nativeApplication owner) response.val =
          ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
            owner payload binding choice.val.val)) value := by
      simp only [sourceReplayBindingDrawAtom, sent, packet, prepared, dite_eq_left binding, queried]
    rw [draw]
    exact ⟨classAtom, responseAtom⟩
  · have noncommit : ∀ material, response.val.transmission = some material →
        ∀ event handle, material.call.packet ≠ .commitment event handle := by
      intro material sent event handle called
      exact bindingPacket ⟨material, event, handle, sent, called⟩
    have draw : sourceReplayBindingDrawAtom setup values implementation owner
        (execution.recall owner) (execution.observe nativeApplication owner) response.val = 1 := by
      cases sent : response.val.transmission with
      | none => simp only [sourceReplayBindingDrawAtom, sent]
      | some material =>
          cases packet : material.call.packet with
          | commitment event handle => exact (noncommit material sent event handle packet).elim
          | opening => simp only [sourceReplayBindingDrawAtom, sent, packet]
          | malformed => simp only [sourceReplayBindingDrawAtom, sent, packet]
    rw [draw, mul_one]
    exact sourceReplay_noncommit_response_atom setup values implementation operational
      fullValues rates waitPositive waitBelow slotPositive badPositive badBelow remaining owner
        execution trace tag response noncommit

open Classical in
/-- Every recalled callback contributes its class and alias atoms at the
literal earlier input. The indexed products retain silent callbacks and all
historical preparations, including those of a subsequently excluded owner. -/
theorem sourceReplay_foreign_callback_product
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) :
    ∃ selected : (owner : Player) →
        (index : Fin (control.execution.recall owner).length) →
        PhaseProposal.Response implementation.runtime implementation.leaks implementation.bounds
          owner ((control.execution.recall owner).take index.val)
            (control.execution.recall owner)[index.val].beforeView,
      (∀ owner index, (selected owner index).val =
        (control.execution.recall owner)[index.val].action) ∧
      (∀ (owner : Player) (first second : Fin (control.execution.recall owner).length)
        (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
        (control.execution.recall owner)[first.val].emitted = some message →
        (control.execution.recall owner)[second.val].emitted = some message → first = second) ∧
      (∀ (owner : Player) (index : Fin (control.execution.recall owner).length),
        ∃ (before : (nativeApplication).Control)
          (prior : (nativeProtocol).Trace (some before)),
        TracePrefix prior trace ∧ before.actor = some owner ∧
          before.execution.recall owner = (control.execution.recall owner).take index.val ∧
          (control.execution.recall owner)[index.val].beforeView =
            before.execution.observe nativeApplication owner) ∧
      let classes := fun (owner : Player)
          (index : Fin (control.execution.recall owner).length) =>
        phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner
            ((control.execution.recall owner).take index.val)
            (control.execution.recall owner)[index.val].beforeView
            (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner ((control.execution.recall owner).take index.val)
                (control.execution.recall owner)[index.val].beforeView (selected owner index))
      let aliases := fun (owner : Player)
          (index : Fin (control.execution.recall owner).length) =>
        PMF.splitKernel
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner ((control.execution.recall owner).take index.val)
              (control.execution.recall owner)[index.val].beforeView)
          (PhaseProposal.canonicalResponse implementation.runtime implementation.leaks
            implementation.bounds owner ((control.execution.recall owner).take index.val)
              (control.execution.recall owner)[index.val].beforeView)
          (PhaseProposal.project_canonicalResponse implementation.runtime implementation.leaks
            implementation.bounds owner ((control.execution.recall owner).take index.val)
              (control.execution.recall owner)[index.val].beforeView)
          rates.aliases.val rates.aliases.property.1 rates.aliases.property.2
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner ((control.execution.recall owner).take index.val)
              (control.execution.recall owner)[index.val].beforeView (selected owner index))
          (selected owner index)
      (∀ owner index, phaseProposalReferencePolicy setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan values rates owner
          ((control.execution.recall owner).take index.val)
          (control.execution.recall owner)[index.val].beforeView
          (control.execution.recall owner)[index.val].action =
        classes owner index * aliases owner index) ∧
      (∀ who : Player,
        (∏ owner ∈ Finset.univ.erase who,
          (((nativeApplication).privateTranscriptFrom [] (control.execution.recall owner)).map
            (fun record => phaseProposalReferencePolicy setup .concurrent implementation.runtime
              implementation.leaks implementation.bounds implementation.plan values rates owner
                record.1.1 record.1.2 record.2)).prod.toReal) =
        (∏ owner ∈ Finset.univ.erase who, ∏ index, (classes owner index).toReal) *
          (∏ owner ∈ Finset.univ.erase who, ∏ index, (aliases owner index).toReal)) ∧
      ∀ (who : Player) (tape : ReservedEpoch.Tape Player implementation.tapeLength),
        (((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).historyReachWeight
          (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
            implementation.leaks implementation.bounds implementation.plan nativeInitial
              implementation.horizon implementation.scheduler values rates)
          ⟨some control, trace⟩).toReal *
            (prefixTapeLaw setup implementation ⟨some control, trace⟩ tape).toReal =
          (implementation.prior tape).toReal *
            sourceReplayFixedTransitionMass setup implementation tape trace *
            ((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).ownPlayReachProbability
              (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
                implementation.leaks implementation.bounds implementation.plan nativeInitial
                  implementation.horizon implementation.scheduler values rates who)
              (((nativeMenu).information nativeInitial implementation.horizon
                implementation.scheduler).ownPlay who trace) *
            (∏ owner ∈ Finset.univ.erase who, ∏ index, (classes owner index).toReal) *
            (∏ owner ∈ Finset.univ.erase who, ∏ index, (aliases owner index).toReal) := by
  have factual (owner : Player) (index : Fin (control.execution.recall owner).length) :
      ∃ (before : (nativeApplication).Control)
        (prior : (nativeProtocol).Trace (some before)),
        TracePrefix prior trace ∧ before.actor = some owner ∧
          before.execution.recall owner = (control.execution.recall owner).take index.val ∧
          (control.execution.recall owner)[index.val].beforeView =
            before.execution.observe nativeApplication owner ∧
          (control.execution.recall owner)[index.val].action ∈ (nativeMenu).actions owner
            ((control.execution.recall owner).take index.val)
            (before.execution.observe nativeApplication owner) := by
    have recalled : control.execution.recall owner =
        (control.execution.recall owner).take index.val ++
          (control.execution.recall owner)[index.val] ::
            (control.execution.recall owner).drop (index.val + 1) := by
      rw [← List.drop_eq_getElem_cons index.isLt]
      exact (List.take_append_drop index.val _).symm
    exact (nativeMenu).recorded_response_at nativeInitial implementation.horizon
      implementation.scheduler control trace owner
        ((control.execution.recall owner).take index.val)
        (control.execution.recall owner)[index.val]
        ((control.execution.recall owner).drop (index.val + 1)) recalled
  have available (owner : Player) (index : Fin (control.execution.recall owner).length) :
      (control.execution.recall owner)[index.val].action ∈ (nativeMenu).actions owner
        ((control.execution.recall owner).take index.val)
        (control.execution.recall owner)[index.val].beforeView := by
    obtain ⟨before, _prior, _kept, _acting, _past, viewed, offered⟩ := factual owner index
    simpa only [viewed] using offered
  let selected := fun (owner : Player)
      (index : Fin (control.execution.recall owner).length) =>
    (⟨(control.execution.recall owner)[index.val].action, available owner index⟩ :
      PhaseProposal.Response implementation.runtime implementation.leaks implementation.bounds
        owner ((control.execution.recall owner).take index.val)
          (control.execution.recall owner)[index.val].beforeView)
  refine ⟨selected, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro owner first second message firstSent secondSent
    have order := (nativeApplication).emissionOrder_history implementation.scheduler nativeInitial
      implementation.horizon ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler trace)
    have outputUnique : ((nativeApplication).outputs (control.execution.recall owner)).Nodup := by
      apply List.Nodup.of_map Message.id
      rw [order owner]
      exact List.nodup_range.map (fun _ _ equal => (Prod.mk.inj equal).2)
    change ((control.execution.recall owner).filterMap
      ReactiveApplication.PlayerEntry.emitted).Pairwise (· ≠ ·) at outputUnique
    have distinct := List.pairwise_filterMap.mp outputUnique
    apply Fin.ext
    rcases lt_trichotomy first.val second.val with earlier | equal | later
    · exact False.elim ((distinct.rel_getElem_of_lt first.isLt second.isLt earlier)
        message firstSent message secondSent rfl)
    · exact equal
    · exact False.elim ((distinct.rel_getElem_of_lt second.isLt first.isLt later)
        message secondSent message firstSent rfl)
  · intro owner index
    obtain ⟨before, prior, kept, acting, past, viewed, _offered⟩ := factual owner index
    exact ⟨before, prior, kept, acting, past, viewed⟩
  · intro classes aliases
    have atoms (owner : Player) (index : Fin (control.execution.recall owner).length) :
        phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
          implementation.bounds implementation.plan values rates owner
          ((control.execution.recall owner).take index.val)
          (control.execution.recall owner)[index.val].beforeView
          (control.execution.recall owner)[index.val].action =
            classes owner index * aliases owner index := by
      obtain ⟨⟨remaining, actor, execution⟩, prior, _kept, acting, past, viewed, offered⟩ :=
        factual owner index
      change actor = some owner at acting
      subst actor
      let response : PhaseProposal.Response implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner) :=
        ⟨(control.execution.recall owner)[index.val].action, by
          change (control.execution.recall owner)[index.val].action ∈
            PhaseCount.onePacketActions implementation.runtime implementation.leaks
              implementation.bounds owner ((control.execution.recall owner).take index.val)
                (execution.observe nativeApplication owner) at offered
          rw [← past] at offered
          exact offered⟩
      have atom := sourceReplay_counted_response_atom setup values implementation operational
        fullValues rates waitPositive waitBelow slotPositive badPositive badBelow remaining owner
          execution prior none response
      rw [sourceReplayAliases_atom setup implementation rates.aliases owner execution none _
        response] at atom
      let factor (past : List (nativeApplication).PlayerEntry)
          (view : (nativeApplication).PlayerView)
          (chosen : PhaseProposal.Response implementation.runtime implementation.leaks
            implementation.bounds owner past view) : Prop :=
        phaseProposalReferencePolicy setup .concurrent implementation.runtime implementation.leaks
            implementation.bounds implementation.plan values rates owner past view chosen.val =
          phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
              implementation.bounds implementation.plan values rates owner past view
              (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                implementation.bounds owner past view chosen) *
            PMF.splitKernel
              (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                implementation.bounds owner past view)
              (PhaseProposal.canonicalResponse implementation.runtime implementation.leaks
                implementation.bounds owner past view)
              (PhaseProposal.project_canonicalResponse implementation.runtime implementation.leaks
                implementation.bounds owner past view)
              rates.aliases.val rates.aliases.property.1 rates.aliases.property.2
              (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                implementation.bounds owner past view chosen) chosen
      have transport (firstPast secondPast : List (nativeApplication).PlayerEntry)
          (firstView secondView : (nativeApplication).PlayerView)
          (samePast : firstPast = secondPast) (sameView : firstView = secondView)
          (first : PhaseProposal.Response implementation.runtime implementation.leaks
            implementation.bounds owner firstPast firstView)
          (second : PhaseProposal.Response implementation.runtime implementation.leaks
            implementation.bounds owner secondPast secondView)
          (sameAction : first.val = second.val) :
          factor firstPast firstView first → factor secondPast secondView second := by
        subst secondPast
        subst secondView
        have sameResponse : first = second := Subtype.ext sameAction
        cases sameResponse
        exact id
      exact transport _ _ _ _ past viewed.symm response (selected owner index) rfl atom
    have foreignProduct (who : Player) :
        (∏ owner ∈ Finset.univ.erase who,
          (((nativeApplication).privateTranscriptFrom [] (control.execution.recall owner)).map
            (fun record => phaseProposalReferencePolicy setup .concurrent implementation.runtime
              implementation.leaks implementation.bounds implementation.plan values rates owner
                record.1.1 record.1.2 record.2)).prod.toReal) =
          (∏ owner ∈ Finset.univ.erase who, ∏ index, (classes owner index).toReal) *
            (∏ owner ∈ Finset.univ.erase who, ∏ index, (aliases owner index).toReal) := by
      calc
        _ = ∏ owner ∈ Finset.univ.erase who,
          ∏ index : Fin (control.execution.recall owner).length,
            (phaseProposalReferencePolicy setup .concurrent implementation.runtime
              implementation.leaks implementation.bounds implementation.plan values rates owner
              ((control.execution.recall owner).take index.val)
              (control.execution.recall owner)[index.val].beforeView
              (control.execution.recall owner)[index.val].action).toReal := by
          apply Finset.prod_congr rfl
          intro owner _member
          simpa only [List.nil_append] using
            (nativeApplication).privateTranscriptFrom_product
              (phaseProposalReferencePolicy setup .concurrent implementation.runtime
                implementation.leaks implementation.bounds implementation.plan values rates owner)
              [] (control.execution.recall owner)
        _ = ∏ owner ∈ Finset.univ.erase who,
          ∏ index : Fin (control.execution.recall owner).length,
            (classes owner index * aliases owner index).toReal := by
          apply Finset.prod_congr rfl
          intro owner _member
          apply Finset.prod_congr rfl
          intro index _present
          exact congrArg ENNReal.toReal (atoms owner index)
        _ = _ := by simp only [ENNReal.toReal_mul, Finset.prod_mul_distrib]
    refine ⟨atoms, foreignProduct, ?_⟩
    intro who tape
    let responseProduct := fun owner =>
      (((nativeApplication).privateTranscriptFrom [] (control.execution.recall owner)).map
        (fun record => phaseProposalReferencePolicy setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan values rates owner
            record.1.1 record.1.2 record.2)).prod.toReal
    have splitProduct : (∏ owner, responseProduct owner) =
        responseProduct who * ∏ owner ∈ Finset.univ.erase who, responseProduct owner :=
      (Finset.mul_prod_erase Finset.univ responseProduct (Finset.mem_univ who)).symm
    have focal := sourceReplay_prescribed_own_atom setup values implementation rates who
      control trace
    change _ = responseProduct who at focal
    rw [sourceReplay_prescribed_native_atom setup values implementation rates tape control trace]
    change (implementation.prior tape).toReal *
        sourceReplayFixedTransitionMass setup implementation tape trace *
          (∏ owner, responseProduct owner) = _
    rw [splitProduct, ← focal]
    rw [show (∏ owner ∈ Finset.univ.erase who, responseProduct owner) =
        (∏ owner ∈ Finset.univ.erase who, ∏ index, (classes owner index).toReal) *
          (∏ owner ∈ Finset.univ.erase who, ∏ index, (aliases owner index).toReal) from
      foreignProduct who]
    ring

omit [Fintype Player] in
/-- At a decoded binding query, the ordinary enriched source atom is exactly
the queried domain law's typed-value atom. The original domain law is retained;
neither a uniform payload law nor a representative source query is substituted. -/
theorem sourceReplay_source_value_atom
    {Field : Type} {layout : Field → EventField Player L}
    (refs : ContextRefs layout setup.context)
    (outputs : ∀ event, FieldRef layout (outputLayout setup.program event))
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (store : Store layout) (past : List (OwnAction Player L))
    (view : ProtocolView who setup.program)
    (decoded : decodeEventView? setup.program refs outputs who event store past = some view)
    (typed : ((setup.proposalRecoveryQuery who information).1).1.1.1 =
      some (ProtocolView.virtualBindings who (setup.context.map Prod.fst).toFinset
        setup.program view))
    (active : setup.commitRecoveryActive who
      ((setup.proposalRecoveryQuery who information).1).1.1)
    (selected : setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryQuery who information).1) :
    ((sourceUnflaggedStrategy setup values who information).map Subtype.val)
        (selected.val.val.map ProposalRecoveryMove.ordinary) =
      ((values who (setup.proposalRecoveryQuery who information)).map (fun choice =>
        phaseRecoveryDomainValue setup .concurrent event who payload binding choice.val.val))
          (phaseRecoveryDomainValue setup .concurrent event who payload binding
            selected.val.val) := by
  let key := setup.proposalRecoveryQuery who information
  let raw := fun choice : setup.CommitRecoveryValueChoice who key.1 =>
    choice.val.val.map ProposalRecoveryMove.ordinary
  have rawInjective : Function.Injective raw := by
    intro first second equal
    apply Subtype.ext
    apply Subtype.ext
    have semantic := congrArg (Option.map (fun move : ProposalRecoveryMove Player L =>
      move.semantic)) equal
    simpa only [raw, Option.map_map, Function.comp_def, ProposalRecoveryMove.ordinary,
      Option.map_id'] using semantic
  have rawLaw : (sourceUnflaggedStrategy setup values who information).map Subtype.val =
      (values who key).map raw := by
    unfold sourceUnflaggedStrategy
    rw [setup.proposalRecovery_ordinary_choice_law, PMF.map_comp]
    apply congrArg (fun transform => (values who key).map transform)
    funext choice
    change choice.val.val.map (fun move => ProposalRecoveryMove.label move false) =
      choice.val.val.map ProposalRecoveryMove.ordinary
    simp only [ProposalRecoveryMove.label_false]
  rw [rawLaw]
  change ((values who key).map raw) (raw selected) = _
  rw [pmf_map_apply_of_injective _ rawInjective selected,
    pmf_map_apply_of_injective _
      (phaseRecoveryDomainValue_injective setup .concurrent refs outputs who event payload
        binding store past view decoded key.1 typed active) selected]

/-- The literal initializer and public Nature probability at an actual row.
Scheduler and behavioral response probabilities are excluded. -/
private def sourceReplayNatureStepAtom
    (before after : (nativeProtocol).State) : ℝ≥0∞ :=
  match before with
  | none => (nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler none (fun _ => none) after
  | some control => match control.actor with
    | some _ => 1
    | none => if control.remaining = 0 then 1 else
        match after with
        | none => 0
        | some next => match next.execution.environmentRecall.getLast? with
          | none => 0
          | some entry => (control.execution.environmentStep nativeApplication entry.command)
              next.execution

/-- The physical foreign-packet factors in the original chronological trace. -/
private def sourceReplayPacketStepAtom (rates : PhaseProposalRates) (who : Player)
    (before : (nativeProtocol).State) (joint : Player → Option (nativeApplication).Action) :
    ℝ≥0∞ :=
  match before with
  | none => 1
  | some control => match control.actor with
    | none => 1
    | some owner => if owner = who then 1 else
        match joint owner with
        | none => 0
        | some response => foreignMechanicalAtom setup implementation rates control.execution
            owner response

private theorem sourceReplay_mechanical_step_factor
    (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {before after : (nativeProtocol).State} (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support) :
    (nativeApplication).transition nativeInitial implementation.horizon
        (ReservedEpoch.family implementation.runtime implementation.leaks
          (ReservedEpoch.packetCapacity implementation.runtime) tape) before joint after *
      sourceReplayPacketStepAtom setup implementation rates who before joint =
    sourceReplayNatureStepAtom setup implementation before after *
      mechanicalStepAtom setup implementation rates who tape before after joint := by
  cases before with
  | none =>
    simp only [sourceReplayPacketStepAtom, sourceReplayNatureStepAtom, mechanicalStepAtom,
      ReactiveApplication.transition, mul_one]
  | some control =>
    rcases control with ⟨remaining, actor, execution⟩
    cases actor with
    | some owner =>
      change after ∈ (PMF.pure (some (⟨remaining, none,
        execution.respond nativeApplication owner ((joint owner).getD ⟨none⟩)⟩ :
          (nativeApplication).Control))).support at moved
      cases (PMF.mem_support_pure_iff ..).mp moved
      simp only [ReactiveApplication.transition, PMF.pure_apply_self,
        sourceReplayPacketStepAtom, sourceReplayNatureStepAtom, mechanicalStepAtom, one_mul]
      cases joint owner <;> rfl
    | none =>
      cases remaining with
      | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
      | succ remaining =>
        change after ∈ ((implementation.scheduler execution.environmentRecall
          (execution.observeEnvironment nativeApplication)).bind fun command =>
            (execution.environmentStep nativeApplication command).map fun next =>
              some (⟨remaining, command.actor? nativeApplication, next⟩ :
                (nativeApplication).Control)).support at moved
        obtain ⟨command, _selected, supported⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
        obtain ⟨next, advanced, rfl⟩ := PMF.support_map .. ▸ supported
        have recorded := (nativeApplication).environmentStep_environmentRecall execution next
          command advanced
        have last : next.environmentRecall.getLast? =
            some ⟨execution.observeEnvironment nativeApplication, command⟩ := by
          rw [recorded, List.getLast?_concat]
        change (nativeApplication).transition nativeInitial implementation.horizon
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime) tape)
              (some ⟨remaining + 1, none, execution⟩) joint
                (some ⟨remaining, command.actor? nativeApplication, next⟩) * _ = _
        rw [(nativeApplication).transition_environment_apply nativeInitial implementation.horizon
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime) tape) remaining execution next
              command advanced joint]
        simp only [sourceReplayPacketStepAtom, sourceReplayNatureStepAtom, mechanicalStepAtom,
          Nat.succ_ne_zero, ↓reduceIte, last, mul_one]
        exact mul_comm _ _

/-- Every counted physical packet has positive mechanical weight at the
actual initialized input. Properness contributes its literal positive flag. -/
private theorem sourceReplay_foreign_packet_positive
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (response : (nativeApplication).Action)
    (available : response ∈ PhaseCount.onePacketActions implementation.runtime
      implementation.leaks implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner)) :
    0 < (foreignMechanicalAtom setup implementation rates execution owner response).toReal := by
  have packet := mechanicalForeignPolicy_packet_supported setup values implementation operational
    fullValues rates waitPositive waitBelow slotPositive badPositive badBelow remaining owner
      execution trace response available
  have flag : 0 < ENNReal.ofReal (1 - rates.badPreparation.val) :=
    ENNReal.ofReal_pos.mpr (sub_pos.mpr badBelow)
  apply ENNReal.toReal_pos
  · dsimp only [foreignMechanicalAtom]
    apply mul_ne_zero packet
    cases transmitted : response.transmission with
    | none => exact one_ne_zero
    | some material =>
        cases shape : material.call.packet with
        | commitment event handle => simpa only [shape] using flag.ne'
        | opening event handle raw => simpa only [shape] using (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)
        | malformed raw => simpa only [shape] using (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)
  · dsimp only [foreignMechanicalAtom]
    refine ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ?_
    cases transmitted : response.transmission with
    | none => exact ENNReal.one_ne_top
    | some material =>
        cases shape : material.call.packet with
        | commitment event handle =>
            simpa only [shape] using (ENNReal.ofReal_ne_top :
              ENNReal.ofReal (1 - rates.badPreparation.val) ≠ ∞)
        | opening event handle raw => simpa only [shape] using ENNReal.one_ne_top
        | malformed raw => simpa only [shape] using ENNReal.one_ne_top

def sourceReplayNatureMass :
    ∀ {state : (nativeProtocol).State}, (nativeProtocol).Trace state → ℝ
  | _, .start => 1
  | after, @Trace.extend _ _ before _ prior _ _ _ =>
      sourceReplayNatureMass prior *
        (sourceReplayNatureStepAtom setup implementation before after).toReal

omit [Fintype Player] in
/-- Proposal labels retain the literal Nature atom of every semantic row. -/
private theorem sourceReplay_lift_mass
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryLiftTrace labels trace).transitionMass = trace.transitionMass := by
  induction trace with
  | start => rfl
  | @extend before after prior joint legal moved ih =>
      simp only [Setup.proposalRecoveryLiftTrace, Trace.transitionMass_extend, ih]
      exact congrArg (fun kernel : PMF setup.commitRecoveryProtocol.State =>
        prior.transitionMass * (kernel after).toReal)
          (setup.proposalRecoveryLiftJoint_step labels ⟨before, joint, legal, after, moved⟩)

omit [Fintype Player] in
/-- The saved source initializer charges the original correlated draw once. -/
private theorem sourceReplay_initial_source_mass
    (theta : State L setup.context) (drawn : theta ∈ setup.initialLaw.support) :
    (RecoverySourceCheckpoint.initialized setup .concurrent implementation.plan theta
      drawn).trace.transitionMass = (setup.initialLaw theta).toReal := by
  have raw := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    history.trace.transitionMass)
      (initialized_checkpoint_history setup .concurrent implementation.plan theta drawn)
  rw [raw]
  change 1 * ((setup.initialLaw.map fun input =>
    some (CommitRecoveryState.atPoint
      (ProtocolState.entry setup.program (setup.initialConfig input)) ∅ 0))
        (some (CommitRecoveryState.atPoint
          (ProtocolState.entry setup.program (setup.initialConfig theta)) ∅ 0))).toReal = _
  have injective : Function.Injective fun input : State L setup.context =>
      some (CommitRecoveryState.atPoint
        (ProtocolState.entry setup.program (setup.initialConfig input)) ∅ 0) := by
    intro first second same
    have points := congrArg CommitRecoveryState.point (Option.some.inj same)
    exact congrArg Config.state (ProtocolState.entry_injective setup.program points)
  rw [one_mul, pmf_map_apply_of_injective _ injective]

omit [Fintype Player] in
/-- A genuine source sample retains its original draw atom in the actual
syntactic suffix, with arbitrary inherited exclusions. -/
private theorem sourceReplay_source_sample_atom
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (name : VarId) (payload : L.Ty) (fresh : name ∉ Γ.map Prod.fst)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (lift : ProtocolState (.sample name fresh law next) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.sample name fresh law next) lift)
    (source : Config Player L Γ) (excluded : Finset Player) (generation : Nat)
    (joint : Player → Option (CommitRecoveryMove Player L)) (value : L.Val payload) :
    (CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (.sample name fresh law next) source)) excluded generation).step
        joint (CommitRecoveryState.atPoint
          (lift (.inr (ProtocolState.entry next (sampleSuccessor name source value))))
          excluded generation) = L.evalDist law (sourcePublicEnv source.state) value := by
  let state := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (.sample name fresh law next) source)) excluded generation
  have notCommit : ProtocolState.atCommit setup.program state.point = false := by
    simp only [state, CommitRecoveryState.atPoint, origin.atCommit_lift,
      ProtocolState.entry, ProtocolState.atCommit, Sum.elim_inl]
  change state.step joint _ = _
  rw [state.step_noncommit_law (CommitRecoveryState.atPoint_blockFrontier _ _ _)
    notCommit joint]
  change ((ProtocolState.recoveryStep setup.program
    (lift (ProtocolState.entry (.sample name fresh law next) source)) excluded joint).map _) _ = _
  rw [origin.recoveryStep_lift]
  simp only [ProtocolState.recoveryStep, ProtocolState.entry, Sum.elim_inl,
    PMF.map_comp, Function.comp_def]
  apply pmf_map_apply_of_injective
  intro first second same
  have points := congrArg CommitRecoveryState.point same
  have suffix := sourceReplaySuffixInjective setup origin points
  have configs := ProtocolState.entry_injective next (Sum.inr.inj suffix)
  exact congrArg (fun config => config.state.get .here) configs

/-- The native initializer retains every encoded input of the joint draw. -/
private theorem sourceReplay_initial_native_atom
    (theta : State L setup.context) :
    (nativeApplication).transition nativeInitial implementation.horizon
        implementation.scheduler none (fun _ => none)
          (some ⟨implementation.horizon, none,
            ReactiveApplication.Execution.initial nativeApplication
              (PhaseRuntimeState.initial implementation.plan (encodeInputs theta))⟩) =
      setup.initialLaw theta := by
  change ((setup.initialLaw.map fun input =>
    PhaseRuntimeState.initial implementation.plan (encodeInputs input)).map fun state =>
      some (⟨implementation.horizon, none,
        ReactiveApplication.Execution.initial nativeApplication state⟩ :
          (nativeApplication).Control)) _ = _
  rw [PMF.map_comp]
  apply pmf_map_apply_of_injective
  intro first second same
  have physical := congrArg (fun control : (nativeApplication).Control =>
    control.execution.application.current.native.config.inputs) (Option.some.inj same)
  simp only [phaseInitial_eq_raw] at physical
  change encodeInputs first = encodeInputs second at physical
  funext name kind source
  have firstRead := encodeInputs_get first source
  have secondRead := encodeInputs_get second source
  rw [physical, secondRead] at firstRead
  cases kind <;> exact firstRead.symm

omit [Fintype Player] in
/-- A physical sample atom is its original public draw, through all automatic
normalization and with arbitrary inherited exclusions. -/
private theorem sourceReplay_sample_atom
    (physical : (nativeApplication).Execution)
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : physical.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist (graphLayout setup.program) payload)
    (output : (serviceGraph setup .concurrent).outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode (graphLayout setup.program)) output)
      ((serviceGraph setup .concurrent).nodes event) = .sample payload law)
    (allowed : physical.application.commandAllowed (.executeSample event) = true)
    (draw : PMF (L.Val payload))
    (evaluates : law.eval? physical.application.current.native.config.store = some draw)
    (value : L.Val payload) :
    physical.environmentStep nativeApplication (.application (.executeSample event))
      (PhaseRuntimeState.normalizeExecution implementation.runtime implementation.leaks
        (PhaseBindingRepair.rawSample implementation.runtime implementation.leaks physical
          event payload output ready value)) = draw value := by
  let next (raw : L.Val payload) :=
    PhaseRuntimeState.normalizeExecution implementation.runtime implementation.leaks
      (PhaseBindingRepair.rawSample implementation.runtime implementation.leaks physical
        event payload output ready raw)
  have stored (raw : L.Val payload) :
      (next raw).application.current.native.config.outputs event =
        some (cast (congrArg EventField.Value output.symm) raw) := by
    exact PhaseRuntimeState.normalize_sample_output physical.application event ready payload
      output allowed (cast (congrArg EventField.Value output.symm) raw)
  have injective : Function.Injective next := by
    intro first second same
    have read := congrArg (fun execution : (nativeApplication).Execution =>
      execution.application.current.native.config.outputs event) same
    rw [stored first, stored second] at read
    exact (cast_inj _).mp (Option.some.inj read)
  have kernel := PhaseBindingRepair.sample_environment_law implementation.runtime
    implementation.leaks physical event ready payload law output code
      (nodeView_eq_sample output code) allowed draw evaluates
  rw [kernel]
  exact pmf_map_apply_of_injective draw injective value

/-- The first actual selected checkpoint and native initializer have identical
whole-draw mass, including hidden input correlations. -/
private theorem sourceReplay_initial_nature_mass
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal none joint)
    (moved : some control ∈ ((nativeProtocol).step none ⟨joint, legal⟩).support) :
    sourceReplayNatureMass setup implementation (.extend .start joint legal moved) =
      (canonicalSource setup implementation operational
        ⟨some control, .extend .start joint legal moved⟩).trace.transitionMass := by
  let trace : (nativeProtocol).Trace (some control) := .extend .start joint legal moved
  have selected := (checkpointSelectionStep setup implementation operational
    (.start : (nativeProtocol).Trace none) joint legal moved PUnit.unit).property
  obtain ⟨theta, drawn, physical, history⟩ := selected
  have selectedHistory :
      (⟨_, (checkpointSelection setup implementation operational trace).val.checkpoint.trace⟩ :
        setup.commitRecoveryProtocol.History) =
      ⟨_, (RecoverySourceCheckpoint.initialized setup .concurrent implementation.plan
        theta drawn).trace⟩ := history
  have mass := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    history.trace.transitionMass) selectedHistory
  change 1 * (sourceReplayNatureStepAtom setup implementation none (some control)).toReal = _
  rw [one_mul]
  change _ = (setup.proposalRecoveryLiftTrace _
    (checkpointSelection setup implementation operational
      trace).val.checkpoint.trace).transitionMass
  rw [sourceReplay_lift_mass, mass,
    sourceReplay_initial_source_mass setup implementation theta drawn]
  have reached : some control ∈ ((nativeProtocol).step none ⟨joint, legal⟩).support := moved
  change some control ∈ ((nativeInitial).map fun native =>
    some (⟨implementation.horizon, none,
      ReactiveApplication.Execution.initial nativeApplication native⟩ :
        (nativeApplication).Control)).support at reached
  obtain ⟨native, _nativeSupport, sameControl⟩ := PMF.support_map .. ▸ reached
  have controlEq : control = ⟨implementation.horizon, none,
      ReactiveApplication.Execution.initial nativeApplication native⟩ :=
    Option.some.inj sameControl.symm
  have nativeEq : native =
      PhaseRuntimeState.initial implementation.plan (encodeInputs theta) := by
    simpa only [controlEq, ReactiveApplication.Execution.initial] using physical
  subst native
  rw [controlEq]
  exact congrArg ENNReal.toReal (sourceReplay_initial_native_atom setup implementation theta)


omit [Fintype Player] in
private theorem sourceReplay_close_within_saved
    (current : CommitRecoveryState setup.program)
    (within : ProtocolState.remaining setup.program current.point ≤
      ProtocolState.remaining setup.program current.saved) :
    ProtocolState.remaining setup.program current.close.point ≤
      ProtocolState.remaining setup.program current.close.saved := by
  unfold CommitRecoveryState.close
  split
  · split
    · split <;> exact le_rfl
    · exact le_rfl
  · split
    · exact within
    · exact le_rfl

omit [Fintype Player] in
private theorem sourceReplay_trace_within_saved
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    state.elim True (fun current =>
      ProtocolState.remaining setup.program current.point ≤
        ProtocolState.remaining setup.program current.saved) := by
  induction trace with
  | start => trivial
  | @extend before after prior joint legal moved ih =>
      cases before with
      | none =>
          obtain ⟨inputs, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
          exact le_rfl
      | some current =>
          obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
          obtain ⟨raw, rawSupported, rfl⟩ := current.step_raw_result joint next supported
          have consumed := ProtocolState.recoveryStep_remaining setup.program current.point
            current.excluded joint raw.1 legal.1 rawSupported
          apply sourceReplay_close_within_saved
          change ProtocolState.remaining setup.program raw.1.1 ≤
            ProtocolState.remaining setup.program current.saved
          change ProtocolState.remaining setup.program current.point ≤
            ProtocolState.remaining setup.program current.saved at ih
          omega

omit [Fintype Player] in
private theorem sourceReplay_saved_remaining_step
    {before after : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace before)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (moved : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support) :
    after.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) ≤
      before.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) := by
  cases before with
  | none =>
      obtain ⟨inputs, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
      simp only [Option.elim_some, Option.elim_none, CommitRecoveryState.atPoint,
        ProtocolState.remaining_entry, le_refl]
  | some current =>
      obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
      obtain ⟨raw, rawSupported, rfl⟩ := current.step_raw_result joint next supported
      have within := sourceReplay_trace_within_saved setup trace
      have consumed := ProtocolState.recoveryStep_remaining setup.program current.point
        current.excluded joint raw.1 legal.1 rawSupported
      exact close_saved_remaining_le (current.install raw.1 raw.2) (by
        change ProtocolState.remaining setup.program raw.1.1 ≤
          ProtocolState.remaining setup.program current.saved
        change ProtocolState.remaining setup.program current.point ≤
          ProtocolState.remaining setup.program current.saved at within
        omega)

omit [Fintype Player] in
private theorem sourceReplay_saved_remaining_le_of_prefix
    {first last : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace first)
    (trace : setup.commitRecoveryProtocol.Trace last) (retained : TracePrefix prior trace) :
    last.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) ≤
      first.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) := by
  induction retained with
  | refl => exact le_rfl
  | @extend before after middle earlier joint legal moved ih =>
      exact (sourceReplay_saved_remaining_step setup middle joint legal moved).trans ih

omit [Fintype Player] in
private theorem sourceReplay_actor_at_rank :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (event : Fin (eventCount program)),
      event.val = instructionCount program - ProtocolState.remaining program point →
        ProtocolState.actor program point = eventOwner? program event := by
  intro Γ O program
  induction program with
  | ret payoffs => intro point event; exact Fin.elim0 event
  | sample name fresh law suffix ih =>
      intro point event rank
      cases point with
      | inl source =>
          have same : event = ⟨0, by simp only [eventCount]; omega⟩ := by
            apply Fin.ext
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
              Nat.sub_self] using rank
          rw [same]
          rfl
      | inr point =>
          have bound := ProtocolState.remaining_le_instructionCount suffix point
          have width := event.isLt
          have counts := eventCount_eq_instructionCount suffix
          simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at rank
          simp only [eventCount] at width
          let tail : Fin (eventCount suffix) := ⟨event.val - 1, by omega⟩
          have same : event = tail.succ := Fin.ext (by
            change event.val = event.val - 1 + 1
            omega)
          have tailRank : tail.val = instructionCount suffix -
              ProtocolState.remaining suffix point := by
            dsimp only [tail]
            omega
          rw [same]
          exact ih point tail tailRank
  | commit name owner fresh guard suffix ih =>
      intro point event rank
      cases point with
      | inl source =>
          have same : event = ⟨0, by simp only [eventCount]; omega⟩ := by
            apply Fin.ext
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
              Nat.sub_self] using rank
          rw [same]
          rfl
      | inr point =>
          have bound := ProtocolState.remaining_le_instructionCount suffix point
          have width := event.isLt
          have counts := eventCount_eq_instructionCount suffix
          simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at rank
          simp only [eventCount] at width
          let tail : Fin (eventCount suffix) := ⟨event.val - 1, by omega⟩
          have same : event = tail.succ := Fin.ext (by
            change event.val = event.val - 1 + 1
            omega)
          have tailRank : tail.val = instructionCount suffix -
              ProtocolState.remaining suffix point := by
            dsimp only [tail]
            omega
          rw [same]
          exact ih point tail tailRank
  | reveal published owner name fresh selected unresolved suffix ih =>
      intro point event rank
      cases point with
      | inl source =>
          have same : event = ⟨0, by simp only [eventCount]; omega⟩ := by
            apply Fin.ext
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
              Nat.sub_self] using rank
          rw [same]
          rfl
      | inr point =>
          have bound := ProtocolState.remaining_le_instructionCount suffix point
          have width := event.isLt
          have counts := eventCount_eq_instructionCount suffix
          simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr] at rank
          simp only [eventCount] at width
          let tail : Fin (eventCount suffix) := ⟨event.val - 1, by omega⟩
          have same : event = tail.succ := Fin.ext (by
            change event.val = event.val - 1 + 1
            omega)
          have tailRank : tail.val = instructionCount suffix -
              ProtocolState.remaining suffix point := by
            dsimp only [tail]
            omega
          rw [same]
          exact ih point tail tailRank

omit [Fintype Player] in
private theorem sourceReplay_owned_step_atom
    (current : CommitRecoveryState setup.program) (owner : Player)
    (acting : ProtocolState.actor setup.program current.point = some owner)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some current) joint)
    (next : CommitRecoveryState setup.program)
    (moved : some next ∈
      (setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩).support) :
    (setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩) (some next) = 1 := by
  have supported : next ∈ (current.step joint).support := by
    change some next ∈ ((current.step joint).map some).support at moved
    obtain ⟨other, supported, same⟩ := (PMF.mem_support_map_iff ..).mp moved
    cases Option.some.inj same
    exact supported
  change ((current.step joint).map some) (some next) = 1
  rw [pmf_map_apply_of_injective _ (Option.some_injective _)]
  apply (PMF.apply_eq_one_iff _ _).mpr
  ext result
  constructor
  · intro member
    exact Set.mem_singleton_iff.mpr
      (setup.commitRecovery_step_unique_of_actor current owner acting joint
        result next member supported)
  · intro same
    cases Set.mem_singleton_iff.mp same
    exact supported

omit [Fintype Player] in
private theorem sourceReplay_owned_interval_mass
    {first last : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace first)
    (trace : setup.commitRecoveryProtocol.Trace last)
    (retained : TracePrefix prior trace)
    (owned : ∀ {before after : setup.commitRecoveryProtocol.State}
      (middle : setup.commitRecoveryProtocol.Trace before)
      (joint : Player → Option (CommitRecoveryMove Player L))
      (legal : setup.commitRecoveryProtocol.Legal before joint)
      (moved : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support),
      TracePrefix prior middle → TracePrefix (middle.extend joint legal moved) trace →
        ∃ (current : CommitRecoveryState setup.program) (owner : Player),
          before = some current ∧
          ProtocolState.actor setup.program current.point = some owner) :
    trace.transitionMass = prior.transitionMass := by
  induction retained with
  | refl => rfl
  | @extend before after middle earlier joint legal moved ih =>
      have lastKept : TracePrefix middle (middle.extend joint legal moved) :=
        .extend .refl joint legal moved
      have mass : middle.transitionMass = prior.transitionMass := by
        apply ih
        intro source target initialTrace row rowLegal rowMoved left right
        exact owned initialTrace row rowLegal rowMoved left (right.trans lastKept)
      obtain ⟨current, owner, source, acting⟩ :=
        owned middle joint legal moved earlier .refl
      cases source
      obtain ⟨next, supported, same⟩ := (PMF.mem_support_map_iff ..).mp moved
      cases same
      have atom := sourceReplay_owned_step_atom setup current owner acting
        joint legal next moved
      rw [Trace.transitionMass_extend, atom, ENNReal.toReal_one, mul_one, mass]

omit [Fintype Player] in
private theorem sourceReplay_prefix_some
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (retained : TracePrefix prior trace) :
    ∃ current, state = some current := by
  cases retained with
  | refl => exact ⟨first, rfl⟩
  | @extend source target middle earlier joint legal moved =>
      cases source with
      | none =>
          obtain ⟨inputs, supported, same⟩ := (PMF.mem_support_map_iff ..).mp moved
          exact ⟨_, same.symm⟩
      | some current =>
          obtain ⟨next, supported, same⟩ := (PMF.mem_support_map_iff ..).mp moved
          exact ⟨next, same.symm⟩

omit [Fintype Player] in
private theorem sourceReplay_actor_none_not_commit :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program),
      ProtocolState.actor program point = none →
        ProtocolState.atCommit program point = false := by
  intro Γ O program
  induction program with
  | ret payoffs => intro point; exact fun _ => rfl
  | sample name fresh law suffix ih =>
      intro point
      cases point with
      | inl source => exact fun _ => rfl
      | inr point => exact ih point
  | commit name owner fresh guard suffix ih =>
      intro point
      cases point with
      | inl source => intro impossible; cases impossible
      | inr point => exact ih point
  | reveal published owner name fresh selected unresolved suffix ih =>
      intro point
      cases point with
      | inl source => exact fun _ => rfl
      | inr point => exact ih point

omit [Fintype Player] in
private theorem sourceReplay_sample_free_interval_mass
    (first last : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (trace : setup.commitRecoveryProtocol.Trace (some last))
    (retained : TracePrefix prior trace)
    (nonchance : ∀ event : Fin (eventCount setup.program),
      instructionCount setup.program - ProtocolState.remaining setup.program first.saved ≤
        event.val →
      event.val < instructionCount setup.program -
        ProtocolState.remaining setup.program last.saved →
      ∃ owner, eventOwner? setup.program event = some owner) :
    trace.transitionMass = prior.transitionMass := by
  apply sourceReplay_owned_interval_mass setup prior trace retained
  intro before after middle joint legal moved left right
  obtain ⟨current, rfl⟩ := sourceReplay_prefix_some setup first prior middle left
  cases acting : ProtocolState.actor setup.program current.point with
  | some owner => exact ⟨current, owner, rfl, acting⟩
  | none =>
      have notCommit := sourceReplay_actor_none_not_commit setup.program current.point acting
      have saved := (setup.commitRecovery_blockFrontier middle).saved_eq_point_of_not_atCommit
        notCommit
      obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
      obtain ⟨raw, rawSupported, nextEq⟩ := current.step_noncommit_atPoint
        (setup.commitRecovery_blockFrontier middle) notCommit joint next supported
      have consumed := ProtocolState.recoveryStep_remaining setup.program current.point
        current.excluded joint raw legal.1 rawSupported
      have lower := sourceReplay_saved_remaining_le_of_prefix setup prior middle left
      have upper := sourceReplay_saved_remaining_le_of_prefix setup
        (middle.extend joint legal moved) trace right
      change ProtocolState.remaining setup.program current.saved ≤
        ProtocolState.remaining setup.program first.saved at lower
      change ProtocolState.remaining setup.program last.saved ≤
        ProtocolState.remaining setup.program next.saved at upper
      rw [saved] at lower
      rw [nextEq] at upper
      change ProtocolState.remaining setup.program last.saved ≤
        ProtocolState.remaining setup.program raw.1 at upper
      have bound := ProtocolState.remaining_le_instructionCount setup.program current.point
      have positive : 0 < ProtocolState.remaining setup.program current.point := by omega
      let event : Fin (eventCount setup.program) :=
        ⟨instructionCount setup.program - ProtocolState.remaining setup.program current.point,
          by rw [eventCount_eq_instructionCount]; omega⟩
      obtain ⟨owner, owned⟩ := nonchance event (by dsimp only [event]; omega)
        (by dsimp only [event]; omega)
      have sourceActor := sourceReplay_actor_at_rank setup.program current.point event rfl
      rw [acting, owned] at sourceActor
      cases sourceActor

omit [Fintype Player] in
private theorem sourceReplay_drain_ownerless_output
    (phase : RuntimePhase (serviceGraph setup .concurrent)) (fuel : Nat)
    (current : RecoveryState (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none) :
    (phase.drainFuel fuel current).native.config.outputs event =
      current.native.config.outputs event := by
  induction fuel generalizing current with
  | zero => rfl
  | succ fuel ih =>
      unfold RuntimePhase.drainFuel
      split
      · rename_i pending
        rw [ih]
        obtain ⟨owner, acting, _excluded⟩ := (Classical.choose_spec pending).2.owned
        have different : event ≠ Classical.choose pending := by
          intro same
          rw [← same, ownerless] at acting
          cases acting
        obtain ⟨action, supported⟩ := current.completeAutomatic_step
          (Classical.choose pending) (Classical.choose_spec pending).2
        rw [Config.step, PMF.support_map] at supported
        obtain ⟨value, _supported, completed⟩ := supported
        rw [← completed]
        exact Config.complete_output_of_ne _ _ _ _ _ _ different
      · rfl

omit [Fintype Player] in
private theorem sourceReplay_settle_ownerless_output
    (phases : List (RuntimePhase (serviceGraph setup .concurrent)))
    (generation : Nat) (entry current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (same : entry.native.config.outputs event = current.native.config.outputs event) :
    (PhaseRuntimeState.settle phases generation entry current retired).current.native.config.outputs
      event = current.native.config.outputs event := by
  induction phases generalizing generation entry current retired with
  | nil => rfl
  | cons phase remaining ih =>
      have drain (state : RecoveryState (serviceGraph setup .concurrent)) :
          (phase.drain state).native.config.outputs event = state.native.config.outputs event :=
        sourceReplay_drain_ownerless_output setup phase _ state event ownerless
      have rebuilt :
          (phase.drain (PhaseRuntimeState.restore entry
            (phase.drain current))).native.config.outputs event =
              current.native.config.outputs event :=
        (drain _).trans same
      unfold PhaseRuntimeState.settle
      dsimp only
      split
      · split
        · split
          · exact rebuilt
          · exact (ih generation _ _ _ rfl).trans rebuilt
        · exact (ih generation _ _ _ rfl).trans (drain current)
      · exact drain current

omit [Fintype Player] in
private theorem sourceReplay_frontier_completed_before
    (state : PhaseRuntimeState (serviceGraph setup .concurrent)) (frontier : state.Frontier)
    (event : (serviceGraph setup .concurrent).EventId)
    (below : event.val < state.attempt.phase) :
    event ∈ state.current.native.config.cut.completed := by
  have positioned := frontier.positioned
  cases phases : state.phases with
  | nil =>
      rw [phases] at positioned
      have positioned : state.current.native.config.cut.IsPrefix _ := positioned
      exact (positioned.2 event).mpr event.isLt
  | cons phase remaining =>
      rw [phases] at positioned
      apply positioned.2.1 event
      simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons,
        Option.map_some, Option.getD_some] using below

omit [Fintype Player] in
private theorem sourceReplay_live_ownerless_missing
    (state : PhaseRuntimeState (serviceGraph setup .concurrent))
    (frontier : state.Frontier) (live : state.Live)
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (lower : state.attempt.phase ≤ event.val) :
    event ∉ state.current.native.config.cut.completed := by
  intro completed
  have positioned := frontier.positioned
  cases installed : state.phases with
  | nil =>
      have bound := event.isLt
      simp only [PhaseRuntimeState.attempt, installed, List.head?_nil, Option.map_none,
        Option.getD_none] at lower
      omega
  | cons phase remaining =>
      rw [installed] at positioned
      have above : phase.low ≤ event.val := by
        simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
          Option.getD_some] using lower
      have below := positioned.2.2 event completed
      have publicOutput := EventCode.output_public_of_actor_none
        ((serviceGraph setup .concurrent).nodes event) ownerless
      have notPublication := EventCode.not_publication_of_actor_none
        ((serviceGraph setup .concurrent).nodes event) ownerless
      have typed := phase.fields event above below
      have kind : phase.kind = .sample := by
        cases kind : phase.kind with
        | sample => rfl
        | commitment =>
            rw [kind] at typed
            obtain ⟨owner, payload, shape⟩ := typed
            rw [shape] at publicOutput
            exact publicOutput.elim
        | reveal =>
            rw [kind] at typed
            obtain ⟨payload, shape⟩ := typed
            exact (notPublication (by rw [shape]; trivial)).elim
      have singleton := phase.sample_singleton kind
      apply live phase (by rw [installed]; exact Option.mem_some_iff.mpr rfl)
      intro query inside
      have bounds := (phase.mem_events query).mp inside
      have same : query = event := Fin.ext (by omega)
      exact same ▸ completed

omit [Fintype Player] in
private theorem sourceReplay_live_ownerless_saved_output
    (state : PhaseRuntimeState (serviceGraph setup .concurrent))
    (frontier : state.Frontier) (live : state.Live) (stored : state.StoredCheckpoint)
    (nonempty : state.phases ≠ [])
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none) :
    state.entry.native.config.outputs event = state.current.native.config.outputs event := by
  have entryPrefix : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
    have positioned := frontier.positioned
    cases installed : state.phases with
    | nil => exact (nonempty installed).elim
    | cons phase remaining =>
        rw [installed] at positioned
        simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
          Option.getD_some] using positioned.1
  by_cases below : event.val < state.attempt.phase
  · have completed := (entryPrefix.2 event).mpr below
    have present := (state.entry.native.config.output_available event).mpr completed
    obtain ⟨value, entryRead⟩ := Option.isSome_iff_exists.mp present
    have currentRead := stored (.inr event) value entryRead
    exact entryRead.trans currentRead.symm
  · have entryMissing : state.entry.native.config.outputs event = none := by
      cases reading : state.entry.native.config.outputs event with
      | none => rfl
      | some value =>
          have completed := (state.entry.native.config.output_available event).mp (by
            rw [reading]; rfl)
          exact (below ((entryPrefix.2 event).mp completed)).elim
    have currentMissing : state.current.native.config.outputs event = none := by
      cases reading : state.current.native.config.outputs event with
      | none => rfl
      | some value =>
          have completed := (state.current.native.config.output_available event).mp (by
            rw [reading]; rfl)
          exact (sourceReplay_live_ownerless_missing setup state frontier live event ownerless
            (by omega) completed).elim
    exact entryMissing.trans currentMissing.symm

omit [Fintype Player] in
private theorem sourceReplay_expire_ownerless
    (current : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none) :
    environmentStep implementation.runtime current (.expire event) = PMF.pure current := by
  by_cases ready : current.config.cut.Ready event
  · cases activated : current.activatedAt event with
    | none =>
        exact environmentStep_expire_of_not_activated implementation.runtime current event
          ready activated
    | some entered =>
        by_cases due : implementation.runtime.deadline event ≤ current.clock - entered
        · cases view : nodeView (serviceGraph setup .concurrent) event with
          | bind owner payload output code =>
              have acting := (EventCode.actor_cast output
                ((serviceGraph setup .concurrent).nodes event)).symm.trans
                  (congrArg EventCode.actor code)
              change (serviceGraph setup .concurrent).actor? event = some owner at acting
              rw [ownerless] at acting
              cases acting
          | resolve owner payload binding checks output code =>
              have acting := (EventCode.actor_cast output
                ((serviceGraph setup .concurrent).nodes event)).symm.trans
                  (congrArg EventCode.actor code)
              change (serviceGraph setup .concurrent).actor? event = some owner at acting
              rw [ownerless] at acting
              cases acting
          | sample payload law output code =>
              exact environmentStep_expire_sample_eq implementation.runtime current event ready
                entered activated due payload law output code view
        · exact environmentStep_expire_of_not_due implementation.runtime current event ready
            entered activated due
  · exact environmentStep_expire_of_not_ready implementation.runtime current event ready

omit [Fintype Player] in
private theorem sourceReplay_environment_ownerless_output
    (current next : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (command : EnvironmentCommand (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (other : command ≠ .executeSample event)
    (moved : next ∈ (environmentStep implementation.runtime current command).support) :
    next.config.outputs event = current.config.outputs event := by
  have stepOther (address : (serviceGraph setup .concurrent).EventId)
      (different : event ≠ address) (ready : current.config.cut.Ready address)
      (action : (serviceGraph setup .concurrent).Action address)
      (supported : next.config ∈ (current.config.step address ready action).support) :
      next.config.outputs event = current.config.outputs event := by
    rw [Config.step, PMF.support_map] at supported
    obtain ⟨value, _supported, same⟩ := supported
    rw [← same]
    exact Config.complete_output_of_ne _ _ _ _ _ _ different
  cases command with
  | advanceClock =>
      rw [environmentStep, PMF.mem_support_pure_iff] at moved
      cases moved
      rfl
  | expire address =>
      by_cases same : event = address
      · subst address
        rw [sourceReplay_expire_ownerless setup implementation current event ownerless,
          PMF.mem_support_pure_iff] at moved
        cases moved
        rfl
      · rcases environmentStep_expire_config_eq_or_mem_step implementation.runtime current next
          address moved with unchanged | ⟨ready, action, supported⟩
        · rw [unchanged]
        · exact stepOther address same ready action supported
  | executeSample address =>
      have different : event ≠ address := fun same => other (by cases same; rfl)
      rcases (environmentStep_executeSample_config_activated implementation.runtime current next
        address moved).2 with ⟨unchanged, _activated⟩ | ⟨ready, action, supported, _activated⟩
      · rw [unchanged]
      · exact stepOther address different ready action supported

omit [Fintype Player] in
private theorem sourceReplay_handle_ownerless_output
    (current next : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (message : Message Player (Payload (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (accepted : EventGraphRuntime.handle implementation.runtime current message = some next) :
    next.config.outputs event = current.config.outputs event := by
  obtain ⟨address, named, acting⟩ := handle_event_actor implementation.runtime current next
    message accepted
  obtain ⟨actual, actualNamed, ready, action, supported⟩ :=
    handle_config_mem_step implementation.runtime current next message accepted
  have same : actual = address := Option.some.inj (actualNamed.symm.trans named)
  subst actual
  have different : event ≠ address := by
    intro same
    rw [← same, ownerless] at acting
    cases acting
  rw [Config.step, PMF.support_map] at supported
  obtain ⟨value, _supported, same⟩ := supported
  rw [← same]
  exact Config.complete_output_of_ne _ _ _ _ _ _ different

omit [Fintype Player] in
private theorem sourceReplay_phase_handle_ownerless_output
    (current next : PhaseRuntimeState (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (same : current.entry.native.config.outputs event = current.current.native.config.outputs event)
    (accepted : current.handle implementation.runtime message = some next) :
    next.current.native.config.outputs event = current.current.native.config.outputs event := by
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
    have raw := sourceReplay_handle_ownerless_output setup implementation current.current.native
      native ⟨message.id, message.payload.packet.call⟩ event ownerless rawAccepted
    have normalized := sourceReplay_settle_ownerless_output setup current.phases
      current.generation current.entry
      (current.current.inclusionResult message.payload.packet.call native) current.retired event
      ownerless (same.trans raw.symm)
    exact normalized.trans raw
  · cases accepted

omit [Fintype Player] in
private theorem sourceReplay_phase_environment_ownerless_output
    (current next : PhaseRuntimeState (serviceGraph setup .concurrent))
    (command : EnvironmentCommand (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (same : current.entry.native.config.outputs event = current.current.native.config.outputs event)
    (other : command ≠ .executeSample event)
    (moved : next ∈ (current.environment implementation.runtime command).support) :
    next.current.native.config.outputs event = current.current.native.config.outputs event := by
  unfold PhaseRuntimeState.environment at moved
  split at moved
  · obtain ⟨native, rawMoved, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
    have raw := sourceReplay_environment_ownerless_output setup implementation
      current.current.native native command event ownerless other rawMoved
    have normalized := sourceReplay_settle_ownerless_output setup current.phases
      current.generation current.entry (current.current.environmentResult command native)
      current.retired event ownerless (same.trans raw.symm)
    exact normalized.trans raw
  · cases (PMF.mem_support_pure_iff _ _).mp moved
    rfl

omit [Fintype Player] in
private theorem sourceReplay_reactive_environment_ownerless_output
    (current next : (nativeApplication).Execution) (command : (nativeApplication).Command)
    (event : (serviceGraph setup .concurrent).EventId)
    (ownerless : (serviceGraph setup .concurrent).actor? event = none)
    (same : current.application.entry.native.config.outputs event =
      current.application.current.native.config.outputs event)
    (other : command ≠ .application (.executeSample event))
    (moved : next ∈ (current.environmentStep nativeApplication command).support) :
    next.application.current.native.config.outputs event =
      current.application.current.native.config.outputs event := by
  unfold ReactiveApplication.Execution.environmentStep at moved
  rw [PMF.support_map] at moved
  obtain ⟨updated, supported, rfl⟩ := moved
  cases command with
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | activate owner =>
      obtain ⟨network, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
      rfl
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change (current.includePending nativeApplication id).application.current.native.config.outputs
        event = current.application.current.native.config.outputs event
      unfold ReactiveApplication.Execution.includePending
      cases included : current.network.includePending id with
      | mk envelope network =>
          cases envelope with
          | none => rfl
          | some message =>
              dsimp only
              change ((current.application.handle implementation.runtime message).getD
                current.application).current.native.config.outputs event = _
              cases accepted : current.application.handle implementation.runtime message with
              | none => rfl
              | some application =>
                  exact sourceReplay_phase_handle_ownerless_output setup implementation
                    current.application application message event ownerless same accepted
  | application operation =>
      obtain ⟨application, applicationMoved, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
      exact sourceReplay_phase_environment_ownerless_output setup implementation
        current.application application operation event ownerless same
          (fun equal => other (by cases equal; rfl))
            applicationMoved

private theorem sourceReplay_environment_crossed_rank_owned
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (live : current.application.Live) (nonempty : current.application.phases ≠ [])
    (command : (nativeApplication).Command)
    (event : (serviceGraph setup .concurrent).EventId)
    (other : command ≠ .application (.executeSample event))
    (moved : next ∈ (current.environmentStep nativeApplication command).support)
    (lower : current.application.attempt.phase ≤ event.val)
    (upper : event.val < next.application.attempt.phase) :
    ∃ owner, eventOwner? setup.program event = some owner := by
  cases acting : (serviceGraph setup .concurrent).actor? event with
  | some owner =>
      refine ⟨owner, ?_⟩
      rw [eventOwner?_eq_actor]
      exact acting
  | none =>
      have missing := sourceReplay_live_ownerless_missing setup current.application
        first.order.frontier live event acting lower
      have same := sourceReplay_live_ownerless_saved_output setup current.application
        first.order.frontier live first.stored nonempty event acting
      have output := sourceReplay_reactive_environment_ownerless_output setup implementation
        current next command event acting same other moved
      have completed := sourceReplay_frontier_completed_before setup next.application
        last.order.frontier event upper
      have present := (next.application.current.native.config.output_available event).mpr completed
      rw [output] at present
      exact False.elim (missing
        ((current.application.current.native.config.output_available event).mp present))

private theorem sourceReplay_nonsample_interval_mass
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (live : current.application.Live) (nonempty : current.application.phases ≠ [])
    (command : (nativeApplication).Command)
    (nonsample : ∀ event : (serviceGraph setup .concurrent).EventId,
      command ≠ .application (.executeSample event))
    (moved : next ∈ (current.environmentStep nativeApplication command).support)
    (retained : TracePrefix first.checkpoint.trace last.checkpoint.trace) :
    last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass := by
  apply sourceReplay_sample_free_interval_mass setup _ _ first.checkpoint.trace
    last.checkpoint.trace retained
  intro event lower upper
  change instructionCount setup.program - ProtocolState.remaining setup.program
    (first.checkpoint.residual.lift
      (ProtocolState.entry first.checkpoint.residual.tail first.checkpoint.source)) ≤ event.val
    at lower
  change event.val < instructionCount setup.program - ProtocolState.remaining setup.program
    (last.checkpoint.residual.lift
      (ProtocolState.entry last.checkpoint.residual.tail last.checkpoint.source)) at upper
  rw [first.checkpoint.saved_position] at lower
  rw [last.checkpoint.saved_position] at upper
  exact sourceReplay_environment_crossed_rank_owned setup implementation current next first last
    live nonempty command event (nonsample event) moved lower upper

omit [Fintype Player] in
private theorem sourceReplay_sample_interval_mass
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (name : VarId) (payload : L.Ty) (fresh : name ∉ Γ.map Prod.fst)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (suffix : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (lift : ProtocolState (.sample name fresh law suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.sample name fresh law suffix) lift)
    (source : Config Player L Γ) (unique : (Γ.map Prod.fst).Nodup)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.sample name fresh law suffix))
    (aligned : CompiledReadoutSuffix setup.program (.sample name fresh law suffix) refs embedding)
    (excluded : Finset Player) (generation : Nat)
    (prior : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
      (lift (ProtocolState.entry (.sample name fresh law suffix) source)) excluded generation)))
    {state : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (last : RecoverySourceCheckpoint setup .concurrent state) (stored : state.StoredCheckpoint)
    (retained : TracePrefix prior last.trace) (longer : prior.length < last.trace.length)
    (value : L.Val payload)
    (observed :
      let head : Fin (eventCount (.sample name fresh law suffix)) := ⟨0, by simp [eventCount]⟩
      let field : FieldRef (graphLayout setup.program) (.publicData payload) := by
        simpa only [head, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.ref head
      field.get? state.current.native.config.store = some value)
    (nonchance : ∀ event : Fin (eventCount setup.program),
      instructionCount setup.program - instructionCount suffix ≤ event.val →
      event.val < instructionCount setup.program - ProtocolState.remaining setup.program
        (last.residual.lift (ProtocolState.entry last.residual.tail last.source)) →
      ∃ owner, eventOwner? setup.program event = some owner) :
    last.trace.transitionMass =
      prior.transitionMass * (L.evalDist law (sourcePublicEnv source.state) value).toReal := by
  let sourceStart := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (.sample name fresh law suffix) source)) excluded generation
  rcases retained.reachesWithin.eq_or_step with sameHistory | firstStep
  · have lengths := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      history.trace.length) sameHistory
    change prior.length = last.trace.length at lengths
    omega
  · obtain ⟨joint, legal, reached, moved, fuel, onward⟩ := firstStep
    obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
    have notCommit : ProtocolState.atCommit setup.program sourceStart.point = false := by
      simp only [sourceStart, CommitRecoveryState.atPoint, origin.atCommit_lift,
        ProtocolState.entry, ProtocolState.atCommit, Sum.elim_inl]
    have kernel : sourceStart.step joint =
        (L.evalDist law (sourcePublicEnv source.state)).map (fun sampled =>
          CommitRecoveryState.atPoint
            (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source sampled))))
            excluded generation) := by
      rw [sourceStart.step_noncommit_law (CommitRecoveryState.atPoint_blockFrontier _ _ _)
        notCommit joint]
      change (ProtocolState.recoveryStep setup.program
        (lift (ProtocolState.entry (.sample name fresh law suffix) source)) excluded joint).map _ =
          _
      rw [origin.recoveryStep_lift]
      simp only [ProtocolState.recoveryStep, ProtocolState.entry, Sum.elim_inl, PMF.map_comp,
        Function.comp_def]
      rfl
    change next ∈ (sourceStart.step joint).support at supported
    rw [kernel] at supported
    obtain ⟨sampled, _sampledSupport, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
    let head : Fin (eventCount (.sample name fresh law suffix)) := ⟨0, by simp [eventCount]⟩
    let field : FieldRef (graphLayout setup.program) (.publicData payload) := by
      simpa only [head, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.ref head
    let nextRefs := ContextRefs.cons (name := name) (cell := .publicData payload) field refs
    let nextEmbedding := embedding.tail suffix (by simp only [eventCount]) (fun _ => rfl)
    have nextAligned : CompiledReadoutSuffix setup.program suffix nextRefs nextEmbedding :=
      aligned.sampleTail setup.program fresh law suffix refs embedding
    have nextUnique : (((name, .publicData payload) :: Γ).map Prod.fst).Nodup := by
      simpa only [List.map_cons] using List.nodup_cons.mpr ⟨fresh, unique⟩
    have agreement : nextRefs.Agrees (sampleSuccessor name source sampled).state
        state.entry.native.config.store :=
      sourceReplaySuffixSavedAgreement setup suffix
        (fun point => lift (.inr point)) (origin.sampleTail fresh law suffix)
        (sampleSuccessor name source sampled) nextUnique nextRefs nextEmbedding nextAligned _
        (prior.extend joint legal moved) rfl rfl last onward.tracePrefix
    have savedRead : field.get? state.entry.native.config.store = some sampled :=
      agreement .here
    have currentRead : field.get? state.current.native.config.store = some sampled :=
      field.get?_preserved _ _ (fun query result present => stored query result present)
        sampled savedRead
    change field.get? state.current.native.config.store = some value at observed
    have sameValue : sampled = value := Option.some.inj (currentRead.symm.trans observed)
    subst sampled
    have tailMass : last.trace.transitionMass =
        (prior.extend joint legal moved).transitionMass := by
      apply sourceReplay_sample_free_interval_mass setup _ _
        (prior.extend joint legal moved) last.trace onward.tracePrefix
      intro event lower upper
      apply nonchance event
      · simpa only [CommitRecoveryState.atPoint, origin.remaining_lift,
          ProtocolState.remaining, Sum.elim_inr, ProtocolState.remaining_entry] using lower
      · exact upper
    have atom : (setup.commitRecoveryProtocol.step (some sourceStart) ⟨joint, legal⟩)
        (some (CommitRecoveryState.atPoint
          (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source value))))
          excluded generation)) = L.evalDist law (sourcePublicEnv source.state) value := by
      change ((sourceStart.step joint).map some) _ = _
      rw [pmf_map_apply_of_injective _ (Option.some_injective _)]
      exact sourceReplay_source_sample_atom setup name payload fresh law suffix lift origin
        source excluded generation joint value
    rw [tailMass, Trace.transitionMass_extend, atom]

private theorem sourceReplay_nonsample_environment_atom
    (operational : implementation.Operational)
    (current next : (nativeApplication).Execution) (command : (nativeApplication).Command)
    (nonsample : ∀ event : (serviceGraph setup .concurrent).EventId,
      command ≠ .application (.executeSample event))
    (moved : next ∈ (current.environmentStep nativeApplication command).support) :
    current.environmentStep nativeApplication command next = 1 := by
  have deterministic : ∃ ending,
      current.environmentStep nativeApplication command = PMF.pure ending := by
    cases command with
    | activate owner =>
        have complete : (nativeApplication).observePending =
            MessageNetwork.completePendingObservation := operational.completePending
        rw [ReactiveApplication.Execution.activation_samples, complete]
        simp only [MessageNetwork.completePendingObservation, PMF.pure_map]
        exact ⟨_, rfl⟩
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        exact ⟨_, rfl⟩
    | «include» id =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        exact ⟨_, rfl⟩
    | application operation =>
        cases operation with
        | executeSample event => exact (nonsample event rfl).elim
        | advanceClock =>
            change ∃ ending, (PMF.map _ (PMF.map _
              (PhaseRuntimeState.environment implementation.runtime current.application
                .advanceClock))) =
                PMF.pure ending
            simp only [PhaseRuntimeState.environment, environmentStep]
            split <;> simp only [PMF.pure_map] <;> exact ⟨_, rfl⟩
        | expire event =>
            change ∃ ending, (PMF.map _ (PMF.map _
              (PhaseRuntimeState.environment implementation.runtime current.application
                (.expire event)))) =
                PMF.pure ending
            simp only [PhaseRuntimeState.environment, environmentStep]
            split <;> simp only [PMF.pure_map] <;> exact ⟨_, rfl⟩
  obtain ⟨ending, kernel⟩ := deterministic
  rw [kernel, PMF.mem_support_pure_iff] at moved
  cases moved
  rw [kernel, PMF.pure_apply_self]

private theorem sourceReplay_sample_command_interval_mass
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (live : current.application.Live)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : current.application.phases = phase :: remaining) (kind : phase.kind = .sample)
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : current.application.current.native.config.cut.Ready event)
    (allowed : current.application.commandAllowed (.executeSample event) = true)
    (moved : next ∈
      (current.environmentStep nativeApplication (.application (.executeSample event))).support)
    (retained : TracePrefix first.checkpoint.trace last.checkpoint.trace) :
    last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass *
      (current.environmentStep nativeApplication
        (.application (.executeSample event)) next).toReal := by
  have nonempty : current.application.phases ≠ [] := by
    rw [installed]
    exact List.cons_ne_nil _ _
  have low : phase.low = current.application.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have inside : event ∈ phase.events := by
    simpa only [PhaseRuntimeState.commandAllowed, installed, List.head?_cons, Option.any_some,
      decide_eq_true_eq] using allowed
  have bounds := (phase.mem_events event).mp inside
  have singleton := phase.sample_singleton kind
  have eventRank : event.val = current.application.attempt.phase := by omega
  have applicationMoved : next.application ∈
      (current.application.environment implementation.runtime (.executeSample event)).support := by
    have supported := moved
    unfold ReactiveApplication.Execution.environmentStep at supported
    obtain ⟨updated, supported, endingEq⟩ := (PMF.mem_support_map_iff ..).mp supported
    have applicationEq := congrArg (fun execution : (nativeApplication).Execution =>
      execution.application) endingEq
    change updated.application = next.application at applicationEq
    obtain ⟨application, supported, updatedEq⟩ := (PMF.mem_support_map_iff ..).mp supported
    have updatedApplication := congrArg (fun execution : (nativeApplication).Execution =>
      execution.application) updatedEq
    change application = updated.application at updatedApplication
    rw [← applicationEq, ← updatedApplication]
    exact supported
  have ownerless : (serviceGraph setup .concurrent).actor? event = none := by
    have output := phase.fields event bounds.1 bounds.2
    rw [kind] at output
    obtain ⟨payload, output⟩ := output
    cases viewed : nodeView (serviceGraph setup .concurrent) event with
    | bind owner ty shape code => cases shape.symm.trans output
    | resolve owner ty binding checks shape code => cases shape.symm.trans output
    | sample ty law shape code =>
        exact (EventCode.actor_cast shape _).symm.trans (congrArg EventCode.actor code)
  have advanced := PhaseRuntimeState.sample_advances_phase implementation.runtime
    current.application next.application first.order.frontier phase
      (by rw [installed]; rfl) kind event (by omega) ready ownerless applicationMoved
  have longer : first.checkpoint.trace.length < last.checkpoint.trace.length := by
    have bounded := retained.length_le
    by_contra notLonger
    have same := retained.eq_of_length (by omega)
    have ranks := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      history.state.map (fun state => instructionCount setup.program -
        ProtocolState.remaining setup.program state.saved)) same
    have sameRank : current.application.attempt.phase = next.application.attempt.phase := by
      simpa only [Option.map_some, CommitRecoveryState.atPoint,
        first.checkpoint.saved_position, last.checkpoint.saved_position] using Option.some.inj ranks
    omega
  generalize checkpointEq : first.checkpoint = checkpoint at retained longer ⊢
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, terminalAligned, agrees, guards, failures, unique, ranks, actors, commits,
    owners, endpoints, automatic, histories, memories, steps, menus, readouts, prior,
    views, historyAlignment, origin⟩
  have total := compiled.countEq
  have positive : 0 < eventCount program := by
    have bounded := event.isLt
    change event.val < eventCount setup.program at bounded
    change current.application.attempt.phase + eventCount program = eventCount setup.program
      at total
    omega
  let zero : Fin (eventCount program) := ⟨0, positive⟩
  have ranked : (embedding.event zero).val = current.application.attempt.phase := by
    have ranked := compiled.rankEq zero
    dsimp only [zero] at ranked
    omega
  have sameEvent : event = embedding.event zero := Fin.ext (eventRank.trans ranked.symm)
  have headSample : RuntimePhaseKind.sample.Matches (outputLayout program zero) := by
    have typed := phase.fields (embedding.event zero) (by omega) (by omega)
    rw [kind] at typed
    change RuntimePhaseKind.sample.Matches (outputLayout setup.program (embedding.event zero))
      at typed
    rw [embedding.layout_eq] at typed
    exact typed
  cases program with
  | ret payoffs => simp only [eventCount] at positive; omega
  | commit name owner fresh guard suffix =>
      obtain ⟨payload, impossible⟩ := headSample
      cases impossible
  | reveal published owner name fresh selected unresolved suffix =>
      obtain ⟨payload, impossible⟩ := headSample
      cases impossible
  | @sample _ _ name payload fresh law suffix =>
      subst event
      have output : (serviceGraph setup .concurrent).outputLayout (embedding.event zero) =
          .publicData payload := by
        change outputLayout setup.program (embedding.event zero) = .publicData payload
        simpa only [zero, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.layout_eq zero
      have code : cast (congrArg (EventCode (graphLayout setup.program)) output)
          ((serviceGraph setup .concurrent).nodes (embedding.event zero)) =
            .sample payload (compilePublicDist refs law) := by
        change cast (congrArg (EventCode (graphLayout setup.program)) output)
          ((toEventGraph setup.program).nodes (embedding.event zero)) =
            .sample payload (compilePublicDist refs law)
        simpa only [zero, compileRankedNodes, outputLayout, Fin.mk_zero, Fin.cases_zero]
          using compiled.nodeEq zero
      have currentAgrees :
          refs.Agrees source.state current.application.current.native.config.store := by
        intro readName cell selected
        exact (refs.get selected).get?_preserved _ _
          (fun field value present => first.stored field value present) _ (agrees selected)
      let draw := L.evalDist law (sourcePublicEnv source.state)
      have evaluates : (compilePublicDist refs law).eval?
          current.application.current.native.config.store = some draw := by
        rw [PublicDist.eval?, compilePublicDist_evalLaw? refs source.state _ currentAgrees law]
        rfl
      have kernel := PhaseBindingRepair.sample_environment_law implementation.runtime
        implementation.leaks current (embedding.event zero) ready payload
          (compilePublicDist refs law) output code (nodeView_eq_sample output code) allowed
            draw evaluates
      have supported := moved
      rw [kernel] at supported
      obtain ⟨value, _sampled, nextEq⟩ := (PMF.mem_support_map_iff ..).mp supported
      cases nextEq
      let raw := PhaseBindingRepair.rawSample implementation.runtime implementation.leaks current
        (embedding.event zero) payload output ready value
      have kept := PhaseRuntimeState.normalize_keepsStore_of_noncommitment raw.application phase
        remaining installed (by rw [kind]; decide)
      have nativeRead :
          let head : Fin (eventCount (.sample name fresh law suffix)) :=
            ⟨0, by simp only [eventCount]; omega⟩
          let field : FieldRef (graphLayout setup.program) (.publicData payload) := by
            simpa only [head, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.ref head
          field.get? (PhaseRuntimeState.normalizeExecution implementation.runtime
            implementation.leaks raw).application.current.native.config.store = some value := by
        dsimp only
        apply FieldRef.get?_preserved _ _ _
          (fun field result present => kept field result present)
        change cast (congrArg (fun kind => Option kind.Value) output)
          ((current.application.current.native.complete (embedding.event zero) ready
            (cast (congrArg EventField.Action output.symm) PUnit.unit)
            (cast (congrArg EventField.Value output.symm) value)).config.outputs
              (embedding.event zero)) = some value
        change cast (congrArg (fun kind => Option kind.Value) output)
          ((current.application.current.native.config.complete (embedding.event zero) ready
            (cast (congrArg EventField.Action output.symm) PUnit.unit)
            (cast (congrArg EventField.Value output.symm) value)).outputs
              (embedding.event zero)) = some value
        rw [Config.complete_output_same]
        have castSome {A B : Type} (same : A = B) (item : A) :
            cast (congrArg Option same) (some item) = some (cast same item) := by
          cases same
          rfl
        rw [castSome (congrArg EventField.Value output), cast_cast]
        simp only [cast_eq]
      have sourceMass := sourceReplay_sample_interval_mass setup name payload fresh law suffix
        lift origin source unique refs embedding terminalAligned current.application.entry.excluded
          current.application.generation prior last.checkpoint last.stored retained longer value
            nativeRead (by
              intro query lower upper
              have afterSample : current.application.attempt.phase + 1 =
                  instructionCount setup.program - instructionCount suffix := by
                simp only [eventCount, eventCount_eq_instructionCount] at total
                omega
              have queryLower : current.application.attempt.phase ≤ query.val := by omega
              have queryUpper : query.val <
                  (PhaseRuntimeState.normalizeExecution implementation.runtime
                    implementation.leaks raw).application.attempt.phase := by
                change query.val < instructionCount setup.program -
                  ProtocolState.remaining setup.program
                    (last.checkpoint.residual.lift (ProtocolState.entry
                      last.checkpoint.residual.tail last.checkpoint.source)) at upper
                rwa [last.checkpoint.saved_position] at upper
              exact sourceReplay_environment_crossed_rank_owned setup implementation current _
                first last live nonempty (.application (.executeSample (embedding.event zero)))
                  query (by intro equal; cases equal; omega) moved queryLower queryUpper)
      have atom := sourceReplay_sample_atom setup implementation current (embedding.event zero)
        ready payload (compilePublicDist refs law) output code allowed draw evaluates value
      rw [sourceMass, atom]

omit [Fintype Player] in
private theorem sourceReplay_same_attempt_interval_mass
    {before after : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (first : RecoverySourceCheckpoint setup .concurrent before)
    (last : RecoverySourceCheckpoint setup .concurrent after)
    (same : before.attempt = after.attempt) (retained : TracePrefix first.trace last.trace) :
    last.trace.transitionMass = first.trace.transitionMass := by
  have generation := congrArg CommitAttemptId.generation same
  have phases := congrArg CommitAttemptId.phase same
  have counts := setup.commitRecovery_same_generation_length retained.reachesWithin _ _ rfl rfl
    generation
  have firstPosition := first.saved_position
  have lastPosition := last.saved_position
  have firstBound := ProtocolState.remaining_le_instructionCount setup.program
    (first.residual.lift (ProtocolState.entry first.residual.tail first.source))
  have lastBound := ProtocolState.remaining_le_instructionCount setup.program
    (last.residual.lift (ProtocolState.entry last.residual.tail last.source))
  have lengths : first.trace.length = last.trace.length := by
    change ProtocolState.remaining setup.program
        (last.residual.lift (ProtocolState.entry last.residual.tail last.source)) +
          last.trace.length =
      ProtocolState.remaining setup.program
        (first.residual.lift (ProtocolState.entry first.residual.tail first.source)) +
          first.trace.length at counts
    omega
  have histories := retained.eq_of_length lengths
  exact (congrArg (fun history : setup.commitRecoveryProtocol.History =>
    history.trace.transitionMass) histories).symm

private theorem sourceReplay_stuttering_sample_interval_mass
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (live : current.application.Live) (nonempty : current.application.phases ≠ [])
    (event : (serviceGraph setup .concurrent).EventId)
    (allowed : current.application.commandAllowed (.executeSample event) = true)
    (rawKernel : environmentStep implementation.runtime current.application.current.native
      (.executeSample event) = PMF.pure current.application.current.native)
    (moved : next ∈
      (current.environmentStep nativeApplication (.application (.executeSample event))).support)
    (retained : TracePrefix first.checkpoint.trace last.checkpoint.trace) :
    last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass *
      (current.environmentStep nativeApplication
        (.application (.executeSample event)) next).toReal := by
  have rawState : current.application.current.environmentResult (.executeSample event)
      current.application.current.native = current.application.current := by
    cases current.application.current
    rfl
  have kernel : current.environmentStep nativeApplication (.application (.executeSample event)) =
      PMF.pure { current with
        application := current.application.normalize
        environmentRecall := current.environmentRecall ++
          [⟨current.observeEnvironment nativeApplication,
            .application (.executeSample event)⟩] } := by
    change PMF.map _ (PMF.map _
      (PhaseRuntimeState.environment implementation.runtime current.application
        (.executeSample event))) = _
    simp only [PhaseRuntimeState.environment,
      allowed, ↓reduceIte, rawKernel, PMF.pure_map]
    rw [rawState]
    rfl
  have supported := moved
  rw [kernel, PMF.mem_support_pure_iff] at supported
  cases supported
  have sourceMass : last.checkpoint.trace.transitionMass =
      first.checkpoint.trace.transitionMass := by
    apply sourceReplay_sample_free_interval_mass setup _ _ first.checkpoint.trace
      last.checkpoint.trace retained
    intro query lower upper
    change instructionCount setup.program - ProtocolState.remaining setup.program
      (first.checkpoint.residual.lift
        (ProtocolState.entry first.checkpoint.residual.tail first.checkpoint.source)) ≤ query.val
      at lower
    change query.val < instructionCount setup.program - ProtocolState.remaining setup.program
      (last.checkpoint.residual.lift
        (ProtocolState.entry last.checkpoint.residual.tail last.checkpoint.source)) at upper
    rw [first.checkpoint.saved_position] at lower
    rw [last.checkpoint.saved_position] at upper
    cases acting : (serviceGraph setup .concurrent).actor? query with
    | some owner =>
        refine ⟨owner, ?_⟩
        rw [eventOwner?_eq_actor]
        exact acting
    | none =>
        have same := sourceReplay_live_ownerless_saved_output setup current.application
          first.order.frontier live first.stored nonempty query acting
        have output := sourceReplay_settle_ownerless_output setup current.application.phases
          current.application.generation current.application.entry current.application.current
          current.application.retired query acting same
        have completed := sourceReplay_frontier_completed_before setup _ last.order.frontier query
          upper
        have available := current.application.normalize.current.native.config.output_available query
        have present := available.mpr completed
        unfold PhaseRuntimeState.normalize at present
        rw [output] at present
        have oldCompleted := (current.application.current.native.config.output_available query).mp
          present
        exact (sourceReplay_live_ownerless_missing setup current.application first.order.frontier
          live query acting lower oldCompleted).elim
  rw [sourceMass, kernel, PMF.pure_apply_self, ENNReal.toReal_one, mul_one]

private theorem sourceReplay_disallowed_sample_interval_mass
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (event : (serviceGraph setup .concurrent).EventId)
    (disallowed : current.application.commandAllowed (.executeSample event) = false)
    (moved : next ∈
      (current.environmentStep nativeApplication (.application (.executeSample event))).support)
    (retained : TracePrefix first.checkpoint.trace last.checkpoint.trace) :
    last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass *
      (current.environmentStep nativeApplication
        (.application (.executeSample event)) next).toReal := by
  have kernel : current.environmentStep nativeApplication (.application (.executeSample event)) =
      PMF.pure { current with environmentRecall := current.environmentRecall ++
        [⟨current.observeEnvironment nativeApplication,
          .application (.executeSample event)⟩] } := by
    change PMF.map _ (PMF.map _
      (PhaseRuntimeState.environment implementation.runtime current.application
        (.executeSample event))) = _
    simp only [PhaseRuntimeState.environment,
      disallowed, Bool.false_eq_true, ↓reduceIte, PMF.pure_map]
  have supported := moved
  rw [kernel, PMF.mem_support_pure_iff] at supported
  cases supported
  have sourceMass := sourceReplay_same_attempt_interval_mass setup first.checkpoint
    last.checkpoint rfl retained
  rw [sourceMass, kernel, PMF.pure_apply_self, ENNReal.toReal_one, mul_one]

private theorem sourceReplay_environment_interval_mass
    (operational : implementation.Operational)
    (current next : (nativeApplication).Execution)
    (first : RecoverySourceWitness setup .concurrent implementation.plan current.application)
    (last : RecoverySourceWitness setup .concurrent implementation.plan next.application)
    (live : current.application.Live) (command : (nativeApplication).Command)
    (moved : next ∈ (current.environmentStep nativeApplication command).support)
    (retained : TracePrefix first.checkpoint.trace last.checkpoint.trace) :
    last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass *
      ((current.environmentStep nativeApplication command) next).toReal := by
  have nonsampleCase (nonsample : ∀ event : (serviceGraph setup .concurrent).EventId,
      command ≠ .application (.executeSample event)) :
      last.checkpoint.trace.transitionMass = first.checkpoint.trace.transitionMass *
        ((current.environmentStep nativeApplication command) next).toReal := by
    have atom := sourceReplay_nonsample_environment_atom setup implementation operational current
      next command nonsample moved
    have sourceMass : last.checkpoint.trace.transitionMass =
        first.checkpoint.trace.transitionMass := by
      by_cases empty : current.application.phases = []
      · apply sourceReplay_sample_free_interval_mass setup _ _ first.checkpoint.trace
          last.checkpoint.trace retained
        intro event lower _upper
        change instructionCount setup.program - ProtocolState.remaining setup.program
          (first.checkpoint.residual.lift
            (ProtocolState.entry first.checkpoint.residual.tail first.checkpoint.source)) ≤
              event.val
          at lower
        rw [first.checkpoint.saved_position] at lower
        simp only [PhaseRuntimeState.attempt, empty, List.head?_nil, Option.map_none,
          Option.getD_none] at lower
        have bounded := event.isLt
        change event.val < eventCount setup.program at bounded
        have counts := eventCount_eq_instructionCount setup.program
        change eventCount setup.program ≤ event.val at lower
        exact (by omega : False).elim
      · exact sourceReplay_nonsample_interval_mass setup implementation current next first last live
          empty command nonsample moved retained
    rw [sourceMass, atom, ENNReal.toReal_one, mul_one]
  cases command with
  | activate owner => exact nonsampleCase (by intro event impossible; cases impossible)
  | wait => exact nonsampleCase (by intro event impossible; cases impossible)
  | «include» id => exact nonsampleCase (by intro event impossible; cases impossible)
  | application operation =>
      cases operation with
      | advanceClock => exact nonsampleCase (by intro event impossible; cases impossible)
      | expire address => exact nonsampleCase (by intro event impossible; cases impossible)
      | executeSample event =>
          by_cases allowed : current.application.commandAllowed (.executeSample event) = true
          · have nonempty : current.application.phases ≠ [] := by
              intro empty
              simp only [PhaseRuntimeState.commandAllowed, empty, List.head?_nil, Option.any_none,
                Bool.false_eq_true] at allowed
            by_cases ready : current.application.current.native.config.cut.Ready event
            · cases viewed : nodeView (serviceGraph setup .concurrent) event with
              | bind owner payload output code =>
                  have kernel := environmentStep_executeSample_of_nonsample implementation.runtime
                    current.application.current.native event ready (by
                      intro ty law shape code impossible
                      rw [viewed] at impossible
                      cases impossible)
                  exact sourceReplay_stuttering_sample_interval_mass setup implementation current
                    next first last live nonempty event allowed kernel moved retained
              | resolve owner payload binding checks output code =>
                  have kernel := environmentStep_executeSample_of_nonsample implementation.runtime
                    current.application.current.native event ready (by
                      intro ty law shape code impossible
                      rw [viewed] at impossible
                      cases impossible)
                  exact sourceReplay_stuttering_sample_interval_mass setup implementation current
                    next first last live nonempty event allowed kernel moved retained
              | sample payload law output code =>
                  obtain ⟨phase, remaining, installed⟩ : ∃ phase remaining,
                      current.application.phases = phase :: remaining := by
                    cases installed : current.application.phases with
                    | nil => exact (nonempty installed).elim
                    | cons phase remaining => exact ⟨phase, remaining, rfl⟩
                  have inside : event ∈ phase.events := by
                    simpa only [PhaseRuntimeState.commandAllowed, installed, List.head?_cons,
                      Option.any_some, decide_eq_true_eq] using allowed
                  have bounds := (phase.mem_events event).mp inside
                  have typed := phase.fields event bounds.1 bounds.2
                  have kind : phase.kind = .sample := by
                    cases kind : phase.kind with
                    | sample => rfl
                    | commitment =>
                        rw [kind] at typed
                        obtain ⟨owner, ty, impossible⟩ := typed
                        cases impossible.symm.trans output
                    | reveal =>
                        rw [kind] at typed
                        obtain ⟨ty, impossible⟩ := typed
                        cases impossible.symm.trans output
                  exact sourceReplay_sample_command_interval_mass setup implementation current next
                    first last live phase remaining installed kind event ready allowed moved
                      retained
            · have kernel := environmentStep_executeSample_of_not_ready implementation.runtime
                current.application.current.native event ready
              exact sourceReplay_stuttering_sample_interval_mass setup implementation current next
                first last live nonempty event allowed kernel moved retained
          · exact sourceReplay_disallowed_sample_interval_mass setup implementation current next
              first last event (Bool.eq_false_iff.mpr allowed) moved retained

private theorem sourceReplay_native_step_some
    {before after : (nativeProtocol).State}
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support) :
    ∃ current, after = some current := by
  cases before with
  | none =>
      obtain ⟨physical, _supported, same⟩ := (PMF.mem_support_map_iff ..).mp moved
      exact ⟨_, same.symm⟩
  | some current =>
      rcases current with ⟨remaining, actor, execution⟩
      cases actor with
      | some owner =>
          change after ∈ (PMF.pure (some
            { remaining := remaining, actor := none,
              execution := execution.respond nativeApplication owner ((joint owner).getD ⟨none⟩) })
              : PMF (nativeProtocol).State).support at moved
          cases (PMF.mem_support_pure_iff _ _).mp moved
          exact ⟨_, rfl⟩
      | none =>
          cases remaining with
          | zero =>
              change after ∈ (PMF.pure (some ⟨0, none, execution⟩) :
                PMF (nativeProtocol).State).support at moved
              cases (PMF.mem_support_pure_iff _ _).mp moved
              exact ⟨_, rfl⟩
          | succ remaining =>
              change after ∈ ((implementation.scheduler execution.environmentRecall
                (execution.observeEnvironment nativeApplication)).bind fun command =>
                  (execution.environmentStep nativeApplication command).map fun next =>
                    some (⟨remaining, command.actor? nativeApplication, next⟩ :
                      (nativeApplication).Control)).support at moved
              obtain ⟨command, _chosen, supported⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
              obtain ⟨next, _advanced, same⟩ := (PMF.mem_support_map_iff ..).mp supported
              exact ⟨_, same.symm⟩

private theorem sourceReplay_native_none_trace
    (trace : (nativeProtocol).Trace none) : trace = .start := by
  have unique : ∀ {state : (nativeProtocol).State} (history : (nativeProtocol).Trace state),
      state = none → HEq history (Trace.start : (nativeProtocol).Trace (nativeProtocol).init) := by
    intro state history stateEq
    cases history with
    | start => rfl
    | extend prior joint legal moved =>
        obtain ⟨current, present⟩ := sourceReplay_native_step_some setup implementation
          joint legal moved
        rw [stateEq] at present
        cases present
  exact eq_of_heq (unique trace rfl)

private theorem sourceReplay_native_live
    (current : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some current)) : current.execution.application.Live := by
  have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have living := (phaseApplication_live implementation.runtime implementation.leaks).history
    nativeInitial implementation.horizon implementation.scheduler
      (fun (state : PhaseRuntimeState (serviceGraph setup .concurrent)) supported => by
      change state ∈ (setup.initialLaw.map fun draw =>
        PhaseRuntimeState.initial implementation.plan (encodeInputs draw)).support at supported
      obtain ⟨inputs, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
      exact ⟨PhaseRuntimeState.initial_frontier implementation.plan _,
        PhaseRuntimeState.initial_live implementation.plan _⟩) raw
  exact living.2

/-- The actual selected source chronology retains the whole correlated
initializer and every original public Nature atom. -/
theorem sourceReplay_nature_mass_eq_canonical
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) :
    sourceReplayNatureMass setup implementation trace =
      (canonicalSource setup implementation operational ⟨_, trace⟩).trace.transitionMass := by
  have semantic : ∀ {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state),
      match state, checkpointSelection setup implementation operational trace with
      | none, _ => sourceReplayNatureMass setup implementation trace = 1
      | some _, selected => sourceReplayNatureMass setup implementation trace =
          selected.val.checkpoint.trace.transitionMass := by
    intro state trace
    induction trace with
    | start => rfl
    | @extend before after prior joint legal moved ih =>
        obtain ⟨ending, rfl⟩ := sourceReplay_native_step_some setup implementation joint legal moved
        cases before with
        | none =>
            cases sourceReplay_native_none_trace setup implementation prior
            have sourceStart := sourceReplay_initial_nature_mass setup implementation operational
              ending joint legal moved
            simpa only [canonicalSource, sourceReplay_lift_mass] using sourceStart
        | some current =>
            let first := (checkpointSelection setup implementation operational prior).val
            let last := (checkpointSelection setup implementation operational
              (prior.extend joint legal moved)).val
            have retained := checkpointSelection_prefix setup implementation operational current
              ending prior (prior.extend joint legal moved) (.extend .refl joint legal moved)
            change sourceReplayNatureMass setup implementation prior =
              first.checkpoint.trace.transitionMass at ih
            change sourceReplayNatureMass setup implementation prior *
              (sourceReplayNatureStepAtom setup implementation (some current)
                (some ending)).toReal =
                last.checkpoint.trace.transitionMass
            rw [ih]
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some owner =>
                change some ending ∈ (PMF.pure (some
                  { remaining := remaining, actor := none,
                    execution := execution.respond nativeApplication owner
                      ((joint owner).getD ⟨none⟩) }) : PMF (nativeProtocol).State).support at moved
                cases (PMF.mem_support_pure_iff _ _).mp moved
                have same : execution.application.attempt =
                    (execution.respond nativeApplication owner
                      ((joint owner).getD ⟨none⟩)).application.attempt := by
                  cases (joint owner).getD ⟨none⟩ with
                  | mk transmission => cases transmission <;> rfl
                have mass := sourceReplay_same_attempt_interval_mass setup first.checkpoint
                  last.checkpoint same retained
                simpa only [sourceReplayNatureStepAtom, ENNReal.toReal_one, mul_one] using mass.symm
            | none =>
                cases remaining with
                | zero =>
                    change some ending ∈ (PMF.pure (some ⟨0, none, execution⟩) :
                      PMF (nativeProtocol).State).support at moved
                    cases (PMF.mem_support_pure_iff _ _).mp moved
                    have mass := sourceReplay_same_attempt_interval_mass setup first.checkpoint
                      last.checkpoint rfl retained
                    simpa only [sourceReplayNatureStepAtom, ↓reduceIte, ENNReal.toReal_one,
                      mul_one] using mass.symm
                | succ remaining =>
                    change some ending ∈ ((implementation.scheduler execution.environmentRecall
                      (execution.observeEnvironment nativeApplication)).bind fun command =>
                        (execution.environmentStep nativeApplication command).map fun next =>
                          some (⟨remaining, command.actor? nativeApplication, next⟩ :
                            (nativeApplication).Control)).support at moved
                    obtain ⟨command, _chosen, supported⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
                    obtain ⟨next, advanced, same⟩ := (PMF.mem_support_map_iff ..).mp supported
                    cases Option.some.inj same
                    have living := sourceReplay_native_live setup implementation _ prior
                    have mass := sourceReplay_environment_interval_mass setup implementation
                      operational execution next first last living command advanced retained
                    have recorded := (nativeApplication).environmentStep_environmentRecall
                      execution next command advanced
                    have latest : next.environmentRecall.getLast? =
                        some ⟨execution.observeEnvironment nativeApplication, command⟩ := by
                      rw [recorded, List.getLast?_concat]
                    simpa only [sourceReplayNatureStepAtom, Nat.succ_ne_zero, ↓reduceIte, latest]
                      using mass.symm
  change sourceReplayNatureMass setup implementation trace =
    (setup.proposalRecoveryLiftTrace _
      (checkpointSelection setup implementation operational trace).val.checkpoint.trace
      ).transitionMass
  rw [sourceReplay_lift_mass]
  exact semantic trace

def sourceReplayResponseProducts (rates : PhaseProposalRates) (who : Player) :
    ∀ {state : (nativeProtocol).State}, (nativeProtocol).Trace state → ℝ × ℝ × ℝ
  | _, .start => (1, 1, 1)
  | _, @Trace.extend _ _ before _ prior joint _ _ =>
      let previous := sourceReplayResponseProducts rates who prior
      let extra : ℝ × ℝ := match before with
        | none => (1, 1)
        | some control => match control.actor with
          | none => (1, 1)
          | some owner => if owner = who then (1, 1) else match joint owner with
            | none => (0, 0)
            | some action =>
              ((sourceReplayBindingDrawAtom setup values implementation owner
                (control.execution.recall owner)
                (control.execution.observe nativeApplication owner) action).toReal,
                (sourceReplayAliasAtom setup implementation rates.aliases owner
                  control.execution (none, some action)).toReal)
      (previous.1 * (sourceReplayPacketStepAtom setup implementation rates who before joint).toReal,
        previous.2.1 * extra.1, previous.2.2 * extra.2)

private theorem sourceReplayResponseProducts_mechanical_extend
    (rates : PhaseProposalRates) (who : Player)
    {before after : (nativeProtocol).State} (prior : (nativeProtocol).Trace before)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support) :
    (sourceReplayResponseProducts setup values implementation rates who
      (prior.extend joint legal moved)).1 =
        (sourceReplayResponseProducts setup values implementation rates who prior).1 *
          (sourceReplayPacketStepAtom setup implementation rates who before joint).toReal := rfl

/-- The literal finite packet product is strictly positive on every actual
counted trace. Subsequent atom cancellation therefore uses no zero convention. -/
private theorem sourceReplay_mechanical_product_positive
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (who : Player) {state : (nativeProtocol).State}
    (trace : (nativeProtocol).Trace state) :
    0 < (sourceReplayResponseProducts setup values implementation rates who trace).1 := by
  induction trace with
  | start => exact zero_lt_one
  | @extend before after prior joint legal moved ih =>
      rw [sourceReplayResponseProducts_mechanical_extend]
      apply mul_pos ih
      cases before with
      | none => exact zero_lt_one
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | none => exact zero_lt_one
          | some owner =>
              by_cases same : owner = who
              · simp only [sourceReplayPacketStepAtom, same, ↓reduceIte, ENNReal.toReal_one,
                  zero_lt_one]
              · obtain ⟨response, selected, available⟩ :
                    ∃ response : (nativeApplication).Action, joint owner = some response ∧
                      response ∈ PhaseCount.onePacketActions implementation.runtime
                        implementation.leaks implementation.bounds owner (execution.recall owner)
                          (execution.observe nativeApplication owner) := by
                  have offered := legal.2 owner
                  cases chosen : joint owner with
                  | none => rw [chosen] at offered; exact (offered rfl).elim
                  | some response => exact ⟨response, rfl, (chosen ▸ offered).2⟩
                simpa only [sourceReplayPacketStepAtom, same, ↓reduceIte, selected] using
                  sourceReplay_foreign_packet_positive setup values implementation operational
                    fullValues rates waitPositive waitBelow slotPositive badPositive badBelow
                      remaining owner execution prior response available

/-- The actual foreign response product separates every proper queried draw
and every raw alias from the physical packet product. Historical focal BAD
remains in the focal policy and imposes no extra goodness condition. -/
private theorem sourceReplay_foreign_response_products
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (who : Player) {state : (nativeProtocol).State}
    (trace : (nativeProtocol).Trace state)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨state, trace⟩) :
    (∏ owner ∈ Finset.univ.erase who,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlayReachProbability
          (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
            implementation.leaks implementation.bounds implementation.plan nativeInitial
              implementation.horizon implementation.scheduler values rates owner)
          (((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).ownPlay owner trace)) =
      (sourceReplayResponseProducts setup values implementation rates who trace).1 *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.1 *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.2 := by
  classical
  let model := (nativeMenu).information nativeInitial implementation.horizon
    implementation.scheduler
  let profile := phaseProposalReferenceStrategy setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan nativeInitial
      implementation.horizon implementation.scheduler values rates
  let own := fun {state} (history : (nativeProtocol).Trace state) owner =>
    model.ownPlayReachProbability (profile owner) (model.ownPlay owner history)
  change (∏ owner ∈ Finset.univ.erase who, own trace owner) = _
  revert foreign
  induction trace with
  | start =>
      intro _foreign
      change (∏ _owner ∈ Finset.univ.erase who, (1 : ℝ)) = 1 * 1 * 1
      simp only [Finset.prod_const_one, mul_one]
  | @extend before after prior joint legal moved ih =>
      intro foreign
      have earlierGood : ∀ owner, owner ≠ who →
          ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
            implementation.leaks implementation.bounds nativeInitial implementation.horizon
              implementation.scheduler owner ⟨before, prior⟩ := by
        intro owner different unusable
        obtain ⟨record, member, bad⟩ := unusable
        have retained : TracePrefix prior (prior.extend joint legal moved) :=
          .extend .refl joint legal moved
        exact foreign owner different ⟨record,
          (model.ownPlay_isSuffix_of_reachesWithin owner retained.reachesWithin).subset member,
          bad⟩
      have previous := ih earlierGood
      let weight := fun owner => match joint owner with
        | none => (1 : ℝ)
        | some action => (((profile owner (model.infoOf owner prior)).map Subtype.val)
            (some action)).toReal
      have update (owner : Player) : own (prior.extend joint legal moved) owner =
          own prior owner * weight owner := by
        dsimp only [own]
        rw [InfoSignals.ownPlay_extend]
        cases selected : joint owner with
        | none => simp only [selected, weight, mul_one]
        | some action =>
            simp only [selected, weight, InformationModel.ownPlayReachProbability]
            ring
      have product : (∏ owner ∈ Finset.univ.erase who,
          own (prior.extend joint legal moved) owner) =
            (∏ owner ∈ Finset.univ.erase who, own prior owner) *
              ∏ owner ∈ Finset.univ.erase who, weight owner := by
        calc
          _ = ∏ owner ∈ Finset.univ.erase who, own prior owner * weight owner :=
            Finset.prod_congr rfl fun owner _member => update owner
          _ = _ := Finset.prod_mul_distrib
      rw [product, previous]
      cases before with
      | none =>
          have silent (owner : Player) : joint owner = none := by
            cases selected : joint owner with
            | none => rfl
            | some action =>
                have active := (selected ▸ legal.2 owner).1
                change none = some owner at active
                cases active
          simp only [weight, silent, Finset.prod_const_one, sourceReplayResponseProducts,
            sourceReplayPacketStepAtom, ENNReal.toReal_one, mul_one]
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | none =>
              have silent (owner : Player) : joint owner = none := by
                cases selected : joint owner with
                | none => rfl
                | some action =>
                    have active := (selected ▸ legal.2 owner).1
                    change none = some owner at active
                    cases active
              simp only [weight, silent, Finset.prod_const_one, sourceReplayResponseProducts,
                sourceReplayPacketStepAtom, ENNReal.toReal_one, mul_one]
          | some owner =>
              have silent (other : Player) (different : other ≠ owner) : joint other = none := by
                cases selected : joint other with
                | none => rfl
                | some action =>
                    have active := (selected ▸ legal.2 other).1
                    change some owner = some other at active
                    exact (different (Option.some.inj active).symm).elim
              by_cases focal : owner = who
              · subst owner
                have weights : (∏ owner ∈ Finset.univ.erase who, weight owner) = 1 := by
                  apply Finset.prod_eq_one
                  intro owner member
                  simp only [weight, silent owner (Finset.mem_erase.mp member).1]
                rw [weights]
                simp only [sourceReplayResponseProducts, sourceReplayPacketStepAtom,
                  ↓reduceIte, ENNReal.toReal_one, mul_one]
              · obtain ⟨action, selected, offered⟩ :
                    ∃ action : (nativeApplication).Action, joint owner = some action ∧
                      action ∈ PhaseCount.onePacketActions implementation.runtime
                        implementation.leaks implementation.bounds owner (execution.recall owner)
                          (execution.observe nativeApplication owner) := by
                  cases selected : joint owner with
                  | none =>
                      have inactive := selected ▸ legal.2 owner
                      exact (inactive rfl).elim
                  | some action => exact ⟨action, rfl, (selected ▸ legal.2 owner).2⟩
                let response : PhaseProposal.Response implementation.runtime implementation.leaks
                    implementation.bounds owner (execution.recall owner)
                      (execution.observe nativeApplication owner) := ⟨action, offered⟩
                have clean : ¬ PhaseProposal.GeneratedUnusableBindingAction
                    implementation.runtime implementation.leaks owner action := by
                  intro unusable
                  apply foreign owner focal
                  refine ⟨(model.infoOf owner prior, action), ?_, unusable⟩
                  rw [InfoSignals.ownPlay_extend, selected]
                  exact List.mem_cons_self
                have atom := sourceReplay_clean_callback_draw_atom setup values implementation
                  operational fullValues rates waitPositive waitBelow slotPositive badPositive
                    badBelow remaining owner execution prior response clean none
                have aliasAtom : sourceReplayAliasAtom setup implementation rates.aliases owner
                    execution (none, some action) =
                    sourceReplayAliases setup implementation rates.aliases owner execution none
                      (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                        implementation.bounds owner (execution.recall owner)
                          (execution.observe nativeApplication owner) response)
                        (none, some action) := by
                  simp only [sourceReplayAliasAtom, dite_eq_left offered]
                  rfl
                have row : phaseProposalReferencePolicy setup .concurrent implementation.runtime
                    implementation.leaks implementation.bounds implementation.plan values rates
                      owner (execution.recall owner) (execution.observe nativeApplication owner)
                        action =
                    foreignMechanicalAtom setup implementation rates execution owner action *
                      sourceReplayBindingDrawAtom setup values implementation owner
                        (execution.recall owner)
                        (execution.observe nativeApplication owner) action *
                      sourceReplayAliasAtom setup implementation rates.aliases owner execution
                        (none, some action) := by
                  rw [aliasAtom]
                  exact atom.2
                have rowReal := congrArg ENNReal.toReal row
                simp only [ENNReal.toReal_mul] at rowReal
                have information : model.infoOf owner prior =
                    some (execution.recall owner, execution.observe nativeApplication owner) := by
                  change ((nativeMenu).signals nativeInitial implementation.horizon
                    implementation.scheduler).infoOf owner prior = _
                  rw [(nativeMenu).info nativeInitial implementation.horizon
                    implementation.scheduler owner prior]
                  simp only [ReactiveApplication.observe, ↓reduceIte]
                have weightEq : weight owner =
                    (phaseProposalReferencePolicy setup .concurrent implementation.runtime
                      implementation.leaks implementation.bounds implementation.plan values rates
                        owner (execution.recall owner)
                          (execution.observe nativeApplication owner) action).toReal := by
                  dsimp only [weight]
                  simp only [selected]
                  rw [information, phaseProposalReferenceStrategy_map_val]
                  exact congrArg ENNReal.toReal
                    (pmf_map_apply_of_injective _ (Option.some_injective _) action)
                have weights : (∏ other ∈ Finset.univ.erase who, weight other) = weight owner := by
                  apply Finset.prod_eq_single owner
                  · intro other _member different
                    simp only [weight, silent other different]
                  · intro absent
                    exact (absent (Finset.mem_erase.mpr ⟨focal, Finset.mem_univ owner⟩)).elim
                rw [weights, weightEq, rowReal]
                simp only [sourceReplayResponseProducts, sourceReplayPacketStepAtom,
                  focal, ↓reduceIte, selected]
                ring

/-- On the actual trace, the fixed-tape transition factors and the foreign
packet factors are exactly public Nature times the existing mechanical path.
The whole initializer is retained once, before the first source row. -/
private theorem sourceReplay_mechanical_path_factor
    (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    sourceReplayFixedTransitionMass setup implementation tape trace *
        (sourceReplayResponseProducts setup values implementation rates who trace).1 =
      sourceReplayNatureMass setup implementation trace *
        (mechanicalPathAtom setup implementation rates who tape trace).toReal := by
  induction trace with
  | start =>
    simp only [sourceReplayFixedTransitionMass, sourceReplayResponseProducts,
      sourceReplayNatureMass, mechanicalPathAtom, ENNReal.toReal_one, mul_one]
  | @extend before after prior joint legal moved ih =>
    have row := congrArg ENNReal.toReal
      (sourceReplay_mechanical_step_factor setup implementation rates who tape joint legal moved)
    simp only [ENNReal.toReal_mul] at row
    rw [sourceReplayFixedTransitionMass, sourceReplayResponseProducts_mechanical_extend,
      sourceReplayNatureMass,
      mechanicalPathAtom, ENNReal.toReal_mul]
    calc
      _ = (sourceReplayFixedTransitionMass setup implementation tape prior *
          (sourceReplayResponseProducts setup values implementation rates who prior).1) *
            (((nativeApplication).transition nativeInitial implementation.horizon
              (ReservedEpoch.family implementation.runtime implementation.leaks
                (ReservedEpoch.packetCapacity implementation.runtime) tape) before joint after
                  ).toReal *
              (sourceReplayPacketStepAtom setup implementation rates who before joint).toReal) :=
                by ring
      _ = _ := by rw [ih, row]; ring

/-- The actual native atom separates scheduler/packet mechanics from public
Nature. The packet product is retained literally for the subsequent proper-draw
and alias partition; no division or zero-case convention is introduced. -/
private theorem sourceReplay_prescribed_mechanical_atom
    (operational : implementation.Operational)
    (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) :
    (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight
      (phaseProposalReferenceStrategy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan nativeInitial implementation.horizon
          implementation.scheduler values rates) ⟨some control, trace⟩).toReal *
        (prefixTapeLaw setup implementation ⟨some control, trace⟩ tape).toReal *
          (sourceReplayResponseProducts setup values implementation rates who trace).1 =
      (implementation.prior tape).toReal *
        (canonicalSource setup implementation operational
          ⟨some control, trace⟩).trace.transitionMass *
          (mechanicalPathAtom setup implementation rates who tape trace).toReal *
            ∏ owner, (((nativeApplication).privateTranscriptFrom []
              (control.execution.recall owner)).map (fun record =>
                phaseProposalReferencePolicy setup .concurrent implementation.runtime
                  implementation.leaks implementation.bounds implementation.plan values rates owner
                    record.1.1 record.1.2 record.2)).prod.toReal := by
  have native := sourceReplay_prescribed_native_atom setup values implementation rates tape
    control trace
  rw [native]
  calc
    _ = (implementation.prior tape).toReal *
        (sourceReplayFixedTransitionMass setup implementation tape trace *
          (sourceReplayResponseProducts setup values implementation rates who trace).1) *
            ∏ owner, (((nativeApplication).privateTranscriptFrom []
              (control.execution.recall owner)).map (fun record =>
                phaseProposalReferencePolicy setup .concurrent implementation.runtime
                  implementation.leaks implementation.bounds implementation.plan values rates owner
                    record.1.1 record.1.2 record.2)).prod.toReal := by ring
    _ = _ := by
      rw [sourceReplay_mechanical_path_factor setup values implementation rates who tape trace]
      rw [sourceReplay_nature_mass_eq_canonical setup implementation operational control trace]
      ring

/-- The original native and tape atom retains the whole initializer once,
the selected source Nature mass, and every actual queried draw and alias.
Only the original focal owner's raw policy remains unsplit. -/
theorem sourceReplay_prescribed_response_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (who : Player) (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩) :
    (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight
      (phaseProposalReferenceStrategy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan nativeInitial implementation.horizon
          implementation.scheduler values rates) ⟨some control, trace⟩).toReal *
        (prefixTapeLaw setup implementation ⟨some control, trace⟩ tape).toReal =
      (implementation.prior tape).toReal *
        (canonicalSource setup implementation operational
          ⟨some control, trace⟩).trace.transitionMass *
          (mechanicalPathAtom setup implementation rates who tape trace).toReal *
            ((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).ownPlayReachProbability
                (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
                  implementation.leaks implementation.bounds implementation.plan nativeInitial
                    implementation.horizon implementation.scheduler values rates who)
                (((nativeMenu).information nativeInitial implementation.horizon
                  implementation.scheduler).ownPlay who trace) *
            (sourceReplayResponseProducts setup values implementation rates who trace).2.1 *
            (sourceReplayResponseProducts setup values implementation rates who trace).2.2 := by
  classical
  let responseProduct := fun owner =>
    (((nativeApplication).privateTranscriptFrom [] (control.execution.recall owner)).map
      (fun record => phaseProposalReferencePolicy setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan values rates owner
          record.1.1 record.1.2 record.2)).prod.toReal
  have splitProduct : (∏ owner, responseProduct owner) =
      responseProduct who * ∏ owner ∈ Finset.univ.erase who, responseProduct owner :=
    (Finset.mul_prod_erase Finset.univ responseProduct (Finset.mem_univ who)).symm
  have foreignProduct : (∏ owner ∈ Finset.univ.erase who, responseProduct owner) =
      (sourceReplayResponseProducts setup values implementation rates who trace).1 *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.1 *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.2 := by
    simpa only [sourceReplay_prescribed_own_atom setup values implementation rates] using
      sourceReplay_foreign_response_products setup values implementation operational fullValues
        rates waitPositive waitBelow slotPositive badPositive badBelow who trace foreign
  have focal := sourceReplay_prescribed_own_atom setup values implementation rates who control trace
  change _ = responseProduct who at focal
  rw [sourceReplay_prescribed_native_atom setup values implementation rates tape control trace]
  change (implementation.prior tape).toReal *
    sourceReplayFixedTransitionMass setup implementation tape trace *
      (∏ owner, responseProduct owner) = _
  rw [splitProduct, foreignProduct, ← focal]
  calc
    _ = (implementation.prior tape).toReal *
        (sourceReplayFixedTransitionMass setup implementation tape trace *
          (sourceReplayResponseProducts setup values implementation rates who trace).1) *
        ((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).ownPlayReachProbability
            (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
              implementation.leaks implementation.bounds implementation.plan nativeInitial
                implementation.horizon implementation.scheduler values rates who)
            (((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).ownPlay who trace) *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.1 *
        (sourceReplayResponseProducts setup values implementation rates who trace).2.2 := by ring
    _ = _ := by
      rw [sourceReplay_mechanical_path_factor setup values implementation rates who tape trace,
        sourceReplay_nature_mass_eq_canonical setup implementation operational control trace]
      ring

local notation "nativeModel" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
  implementation.initial implementation.horizon implementation.scheduler

open Classical in
/-- A positive qualified native anchor has a nonzero literal mechanical
coefficient. Both the original tape atom and every mechanical path factor
are recovered from the actual native atom, without a quotient. -/
private theorem sourceReplay_mechanicalCoefficient_ne_zero
    (operational : implementation.Operational)
    (scale nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (who : Player) (site : (nativeModel).InformationSite who)
    (event : (serviceGraph setup .concurrent).EventId)
    (index : MechanicalIndex setup implementation who)
    (history : (nativeModel).InformationHistory who site.1)
    (sameWord : mechanicalWord setup implementation who history.val.trace = index.1.val)
    (reached : (nativeModel).historyReachWeight nativeProfile history.val ≠ 0)
    (tapeSupported : prefixTapeLaw setup implementation history.val index.2 ≠ 0)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          history.val)
    (alive : history.val.state.elim True (fun control =>
      who ∉ control.execution.application.current.excluded))
    (admitted : bindingAdmissionBit setup implementation who event history.val index.2 = true) :
    mechanicalCoefficient setup implementation ⟨nativeBad, scale, scale, scale⟩ nativeProfile
      who site event index ≠ 0 := by
  have anchor := mechanicalCoefficient_eq_of_anchor setup values implementation operational
    scale nativeBad scalePositive scaleBelow nativeBadPositive nativeBadBelow fullValues
      nativeProfile nativePrescribed who site event index history sameWord reached tapeSupported
        foreign alive admitted
  rw [anchor]
  have reachedReal := ENNReal.toReal_pos reached
    ((nativeModel).historyReachWeight_ne_top nativeProfile history.val)
  have ownPositive : 0 < (nativeModel).ownPlayReachProbability (nativeProfile who)
      ((nativeModel).ownPlay who history.val.trace) := by
    rw [(nativeModel).historyReachProbability_eq_player_mul_counterfactual nativeProfile who
      history.val.trace, (nativeModel).playerReachProbability_eq_ownPlayReachProbability]
      at reachedReal
    exact pos_of_mul_pos_left reachedReal
      ((nativeModel).counterfactualReachProbability_nonneg nativeProfile who history.val.trace)
  have ownNonzero := (ENNReal.ofReal_pos.mpr ownPositive).ne'
  rcases history with ⟨⟨state, trace⟩, _information⟩
  cases state with
  | none => simp only [bindingAdmissionBit, Bool.false_eq_true] at admitted
  | some control =>
      have tapeReal := ENNReal.toReal_pos tapeSupported (PMF.apply_ne_top _ _)
      have packet := sourceReplay_mechanical_product_positive setup values implementation
        operational fullValues ⟨nativeBad, scale, scale, scale⟩ scalePositive scaleBelow
          scalePositive nativeBadPositive nativeBadBelow who trace
      have atom := sourceReplay_prescribed_mechanical_atom setup values implementation
        operational ⟨nativeBad, scale, scale, scale⟩ who index.2 control trace
      rw [← nativePrescribed] at atom
      have nonzero : (implementation.prior index.2).toReal *
          (canonicalSource setup implementation operational
            ⟨some control, trace⟩).trace.transitionMass *
          (mechanicalPathAtom setup implementation ⟨nativeBad, scale, scale, scale⟩ who
            index.2 trace).toReal *
          ∏ owner, (((nativeApplication).privateTranscriptFrom []
            (control.execution.recall owner)).map (fun record =>
              phaseProposalReferencePolicy setup .concurrent implementation.runtime
                implementation.leaks implementation.bounds implementation.plan values
                ⟨nativeBad, scale, scale, scale⟩ owner record.1.1 record.1.2 record.2)).prod.toReal
            ≠ 0 := by
        rw [← atom]
        exact (mul_pos (mul_pos reachedReal tapeReal) packet).ne'
      have first := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp nonzero).1)
      have priorReal := (mul_ne_zero_iff.mp first.1).1
      have pathReal := first.2
      have priorNonzero : implementation.prior index.2 ≠ 0 := by
        intro zero
        exact priorReal (by rw [zero, ENNReal.toReal_zero])
      have pathNonzero : mechanicalPathAtom setup implementation
          ⟨nativeBad, scale, scale, scale⟩ who index.2 trace ≠ 0 := by
        intro zero
        exact pathReal (by rw [zero, ENNReal.toReal_zero])
      exact mul_ne_zero (mul_ne_zero priorNonzero ownNonzero) pathNonzero

open Classical in
/-- A zero mechanical coefficient has no positive original annotated atom.
This includes every posterior entry and complete issued word, before any
source or mechanical factor is canceled. -/
theorem annotated_forced_block_zero_of_coefficient_zero
    (operational : implementation.Operational)
    (scale nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (who : Player) (site : (nativeModel).InformationSite who)
    (index : MechanicalIndex setup implementation who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (value : L.Val payload) (cut completed : setup.proposalRecoveryProtocol.History)
    (zero : mechanicalCoefficient setup implementation ⟨nativeBad, scale, scale, scale⟩
      nativeProfile who site event index = 0) :
    annotatedForcedBlockWeight setup values implementation operational sourceProfile nativeProfile
      who site index event payload value cut completed = 0 := by
  unfold annotatedForcedBlockWeight
  apply ENNReal.tsum_eq_zero.mpr
  intro history
  by_cases mechanical : mechanicalWord setup implementation who history.val.trace = index.1.val
  · rw [ite_eq_left mechanical]
    apply ENNReal.tsum_eq_zero.mpr
    intro entry
    apply ENNReal.tsum_eq_zero.mpr
    intro word
    by_contra positive
    have prefixWeight := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).1
    have admission := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp positive).1).2
    have admitted : bindingAdmissionBit setup implementation who event history.val index.2 =
        true := by
      cases chosen : bindingAdmissionBit setup implementation who event history.val index.2
      · simp only [chosen, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false] at admission
      · rfl
    unfold annotatedPrefixWeight at prefixWeight
    dsimp only at prefixWeight
    obtain ⟨weights, qualified⟩ := mul_ne_zero_iff.mp prefixWeight
    obtain ⟨reached, tapeSupported⟩ := mul_ne_zero_iff.mp weights
    have good : (∀ owner, owner ≠ who →
        ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
            implementation.scheduler owner history.val) ∧
        history.val.state.elim True (fun control =>
          who ∉ control.execution.application.current.excluded) := by
      by_contra bad
      rw [ite_eq_right bad] at qualified
      exact qualified rfl
    exact sourceReplay_mechanicalCoefficient_ne_zero setup values implementation operational
      scale nativeBad scalePositive scaleBelow nativeBadPositive nativeBadBelow fullValues
        nativeProfile nativePrescribed who site event index history mechanical reached tapeSupported
          good.1 good.2 admitted zero
  · exact ite_eq_right mechanical


-- BEGIN CURRENT ISSUED QUERY PRODUCT

/-- Every literal recalled binding emission is its first fresh registration.
The signed attempt is retained, including historical canceled attempts. -/
theorem sourceReplay_recorded_binding_registration
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (owner : Player) (record : (nativeApplication).PlayerEntry)
    (recorded : record ∈ control.execution.recall owner)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (emitted : record.emitted = some message)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent))
    (call : message.payload.packet.call = .commitment event handle) :
    ∃ (serial : Nat) (opening : Option (Raw L))
      (evidence : EvidenceRequest (serviceGraph setup .concurrent)),
      handle = (owner, .prepared serial) ∧ message.sender = owner ∧
      record.action = ⟨some
        ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ ∧
      record.beforeView.application.1.candidates (.prepared serial) = .fresh ∧
      record.beforeView.application.2.attempt = message.payload.attempt ∧
      control.execution.application.current.native.bindingResult handle payload =
        (opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success := by
  have output : message ∈ (nativeApplication).outputs (control.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
  have recalled := (nativeApplication).history_inputRecall nativeInitial implementation.horizon
    implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler trace) owner
  have input : message ∈ control.execution.network.inputs := by
    rw [← recalled] at output
    exact (List.mem_filter.mp output).1
  obtain ⟨serial, opening, evidence, original, handleEq, sender, member, sent, action,
    fresh, signed, result⟩ := issued_binding_record setup implementation control trace owner event
      payload shape handle message input call
  have same : original = record := recorded_emission_unique setup implementation trace owner
    original record member recorded message sent emitted
  subst original
  exact ⟨serial, opening, evidence, handleEq, sender, action, fresh, signed, result⟩

/-- An earlier own recall retains precisely the same original registering
records for its issued packets. Authentic emissions transfer the final ledger. -/
private theorem sourceReplay_issued_ledger_prefix
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low high : Nat)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (before : (nativeApplication).Control) (owner : Player)
    (past : before.execution.recall owner ⊆ control.execution.recall owner)
    (signed : before.execution.application.attempt = control.execution.application.attempt)
    (word : DecisionView owner Δ)
    (retained : issuedLedger setup implementation block low control high owner word) :
    issuedLedger setup implementation block low before high owner word := by
  intro named payload shape candidate message emitted current call interval
  obtain ⟨record, member, sent⟩ := List.mem_filterMap.mp emitted
  have finalEmitted : message ∈ (nativeApplication).outputs (control.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨record, past member, sent⟩
  obtain ⟨serial, opening, evidence, registered, slot, registeredMember, registeredSent,
    action, fresh, result⟩ := retained named payload shape candidate message finalEmitted
      (current.trans signed) call interval
  have same : registered = record := recorded_emission_unique setup implementation trace owner
    registered record registeredMember (past member) message registeredSent sent
  subst registered
  exact ⟨serial, opening, evidence, record, slot, member, sent, action, fresh, result⟩

open Classical in
/-- At a literal earlier callback, the final recall observation is exactly
its then-issued owner ledger. The signed attempt is retained explicitly. -/
private theorem sourceReplay_issued_callback_observation
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (control before : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before)) (owner : Player) (count : Nat)
    (past : before.execution.recall owner = (control.execution.recall owner).take count)
    (signed : before.execution.application.attempt = control.execution.application.attempt)
    (reference word : DecisionView owner Δ)
    (retained : issuedLedger setup implementation block low before (low + block.length)
      owner reference) :
    sourceIssuedOwnObservation setup implementation block low control owner reference count word ↔
      issuedLedger setup implementation block low before (low + block.length) owner word := by
  have ledger := issuedLedger_iff_recalled_word_actions setup implementation block suffix
    embedding low rank actions prior owner reference word retained
  simpa only [sourceIssuedOwnObservation, List.take_length, past,
    sourceIssuedRecordPosition, signed] using ledger.symm

open Classical in
/-- A proper literal preparation contributes its typed queried value atom.
The opening and query refer to this callback's actual earlier input. -/
private theorem sourceReplay_prepared_binding_draw
    (owner : Player) (past : List (nativeApplication).PlayerEntry)
    (view : (nativeApplication).PlayerView)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (serial : Nat) (opening : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup .concurrent))
    (value : L.Val payload) (decoded : opening.bind (fun raw => raw.as? payload) = some value)
    (key : setup.ProposalRecoveryComponent owner)
    (query : phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
      implementation.plan owner event past view = some key) :
    sourceReplayBindingDrawAtom setup values implementation owner past view
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ =
      ((values owner key).map (fun sampled => phaseRecoveryDomainValue setup .concurrent event
        owner payload shape sampled.val.val)) value := by
  simp only [sourceReplayBindingDrawAtom, PhaseProposal.bindingPreparation, shape, decoded,
    Option.map_some, dite_eq_left, query]

/-- Every literal foreign recall occurrence comes from the corresponding
supported sequential callback, with its original and actual input retained. -/
theorem sourceReplay_recorded_foreign_callback
    (scale : Set.Icc (0 : ℝ) 1) (who : Player)
    (target : setup.proposalRecoveryProtocol.History) (reference : (nativeApplication).Control)
    (endpoint actualEndpoint original : (nativeProtocol).History)
    (script : List (RawReplayChoice setup implementation)) (mass : ℝ≥0∞)
    (supported : SourceReplayScriptMass (setup := setup) (values := values)
      (implementation := implementation) scale who target reference original script mass)
    (onward : TracePrefix original.trace endpoint.trace)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (replayed : sourceRawReplay setup implementation who target reference original script =
      some ⟨some control, trace⟩)
    (actualOnward : TracePrefix trace actualEndpoint.trace)
    (owner : Player) (foreign : owner ≠ who) (index : Nat)
    (inside : index < (control.execution.recall owner).length)
    (currentRelated : RawReplayState setup implementation who target reference
      (rawReplayLost setup implementation script) original ⟨some control, trace⟩)
    (currentRestricted : SourceReplayLostRestricted setup implementation target reference who
      (rawReplayLost setup implementation script)) :
    ∃ (before after : (nativeApplication).Control)
      (prior : (nativeProtocol).Trace (some before))
      (joint : Player → Option (nativeApplication).Action)
      (legal : (nativeProtocol).Legal (some before) joint)
      (moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
      (earlier : List (RawReplayChoice setup implementation)) (earlierMass : ℝ≥0∞)
      (actualBefore : (nativeApplication).Control)
      (actualPrior : (nativeProtocol).Trace (some actualBefore))
      (actualAfter : (nativeProtocol).History)
      (kernel : PMF (RawReplayChoice setup implementation))
      (choice : RawReplayChoice setup implementation),
      TracePrefix (prior.extend joint legal moved) endpoint.trace ∧
      TracePrefix actualPrior actualEndpoint.trace ∧ before.actor = some owner ∧
      SourceReplayScriptMass (setup := setup) (values := values)
        (implementation := implementation) scale who target reference
          ⟨some before, prior⟩ earlier earlierMass ∧
      sourceRawReplay setup implementation who target reference ⟨some before, prior⟩ earlier =
        some ⟨some actualBefore, actualPrior⟩ ∧
      RawReplayState setup implementation who target reference
        (rawReplayLost setup implementation earlier) ⟨some before, prior⟩
          ⟨some actualBefore, actualPrior⟩ ∧
      SourceReplayLostRestricted setup implementation target reference who
        (rawReplayLost setup implementation earlier) ∧
      sourceRawReplay setup implementation who target reference
        ⟨some after, prior.extend joint legal moved⟩ (choice :: earlier) = some actualAfter ∧
      TracePrefix actualAfter.trace actualEndpoint.trace ∧
      RawReplayState setup implementation who target reference
        (rawReplayLost setup implementation (choice :: earlier))
          ⟨some after, prior.extend joint legal moved⟩ actualAfter ∧
      SourceReplayLostRestricted setup implementation target reference who
        (rawReplayLost setup implementation (choice :: earlier)) ∧
      SourceReplayCallbackAtoms (setup := setup) (values := values)
        (implementation := implementation) scale owner actualBefore.execution target reference
          ((joint owner).getD ⟨none⟩) kernel ∧
      SourceReplayCallbackLaw (setup := setup) (values := values)
        (implementation := implementation) scale owner actualBefore.execution target reference
          kernel ∧ choice ∈ kernel.support ∧
      choice.2 = some (control.execution.recall owner)[index].action ∧
      actualBefore.execution.recall owner = (control.execution.recall owner).take index ∧
      (control.execution.recall owner)[index].beforeView =
        actualBefore.execution.observe nativeApplication owner := by
  classical
  have priorKept (history : (nativeProtocol).History) :
      TracePrefix history.prior.trace history.trace := by
    rcases history with ⟨state, historyTrace⟩
    cases historyTrace with
    | start => exact .refl
    | extend earlier joint legal moved => exact .extend .refl joint legal moved
  revert currentRelated currentRestricted
  induction supported generalizing control trace index with
  | start =>
      intro _currentRelated _currentRestricted
      simp only [sourceRawReplay] at replayed
      have state := congrArg (fun history : (nativeProtocol).History => history.state)
        (Option.some.inj replayed)
      cases state
  | @deterministic before after prior joint legal moved script mass quiet priorActual
      priorReplay priorRelated priorRestricted earlier ih =>
      intro _currentRelated _currentRestricted
      obtain ⟨previous, previousReplay, priorEq⟩ := sourceRawReplay_step_prior setup implementation
        who target reference prior joint legal moved (none, none) script
          ⟨some control, trace⟩ replayed
      have previousSame : previous = priorActual :=
        Option.some.inj (previousReplay.symm.trans priorReplay)
      have previousRelated : RawReplayState setup implementation who target reference
          (rawReplayLost setup implementation script) ⟨before, prior⟩ previous := by
        rw [previousSame]
        exact priorRelated
      have actualPreviousKept : TracePrefix previous.trace actualEndpoint.trace := by
        have kept := (priorKept ⟨some control, trace⟩).trans actualOnward
        rw [priorEq] at kept
        exact kept
      have previousKept : TracePrefix prior endpoint.trace :=
        (TracePrefix.extend (TracePrefix.refl (prefixTrace := prior)) joint legal moved).trans
          onward
      rw [sourceRawReplay, previousReplay, Option.bind_some] at replayed
      cases before with
      | none =>
          cases state : target.state with
          | none => simp only [state] at replayed; cases replayed
          | some current =>
              simp only [state] at replayed
              have stateEq := (sourceReplayAppend_prior_state setup implementation previous
                ⟨some control, trace⟩ _ _ replayed).2
              have controlEq := Option.some.inj stateEq
              have empty : control.execution.recall owner = [] :=
                congrArg (fun current : (nativeApplication).Control =>
                  current.execution.recall owner) controlEq
              simp only [empty, List.length_nil] at inside
              omega
      | some originalBefore =>
          cases acting : originalBefore.actor with
          | none =>
              simp only [acting] at replayed
              rcases previous with ⟨previousState, previousTrace⟩
              cases previousState with
              | none => cases replayed
              | some actualBefore =>
                  cases after with
                  | none => cases replayed
                  | some ending =>
                      have stateEq := (sourceReplayAppend_prior_state setup implementation
                        ⟨some actualBefore, previousTrace⟩ ⟨some control, trace⟩ _ _ replayed).2
                      have controlEq := Option.some.inj stateEq
                      have recallEq : control.execution.recall owner =
                          actualBefore.execution.recall owner := by
                        rw [controlEq]
                        rfl
                      simpa only [recallEq] using ih previousKept actualBefore previousTrace
                        previousReplay actualPreviousKept index (by
                          simpa only [recallEq] using inside) previousRelated priorRestricted
          | some responder =>
              have responderEq : responder = who := by
                rcases quiet with quiet | quiet
                · simp only [ReactiveApplication.actor, Option.bind_some, acting] at quiet
                  cases quiet
                · simpa only [ReactiveApplication.actor, Option.bind_some, acting,
                    Option.some.injEq] using quiet
              subst responder
              simp only [acting, ↓reduceIte] at replayed
              rcases previous with ⟨previousState, previousTrace⟩
              cases previousState with
              | none => cases replayed
              | some actualBefore =>
                  obtain ⟨action, _selected, appended⟩ := Option.bind_eq_some_iff.mp replayed
                  have stateEq := (sourceReplayAppend_prior_state setup implementation
                    ⟨some actualBefore, previousTrace⟩ ⟨some control, trace⟩ _ _ appended).2
                  have controlEq := Option.some.inj stateEq
                  have recallEq : control.execution.recall owner =
                      actualBefore.execution.recall owner := by
                    rw [controlEq]
                    exact (nativeApplication).respond_recall_other actualBefore.execution who
                      owner foreign action
                  simpa only [recallEq] using ih previousKept actualBefore previousTrace
                    previousReplay actualPreviousKept index (by simpa only [recallEq] using inside)
                      previousRelated priorRestricted
  | @foreign before after prior joint legal moved script mass responder different acting previous
      previousTrace previousReplay related restricted kernel atoms description choice member earlier
      ih =>
      intro currentRelated currentRestricted
      have currentReplay := replayed
      obtain ⟨_tag, response, responseEq, _proper, _form⟩ := atoms choice member
      rw [sourceRawReplay, previousReplay, Option.bind_some] at replayed
      simp only [acting, ite_eq_right different, responseEq, Option.bind_some] at replayed
      have appended := sourceReplayAppend_prior_state setup implementation
        ⟨some previous, previousTrace⟩ ⟨some control, trace⟩ _ _ replayed
      have stateEq := appended.2
      have actualPreviousKept : TracePrefix previousTrace actualEndpoint.trace := by
        have kept := (priorKept ⟨some control, trace⟩).trans actualOnward
        rw [appended.1] at kept
        exact kept
      have controlEq := Option.some.inj stateEq
      have previousKept : TracePrefix prior endpoint.trace :=
        (TracePrefix.extend (TracePrefix.refl (prefixTrace := prior)) joint legal moved).trans
          onward
      by_cases sameOwner : owner = responder
      · subst responder
        obtain ⟨emitted, recalledEntry⟩ := (nativeApplication).respond_recall_entry
          previous.execution owner response.val
        have recallEq : control.execution.recall owner = previous.execution.recall owner ++
            [⟨previous.execution.observe nativeApplication owner, response.val, emitted⟩] := by
          rw [controlEq]
          exact recalledEntry
        by_cases old : index < (previous.execution.recall owner).length
        · have previousResult := ih previousKept previous previousTrace previousReplay
            actualPreviousKept index old related restricted
          simpa only [recallEq, List.getElem_append_left old,
            List.take_append_of_le_length (Nat.le_of_lt old)] using previousResult
        · have last : index = (previous.execution.recall owner).length := by
            rw [recallEq, List.length_append, List.length_singleton] at inside
            omega
          subst index
          refine ⟨before, after, prior, joint, legal, moved, script, mass, previous,
            previousTrace, ⟨some control, trace⟩, kernel, choice, onward, actualPreviousKept,
            acting, earlier,
            previousReplay, related, restricted, currentReplay, actualOnward,
            currentRelated, currentRestricted, atoms, description, member, ?_, ?_, ?_⟩
          · simpa only [recallEq, List.getElem_concat_length rfl] using responseEq
          · simp only [recallEq, List.take_left]
          · simp only [recallEq, List.getElem_concat_length rfl]
      · have recallEq : control.execution.recall owner = previous.execution.recall owner := by
          rw [controlEq]
          exact (nativeApplication).respond_recall_other previous.execution responder owner
            sameOwner response.val
        simpa only [recallEq] using ih previousKept previous previousTrace previousReplay
          actualPreviousKept index
          (by simpa only [recallEq] using inside) related restricted

open Classical in
/-- Conditioning the fixed complete word at an actual recalled callback
uses its chronological proper kernel at the updated earlier own view. -/
private theorem sourceReplay_issued_callback_kernel
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((earlier.append (.commit name owner fresh guard later)).prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction ((earlier.append (.commit name owner fresh guard later)).prepend suffix)
        index (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (control before : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some before)) (count : Nat)
    (past : before.execution.recall owner = (control.execution.recall owner).take count)
    (signed : before.execution.application.attempt = control.execution.application.attempt)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : before.execution.application.phases.head? = some phase)
    (phaseLow : phase.low = low)
    (phaseHigh : phase.high = low + (earlier.append (.commit name owner fresh guard later)).length)
    (selected : (serviceGraph setup .concurrent).EventId)
    (shape : (serviceGraph setup .concurrent).outputLayout selected = .binding owner payload)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, selected⟩)
    (selectedInside : low ≤ selected.val ∧
      selected.val < low + (earlier.append (.commit name owner fresh guard later)).length)
    (selectedRank : selected.val - low = earlier.length)
    (unsent : ∀ message ∈ (nativeApplication).outputs (before.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨before.execution.application.attempt, selected⟩)
    (profile : SourceProgram.BehavioralProfile
      (earlier.prepend (.commit name owner fresh guard (later.prepend suffix))))
    (entry : SourceProgram.Config Player L Γ) (reference : DecisionView owner Ξ) :
    let current := earlier.tailProfile (.commit name owner fresh guard (later.prepend suffix))
      profile
    let beforeLaw := earlier.prefixLaw (.commit name owner fresh guard (later.prepend suffix))
      profile entry
    let complete := beforeLaw.bind fun config =>
      ((SourceProgram.CommitPrefix.commit name owner fresh guard later).prefixLaw suffix
        current config)
    let prior := complete.map (SourceProgram.Config.view owner)
    let observed := (later.entryView owner reference).back true
    reference ∈ prior.support →
    issuedLedger setup implementation (earlier.append (.commit name owner fresh guard later)) low
      before (low + (earlier.append (.commit name owner fresh guard later)).length)
      owner reference →
    (fiberPosterior prior (fun word => decide (sourceIssuedOwnObservation setup implementation
      (earlier.append (.commit name owner fresh guard later)) low control owner reference
        count word)) true).map
      ((earlier.append (.commit name owner fresh guard later)).wordAction owner earlier.length) =
      (SourceProgram.commitKernel current observed).map (fun result =>
        some (OwnAction.commit owner name payload result)) := by
  intro current beforeLaw complete prior observed supported retained
  have observation : (fun word => decide (sourceIssuedOwnObservation setup implementation
      (earlier.append (.commit name owner fresh guard later)) low control owner reference
        count word)) = (fun word => decide (issuedLedger setup implementation
      (earlier.append (.commit name owner fresh guard later)) low before
        (low + (earlier.append (.commit name owner fresh guard later)).length) owner word)) := by
    funext word
    exact decide_eq_decide.mpr (sourceReplay_issued_callback_observation setup implementation
      (earlier.append (.commit name owner fresh guard later)) suffix embedding low rank actions
        control before trace owner count past signed reference word retained)
  rw [observation]
  exact issuedLedger_owned_word_conditional setup implementation fresh guard earlier later suffix
    embedding low rank actions trace phase installed phaseLow phaseHigh selected shape request
      selectedInside selectedRank unsent profile entry reference supported retained

/-- Inside the same ordinary attempt, a literal retained source rank is
exactly the corresponding prefix of the original run from the fixed entry. -/
private theorem sourceReplay_ordinary_rank_support
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (lift : ProtocolState (earlier.prepend (later.prepend suffix)) →
      ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (earlier.prepend (later.prepend suffix)) lift)
    (entry : SourceProgram.Config Player L Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (point : current.point = lift
      (ProtocolState.entry (earlier.prepend (later.prepend suffix)) entry))
    (ordinary : current.excluded = current.entryExcluded)
    (final : setup.proposalRecoveryProtocol.History)
    (supported : final ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) (earlier.length + later.length)
        ⟨some current, trace⟩).support)
    (selected : CommitRecoveryState setup.program)
    (selectedTrace : setup.proposalRecoveryProtocol.Trace (some selected))
    (retained : TracePrefix selectedTrace final.trace)
    (generation : selected.generation = current.generation)
    (rank : instructionCount setup.program - ProtocolState.remaining setup.program selected.point =
      instructionCount setup.program - ProtocolState.remaining setup.program current.point +
        earlier.length) :
    (⟨some selected, selectedTrace⟩ : setup.proposalRecoveryProtocol.History) ∈
      (setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup values)
        earlier.length ⟨some current, trace⟩).support ∧
      final ∈ (setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup values)
        later.length ⟨some selected, selectedTrace⟩).support := by
  rw [setup.proposalRecoveryModel.runBehavioralFrom_add] at supported
  obtain ⟨middle, first, last⟩ := (PMF.mem_support_bind_iff ..).mp supported
  have middleKept := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin
    (sourceUnflaggedStrategy setup values) later.length middle final last).tracePrefix
  obtain ⟨middleSource, middleCurrent, middleTrace, _attempt, middleEq, middlePoint,
    _middleExcluded, _middleEntry, middleGeneration, _middleWord, _middleLabels, _proper⟩ :=
    proposalRecovery_ordinary_commit_block_support setup values earlier (later.prepend suffix)
      lift origin entry current trace point ordinary middle first
  subst middle
  have firstRemaining : ProtocolState.remaining setup.program current.point =
      instructionCount (earlier.prepend (later.prepend suffix)) := by
    rw [point, origin.remaining_lift, ProtocolState.remaining_entry]
  have middleRemaining : ProtocolState.remaining setup.program middleCurrent.point =
      instructionCount (later.prepend suffix) := by
    rw [middlePoint, origin.remaining_lift, earlier.liftPoint_remaining,
      ProtocolState.remaining_entry]
  have firstCount := earlier.instructionCount_prepend (later.prepend suffix)
  have selectedBound := ProtocolState.remaining_le_instructionCount setup.program selected.point
  have currentBound := ProtocolState.remaining_le_instructionCount setup.program current.point
  have middleBound := ProtocolState.remaining_le_instructionCount setup.program middleCurrent.point
  have sameRemaining : ProtocolState.remaining setup.program selected.point =
      ProtocolState.remaining setup.program middleCurrent.point := by omega
  have sameGeneration : selected.generation = middleCurrent.generation :=
    generation.trans middleGeneration.symm
  by_cases order : selectedTrace.length ≤ middleTrace.length
  · have selectedToMiddle : TracePrefix selectedTrace middleTrace :=
      (retained.reachesWithin.ancestor_comparable middleKept.reachesWithin order).tracePrefix
    have balance := setup.commitRecovery_same_generation_length
      (setup.proposalRecoveryEraseTrace_prefix selectedToMiddle).reachesWithin
        selected middleCurrent rfl rfl sameGeneration
    have depth : selectedTrace.length = middleTrace.length := by
      simp only [setup.proposalRecoveryEraseTrace_length] at balance
      omega
    have same := selectedToMiddle.eq_of_length depth
    rw [same]
    exact ⟨first, last⟩
  · have middleToSelected : TracePrefix middleTrace selectedTrace :=
      (middleKept.reachesWithin.ancestor_comparable retained.reachesWithin (by
        change middleTrace.length ≤ selectedTrace.length
        omega)).tracePrefix
    have balance := setup.commitRecovery_same_generation_length
      (setup.proposalRecoveryEraseTrace_prefix middleToSelected).reachesWithin
        middleCurrent selected rfl rfl sameGeneration.symm
    have depth : middleTrace.length = selectedTrace.length := by
      simp only [setup.proposalRecoveryEraseTrace_length] at balance
      omega
    have same := middleToSelected.eq_of_length depth
    rw [← same]
    exact ⟨first, last⟩

open Classical in
/-- At an actual ready callback, the conditional source owner-word law is
the original source law at the same retained commitment row. -/
private theorem sourceReplay_issued_source_callback_atom
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    {Δ : SourceCtx Player L} {Q : Finset VarId}
    (suffix : SourceProgram Player L Δ Q)
    (wordBlock : SourceProgram.CommitPrefix
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.context
      (checkpointSelection setup implementation operational
        trace).val.checkpoint.residual.names Δ Q)
    (reconstruct : (checkpointSelection setup implementation operational
      trace).val.checkpoint.residual.tail =
      wordBlock.prepend suffix)
    (boundary : IsCommitBoundary suffix)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan control phase wordBlock suffix)
    (positive : 0 < wordBlock.length)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (ordinarySupported : (⟨some targetCurrent, targetTrace⟩ :
      setup.proposalRecoveryProtocol.History) ∈
      (setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup values)
        wordBlock.length ⟨some cursor.current, cursor.trace⟩).support)
    (referenceWord : SourceProgram.Config Player L Δ)
    (referenceSupported : referenceWord ∈ (wordBlock.prefixLaw suffix
      (ordinaryBlockProfile setup .concurrent implementation.plan values wordBlock suffix
        cursor.embedding (fun owner view => cursor.views.view owner view)
        (control.execution.application.entry.excluded, control.execution.application.generation,
          control.execution.application.attempt.phase)
        control.execution.application.publicView
        (PhaseProposal.sourceArchive control.execution.network.inputs)) cursor.source).support)
    (ledger : ∀ owner, issuedLedger setup implementation wordBlock
      control.execution.application.attempt.phase control
        (control.execution.application.attempt.phase + wordBlock.length) owner
          (referenceWord.view owner))
    (finished : SourceProgram.Config Player L Δ)
    (attempt : wordBlock.Attempt cursor.source cursor.current.excluded finished
      targetCurrent.excluded)
    (finishedPoint : targetCurrent.point = cursor.lift
      (wordBlock.liftPoint suffix (ProtocolState.entry suffix finished)))
    (exclusions : targetCurrent.excluded = cursor.current.excluded)
    (referenceEq : referenceWord = attempt.withoutMisses ∅ cursor.source)
    (owner : Player) (count : Nat)
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (actualBefore : (nativeApplication).Control)
    (actualPrior : (nativeProtocol).Trace (some actualBefore))
    (actualKept : TracePrefix actualPrior trace)
    (past : actualBefore.execution.recall owner = (control.execution.recall owner).take count)
    (sameAttempt : actualBefore.execution.application.attempt =
      control.execution.application.attempt)
    (unsent : ∀ message ∈ (nativeApplication).outputs (actualBefore.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨actualBefore.execution.application.attempt, named⟩)
    (request : actualBefore.execution.application.SeedRequest owner
      ⟨actualBefore.execution.application.attempt, named⟩)
    (sourceCurrent : CommitRecoveryState setup.program)
    (sourceTrace : setup.proposalRecoveryProtocol.Trace (some sourceCurrent))
    (sourceKept : TracePrefix sourceTrace targetTrace)
    (sourceRank : named.val = instructionCount setup.program -
      ProtocolState.remaining setup.program sourceCurrent.point)
    (sourceCurrentGeneration : sourceCurrent.generation = control.execution.application.generation)
    (surviving : owner ∉ sourceCurrent.excluded) :
    control.execution.application.attempt.phase ≤ named.val ∧
      named.val < control.execution.application.attempt.phase + wordBlock.length ∧
      (fiberPosterior
        ((wordBlock.prefixLaw suffix
          (ordinaryBlockProfile setup .concurrent implementation.plan values wordBlock suffix
            cursor.embedding (fun actor view => cursor.views.view actor view)
            (control.execution.application.entry.excluded,
              control.execution.application.generation, control.execution.application.attempt.phase)
            control.execution.application.publicView
            (PhaseProposal.sourceArchive control.execution.network.inputs)) cursor.source).map
              (SourceProgram.Config.view owner))
        (fun word => decide (sourceIssuedOwnObservation setup implementation wordBlock
          control.execution.application.attempt.phase control owner (referenceWord.view owner)
            count word)) true).map
          (wordBlock.wordAction owner (named.val - control.execution.application.attempt.phase)) =
        (values owner (setup.proposalRecoveryQuery owner
          (setup.proposalRecoveryModel.infoOf owner sourceTrace))).map (fun sampled =>
            decodeEventAction setup.program named
              (cast (congrArg EventField.Action shape.symm) (.success
                (phaseRecoveryDomainValue setup .concurrent named owner ty shape
                  sampled.val.val)))) := by
  classical
  let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
  have initialEq : nativeInitial = (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  have earlierLedger := sourceReplay_issued_ledger_prefix setup implementation wordBlock
    control.execution.application.attempt.phase
      (control.execution.application.attempt.phase + wordBlock.length)
      control trace actualBefore owner (by
        rw [past]
        exact List.take_subset _ _) sameAttempt (referenceWord.view owner) (ledger owner)
  have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    intro state reached
    rw [initialEq] at reached
    obtain ⟨input, _drawn, rfl⟩ := (PMF.mem_support_map_iff ..).mp reached
    exact PhaseRuntimeState.initial_ordered implementation.plan input
  have beforeOrdered := (phaseApplication_seedOrder implementation.runtime
    implementation.leaks).history nativeInitial implementation.horizon
      implementation.scheduler initialized
        ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler actualPrior)
  have phasesAlong : ∀ {state} {lastTrace : (nativeProtocol).Trace state},
      TracePrefix actualPrior lastTrace →
      ∃ next : (nativeApplication).Control, state = some next ∧
        next.execution.application.Ordered ∧
        actualBefore.execution.application.attempt.generation ≤
          next.execution.application.attempt.generation ∧
        actualBefore.execution.application.attempt.phase ≤
          next.execution.application.attempt.phase ∧
        (actualBefore.execution.application.attempt = next.execution.application.attempt →
          next.execution.application.phases =
            actualBefore.execution.application.phases) := by
    intro state lastTrace kept
    induction kept with
    | refl => exact ⟨actualBefore, rfl, beforeOrdered, le_rfl, le_rfl, fun _ => rfl⟩
    | @extend oldState nextState previousTrace kept joint legal realized ih =>
      obtain ⟨middle, rfl, middleOrdered, lowerGeneration, lowerPhase, previousPhases⟩ := ih
      have moved : nextState ∈ ((nativeApplication).transition nativeInitial
          implementation.horizon implementation.scheduler (some middle) joint).support :=
        realized
      obtain ⟨next, rfl, _recalled⟩ := (nativeApplication).transition_recall_prefix
        nativeInitial implementation.horizon implementation.scheduler middle nextState
          joint moved
      have nextOrdered := (phaseApplication_seedOrder implementation.runtime
        implementation.leaks).transition nativeInitial implementation.horizon
          implementation.scheduler initialized (some middle) (some next) joint
            middleOrdered moved
      have progress := (phaseApplication_namespace_progress implementation.runtime
        implementation.leaks).transition nativeInitial implementation.horizon
          implementation.scheduler middle next joint moved middleOrdered
      refine ⟨next, rfl, nextOrdered, lowerGeneration.trans progress.1,
        lowerPhase.trans progress.2, ?_⟩
      intro sameNext
      have intermediate : actualBefore.execution.application.attempt =
          middle.execution.application.attempt := by
        have generationEq := congrArg CommitAttemptId.generation sameNext
        have phaseEq := congrArg CommitAttemptId.phase sameNext
        cases first : actualBefore.execution.application.attempt with
        | mk firstPhase firstGeneration =>
          cases second : middle.execution.application.attempt with
          | mk secondPhase secondGeneration =>
            simp only [first, second] at lowerGeneration lowerPhase progress
            simp only [first] at generationEq phaseEq ⊢
            congr 1 <;> omega
      exact ((phaseApplication_sameAttempt_controls implementation.runtime
        implementation.leaks).transition nativeInitial implementation.horizon
          implementation.scheduler middle next joint moved middleOrdered
            (intermediate.symm.trans sameNext)).1.trans (previousPhases intermediate)
  obtain ⟨last, stateEq, _ordered, _lowerGeneration, _lowerPhase, phasesPreserved⟩ :=
    phasesAlong actualKept
  have lastEq : last = control := (Option.some.inj stateEq).symm
  subst last
  have samePhases : control.execution.application.phases =
      actualBefore.execution.application.phases := phasesPreserved sameAttempt
  have countedBefore := initialEq ▸ actualPrior
  have rawBefore := (nativeMenu).toRawTrace _ implementation.horizon
    implementation.scheduler countedBefore
  obtain ⟨currentPhase, remaining, installed, commitment, phaseInside⟩ :=
    phase_ready_binding_phase implementation.runtime implementation.leaks
      implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent) operational.maximalPhases
        (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
          rawBefore owner named ty shape request.2.2.1
  have finalInstalled : control.execution.application.phases = currentPhase :: remaining :=
    samePhases.trans installed
  have geometry := source_checkpoint_binding_interval setup implementation
    (checkpointSelection setup implementation operational trace).val
      operational.maximalPhases
      currentPhase remaining finalInstalled commitment
  have phaseLow : currentPhase.low = control.execution.application.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, finalInstalled, List.head?_cons,
      Option.map_some, Option.getD_some]
  have endpoint : ProtocolState.commitEnd setup.program
      (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) =
        instructionCount suffix := by
    rw [checkpoint.origin.commitEnd_lift, reconstruct]
    exact wordBlock.commitEnd_entry_prepend suffix boundary checkpoint.source
  have phaseHigh : currentPhase.high =
      control.execution.application.attempt.phase + wordBlock.length := by
    have ranks := checkpoint.compiled.countEq
    have width := wordBlock.instructionCount_prepend suffix
    have interval := geometry.2.2
    rw [endpoint] at interval
    simp only [eventCount_eq_instructionCount] at ranks
    rw [reconstruct] at ranks
    omega
  have selectedInside : control.execution.application.attempt.phase ≤ named.val ∧
      named.val < control.execution.application.attempt.phase + wordBlock.length := by
    have bounds := (currentPhase.mem_events named).mp phaseInside
    simpa only [phaseLow, phaseHigh] using bounds
  refine ⟨selectedInside.1, selectedInside.2, ?_⟩
  have offset : cursor.offset = control.execution.application.attempt.phase := by
    have firstCount := cursor.compiled.countEq
    have selectedCount := checkpoint.compiled.countEq
    change cursor.offset + eventCount (wordBlock.prepend suffix) = eventCount setup.program
      at firstCount
    change control.execution.application.attempt.phase + eventCount checkpoint.residual.tail =
      eventCount setup.program at selectedCount
    rw [reconstruct] at selectedCount
    omega
  let selectedIndex : Fin (eventCount (wordBlock.prepend suffix)) :=
    ⟨named.val - control.execution.application.attempt.phase, by
      have count := wordBlock.eventCount_prepend suffix
      omega⟩
  have selectedBound : selectedIndex.val < wordBlock.length := by
    dsimp only [selectedIndex]
    omega
  have selectedEq : cursor.embedding.event selectedIndex = named := by
    apply Fin.ext
    rw [cursor.compiled.rankEq, offset]
    dsimp only [selectedIndex]
    omega
  have selectedShape : outputLayout (wordBlock.prepend suffix) selectedIndex =
      .binding owner ty :=
    (cursor.embedding.layout_eq selectedIndex).symm.trans (selectedEq.symm ▸ shape)
  obtain ⟨middleContext, middleNames, name, fresh, guard, first, last, firstSize,
    blockSplit⟩ := wordBlock.binding_split_of_layout suffix selectedIndex selectedBound
      owner ty selectedShape
  dsimp only [selectedIndex] at firstSize
  subst wordBlock
  let head : SourceProgram.CommitPrefix middleContext middleNames Δ Q :=
    .commit name owner fresh guard last
  let wholeProfile := ordinaryBlockProfile setup .concurrent implementation.plan values
    (first.append head) suffix cursor.embedding
      (fun owner view => cursor.views.view owner view)
      (control.execution.application.entry.excluded,
        control.execution.application.generation,
        control.execution.application.attempt.phase)
      control.execution.application.publicView
      (PhaseProposal.sourceArchive control.execution.network.inputs)
  let association := first.prepend_append head suffix
  let splitProfile := cast (congrArg SourceProgram.BehavioralProfile association)
    wholeProfile
  let splitLift := fun point : ProtocolState (first.prepend (head.prepend suffix)) =>
    cursor.lift (cast (congrArg ProtocolState association.symm) point)
  have transportOrigin {context : SourceCtx Player L} {names : Finset VarId}
      (old new : SourceProgram Player L context names) (same : old = new)
      (oldLift : ProtocolState old → ProtocolState setup.program)
      (oldOrigin : ProtocolSuffix setup.program old oldLift) :
      ProtocolSuffix setup.program new (fun point =>
        oldLift (cast (congrArg ProtocolState same.symm) point)) := by
    cases same
    exact oldOrigin
  have transportEntry {context : SourceCtx Player L} {names : Finset VarId}
      (old new : SourceProgram Player L context names) (same : old = new)
      (source : SourceProgram.Config Player L context) :
      cast (congrArg ProtocolState same) (ProtocolState.entry old source) =
        ProtocolState.entry new source := by
    cases same
    rfl
  have splitOrigin : ProtocolSuffix setup.program
      (first.prepend (head.prepend suffix)) splitLift :=
    transportOrigin _ _ association cursor.lift cursor.origin
  have splitPoint : cursor.current.point = splitLift
      (ProtocolState.entry (first.prepend (head.prepend suffix)) cursor.source) := by
    dsimp only [splitLift]
    rw [cursor.point, ← transportEntry _ _ association cursor.source, cast_cast, cast_eq]
  have ordinary : cursor.current.excluded = cursor.current.entryExcluded :=
    cursor.excluded.trans cursor.entryExcluded.symm
  have sourceSameGeneration : sourceCurrent.generation = cursor.current.generation := by
    have controls := congrArg (fun signal => signal.2.1) (cursor.controls positive)
    change cursor.current.generation = control.execution.application.generation at controls
    exact sourceCurrentGeneration.trans controls.symm
  have startRank : instructionCount setup.program -
      ProtocolState.remaining setup.program cursor.current.point =
        control.execution.application.attempt.phase := by
    rw [cursor.point, cursor.origin.remaining_lift, ProtocolState.remaining_entry]
    have count := cursor.compiled.countEq
    simp only [eventCount_eq_instructionCount] at count
    rw [offset] at count
    omega
  have sourcePosition : instructionCount setup.program -
      ProtocolState.remaining setup.program sourceCurrent.point =
        instructionCount setup.program -
          ProtocolState.remaining setup.program cursor.current.point + first.length := by
    rw [startRank, ← sourceRank]
    omega
  have wholeSupported := ordinarySupported
  simp only [SourceProgram.CommitPrefix.length_append] at wholeSupported
  obtain ⟨sourceSupported, tailSupported⟩ := sourceReplay_ordinary_rank_support setup values
    first head suffix splitLift splitOrigin cursor.source cursor.current cursor.trace
      splitPoint ordinary ⟨some targetCurrent, targetTrace⟩ wholeSupported sourceCurrent
        sourceTrace sourceKept sourceSameGeneration sourcePosition
  obtain ⟨middleSource, middleCurrent, middleTrace, firstAttempt, sourceHistoryEq,
    middlePoint, middleExcluded, middleEntry, middleGeneration, _middleWord,
    _middleLabels, firstProper⟩ :=
      proposalRecovery_ordinary_commit_block_support setup values
      first (head.prepend suffix) splitLift splitOrigin cursor.source cursor.current
        cursor.trace splitPoint ordinary ⟨some sourceCurrent, sourceTrace⟩ sourceSupported
  have sourceCurrentEq : sourceCurrent = middleCurrent :=
    Option.some.inj (congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      history.state) sourceHistoryEq)
  have sourceInfoEq : setup.proposalRecoveryModel.infoOf owner sourceTrace =
      setup.proposalRecoveryModel.infoOf owner middleTrace :=
    congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      setup.proposalRecoveryModel.infoOf owner history.trace) sourceHistoryEq
  rw [sourceHistoryEq] at tailSupported
  obtain ⟨lastSource, lastCurrent, lastTrace, tailAttempt, targetHistoryEq, lastPoint,
    _lastExcluded, _lastEntry, _lastGeneration, _lastWord, _lastLabels, _lastProper⟩ :=
    proposalRecovery_ordinary_commit_block_support setup values head suffix
      (fun point => splitLift (first.liftPoint (head.prepend suffix) point))
        (splitOrigin.compose (first.protocolSuffix (head.prepend suffix))) middleSource
          middleCurrent middleTrace middlePoint
            (middleExcluded.trans middleEntry.symm)
              ⟨some targetCurrent, targetTrace⟩ tailSupported
  have targetCurrentEq : targetCurrent = lastCurrent :=
    Option.some.inj (congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      history.state) targetHistoryEq)
  have endpointPoint (result : SourceProgram.Config Player L Δ) :
      splitLift (first.liftPoint (head.prepend suffix)
        (head.liftPoint suffix (ProtocolState.entry suffix result))) =
        cursor.lift ((first.append head).liftPoint suffix (ProtocolState.entry suffix
          result)) := by
    dsimp only [splitLift]
    rw [← first.liftPoint_append head suffix, cast_cast, cast_eq]
  have lastPointWhole : targetCurrent.point = cursor.lift
      ((first.append head).liftPoint suffix (ProtocolState.entry suffix lastSource)) := by
    rw [targetCurrentEq, lastPoint, endpointPoint]
  have finalViews : finished.view owner = lastSource.view owner := by
    have same := congrArg (ProtocolState.observe owner setup.program)
      (finishedPoint.symm.trans lastPointWhole)
    have localSame := (cursor.origin.compose
      ((first.append head).protocolSuffix suffix)).observe_reflect owner
        (ProtocolState.entry suffix finished) (ProtocolState.entry suffix lastSource) same
    have recalled := congrArg (ProtocolView.entryView owner suffix) localSame
    simpa only [ProtocolView.entryView_observe_entry] using recalled
  have entrySurvives : owner ∉ cursor.current.excluded := by
    intro excluded
    exact surviving ((congrArg CommitRecoveryState.excluded sourceCurrentEq).symm ▸
      middleExcluded.symm ▸ excluded)
  have finalSurvives : owner ∉ targetCurrent.excluded := by
    rw [exclusions]
    exact entrySurvives
  have referenceView : referenceWord.view owner = finished.view owner := by
    rw [referenceEq]
    exact (attempt.withoutMisses_surviving_view ∅ cursor.source owner rfl
      finalSurvives).symm
  have typedProjection {initialContext finalContext : SourceCtx Player L}
      {initialNames finalNames : Finset VarId}
      (piece : SourceProgram.CommitPrefix initialContext initialNames
        finalContext finalNames) (rest : SourceProgram Player L finalContext finalNames)
      (result : SourceProgram.Config Player L finalContext) :
      ProtocolView.entryView owner (piece.prepend rest)
        (ProtocolState.observe owner (piece.prepend rest)
          (piece.liftPoint rest (ProtocolState.entry rest result))) =
        piece.entryView owner (result.view owner) := by
    induction piece with
    | nil => exact ProtocolView.entryView_observe_entry owner rest result
    | commit _ actor _ _ remaining ih =>
        change (ProtocolView.entryView owner (remaining.prepend rest)
          (ProtocolState.observe owner (remaining.prepend rest)
            (remaining.liftPoint rest (ProtocolState.entry rest result)))).back
              (decide (actor = owner)) = _
        rw [ih]
        rfl
  have observed : (last.entryView owner (referenceWord.view owner)).back true =
      middleSource.view owner := by
    have recovered := tailAttempt.entryView suffix owner (by
      rw [← (congrArg CommitRecoveryState.excluded targetCurrentEq)]
      exact finalSurvives)
    rw [typedProjection head suffix lastSource] at recovered
    rw [referenceView, finalViews]
    simpa only [head, SourceProgram.CommitPrefix.entryView, decide_true] using recovered
  have sourceLaw := first.prefixLaw_append head suffix wholeProfile cursor.source
  have ownSupported : referenceWord.view owner ∈
      (((first.prefixLaw (head.prepend suffix) splitProfile cursor.source).bind
        (head.prefixLaw suffix (first.tailProfile (head.prepend suffix) splitProfile))).map
          (SourceProgram.Config.view owner)).support := by
    rw [← sourceLaw]
    exact (PMF.mem_support_map_iff ..).mpr ⟨referenceWord, referenceSupported, rfl⟩
  have ranks : ∀ position, (cursor.embedding.event position).val =
      control.execution.application.attempt.phase + position.val := by
    intro position
    rw [cursor.compiled.rankEq, offset]
  have installedHead : actualBefore.execution.application.phases.head? =
      some currentPhase := by simp only [installed, List.head?_cons]
  have conditional := sourceReplay_issued_callback_kernel setup implementation fresh guard
    first last suffix cursor.embedding control.execution.application.attempt.phase ranks
      cursor.views.actionEq control actualBefore actualPrior count past sameAttempt
        currentPhase installedHead phaseLow phaseHigh named shape request selectedInside
          firstSize.symm unsent splitProfile cursor.source (referenceWord.view owner)
            ownSupported earlierLedger
  rw [← firstSize, sourceLaw]
  refine conditional.trans ?_
  rw [observed]
  have committingStart : ProtocolState.atCommit setup.program
      cursor.current.point = true := by
    rw [splitPoint, splitOrigin.atCommit_lift]
    cases first <;> rfl
  have savedRank := congrArg (fun signal => signal.2.2) (cursor.controls positive)
  change instructionCount setup.program -
    ProtocolState.remaining setup.program cursor.current.saved =
      control.execution.application.attempt.phase at savedRank
  have savedBound := ProtocolState.remaining_le_instructionCount setup.program
    cursor.current.saved
  have pointBound := ProtocolState.remaining_le_instructionCount setup.program
    cursor.current.point
  have sameRemaining : ProtocolState.remaining setup.program cursor.current.saved =
      ProtocolState.remaining setup.program cursor.current.point := by omega
  obtain ⟨entryTrace, entryKept, entryClock⟩ := setup.commitRecovery_attempt_entry
    cursor.current (setup.proposalRecoveryEraseTrace cursor.trace) committingStart
  have entryDepth : entryTrace.length =
      (setup.proposalRecoveryEraseTrace cursor.trace).length := by omega
  have entryHistory := entryKept.eq_of_length entryDepth
  have initialState := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    history.state) entryHistory
  have atPoint : CommitRecoveryState.atPoint cursor.current.saved
      cursor.current.entryExcluded cursor.current.generation = cursor.current :=
    Option.some.inj initialState
  have savedPoint : cursor.current.saved = cursor.current.point :=
    congrArg CommitRecoveryState.point atPoint
  have startState : CommitRecoveryState.atPoint cursor.current.point
      cursor.current.excluded cursor.current.generation = cursor.current := by
    rw [← savedPoint, ordinary]
    exact atPoint
  let startTrace : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint cursor.current.point cursor.current.excluded
        cursor.current.generation)) := startState.symm ▸
          setup.proposalRecoveryEraseTrace cursor.trace
  have startTraceEq : (⟨some (CommitRecoveryState.atPoint cursor.current.point
        cursor.current.excluded cursor.current.generation), startTrace⟩ :
          setup.commitRecoveryProtocol.History) =
      ⟨some cursor.current, setup.proposalRecoveryEraseTrace cursor.trace⟩ := by
    have transport {before after : CommitRecoveryState setup.program}
        (same : before = after) (trace : setup.commitRecoveryProtocol.Trace (some after)) :
        (⟨some before, same.symm ▸ trace⟩ : setup.commitRecoveryProtocol.History) =
          ⟨some after, trace⟩ := by
      cases same
      rfl
    exact transport startState (setup.proposalRecoveryEraseTrace cursor.trace)
  have sourcePast := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin
    (sourceUnflaggedStrategy setup values) first.length
      ⟨some cursor.current, cursor.trace⟩ ⟨some sourceCurrent, sourceTrace⟩
        sourceSupported).tracePrefix
  have sourceClock := setup.commitRecovery_same_generation_length
    (setup.proposalRecoveryEraseTrace_prefix sourcePast).reachesWithin cursor.current
      sourceCurrent rfl rfl sourceSameGeneration.symm
  have sourceRemaining : ProtocolState.remaining setup.program sourceCurrent.point +
      first.length = ProtocolState.remaining setup.program cursor.current.point := by
    have sourceBound := ProtocolState.remaining_le_instructionCount setup.program
      sourceCurrent.point
    omega
  have depth : sourceTrace.length = cursor.trace.length + first.length := by
    simp only [setup.proposalRecoveryEraseTrace_length] at sourceClock
    omega
  have window := (first.append head).length_le_commit_window suffix cursor.source
  have strictWindow : sourceTrace.length +
      ProtocolState.commitEnd setup.program cursor.current.point <
        cursor.trace.length +
          ProtocolState.remaining setup.program cursor.current.point := by
    rw [cursor.point, cursor.origin.commitEnd_lift, cursor.origin.remaining_lift] at ⊢
    dsimp only [head] at window
    simp only [SourceProgram.CommitPrefix.length_append,
      SourceProgram.CommitPrefix.length] at window
    omega
  have startKept : TracePrefix startTrace
      (setup.proposalRecoveryEraseTrace sourceTrace) := by
    have kept := setup.proposalRecoveryEraseTrace_prefix sourcePast
    exact (congrArg (fun history : setup.commitRecoveryProtocol.History =>
      TracePrefix history.trace (setup.proposalRecoveryEraseTrace sourceTrace))
        startTraceEq).mpr kept
  have startInside : (setup.proposalRecoveryEraseTrace sourceTrace).length +
      ProtocolState.commitEnd setup.program cursor.current.point < startTrace.length +
        ProtocolState.remaining setup.program cursor.current.point := by
    have clock := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      history.trace.length) startTraceEq
    simpa only [setup.proposalRecoveryEraseTrace_length, clock] using strictWindow
  have sameExcluded : sourceCurrent.excluded = cursor.current.excluded := by
    rw [sourceCurrentEq, middleExcluded]
  obtain ⟨_current, _replay, stateEq, sourceSavedEq, _sourceEntry, sourceGen,
    _rest⟩ := setup.commitRecovery_noMiss_prefix_information owner cursor.current.point
      cursor.current.excluded cursor.current.generation startTrace committingStart
        (setup.proposalRecoveryEraseTrace sourceTrace) startKept startInside surviving
  have currentEq : _current = sourceCurrent := (Option.some.inj stateEq).symm
  subst _current
  have controlsRead : setup.commitRecoveryPublic (some sourceCurrent) =
      (control.execution.application.entry.excluded,
        control.execution.application.generation,
        control.execution.application.attempt.phase) := by
    change (sourceCurrent.excluded, sourceCurrent.generation,
      instructionCount setup.program - ProtocolState.remaining setup.program
        sourceCurrent.saved) = _
    rw [sameExcluded, sourceGen, sourceSavedEq, startRank]
    have controls := cursor.controls positive
    have saved := PhaseRuntimeState.saved_excluded_eq_public_failures
      (checkpointSelection setup implementation operational trace).val.exclusions
      (checkpointSelection setup implementation operational trace).val.failures
      (checkpointSelection setup implementation operational trace).val.order.frontier
      currentPhase remaining finalInstalled
    have inherited :
        (control.execution.application.publicView.retired.map fun record =>
          record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ =
        PhaseRuntimeState.archivedFailureOwners control.execution.application.retired := by
      have failures := PhaseRuntimeState.sourceRecordFailures_sourceControlRecords
        control.execution.application.retired
      simpa only [RuntimePhasePlan.sourceRecordFailures, PhaseRuntimeState.sourceControlRecords,
        PhaseRuntimeState.publicView, List.map_map, Function.comp_def,
        State.sourceFailureFootprint_read, State.sourceFailureFootprint] using failures
    have mask := congrArg Prod.fst controls
    rw [inherited, State.sourceFailureFootprint_read] at mask
    dsimp only [State.sourceFailureFootprint] at mask
    exact Prod.ext (mask.trans saved.symm) (Prod.ext
      (congrArg (fun signal => signal.2.1) controls) rfl)
  have numeric := source_binding_prefix_addresses setup owner cursor.current.point
    cursor.current.excluded cursor.current.generation startTrace committingStart
      entrySurvives (setup.proposalRecoveryEraseTrace sourceTrace) startKept startInside
        sameExcluded
  have startAddresses := cursor.addresses positive owner
  rw [setup.commitRecovery_publicRecall_addresses] at startAddresses
  have startWord : setup.recoveryAddressWord
      (setup.proposalRecoveryEraseTrace cursor.trace) =
        control.execution.application.publicView.sourcePublicAddressWord
          implementation.plan cursor.offset :=
    List.reverse_injective (List.append_cancel_right startAddresses)
  have startWordEq : setup.recoveryAddressWord startTrace =
      setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cursor.trace) :=
    congrArg (fun history : setup.commitRecoveryProtocol.History =>
      setup.recoveryAddressWord history.trace) startTraceEq
  rw [startWordEq, startWord] at numeric
  have numericClock : (setup.proposalRecoveryEraseTrace sourceTrace).length -
      startTrace.length = first.length := by
    have clock := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      history.trace.length) startTraceEq
    simp only [setup.proposalRecoveryEraseTrace_length] at clock ⊢
    omega
  rw [numericClock, startRank] at numeric
  have controlSignals := cursor.controls positive
  change (cursor.current.excluded, cursor.current.generation,
    instructionCount setup.program - ProtocolState.remaining setup.program
      cursor.current.saved) = _ at controlSignals
  rw [savedRank] at controlSignals
  simp only [PhaseRuntimeState.publicView, List.map_map, Function.comp_def] at controlSignals
  have addressRead : (setup.attemptPublicRecall owner
      (setup.proposalRecoveryEraseTrace sourceTrace)).map
        (setup.commitRecoveryPublicAddress owner) =
      (control.execution.application.publicView.sourcePublicAddressWord implementation.plan
        (ProtocolView.position owner setup.program
          (ProtocolState.observe owner setup.program sourceCurrent.point))).reverse ++
            [(none, (∅, 0, 0))] := by
    rw [setup.commitRecovery_publicRecall_addresses, numeric]
    have position := ProtocolView.position_add_remaining owner setup.program
      sourceCurrent.point
    have positionEq : ProtocolView.position owner setup.program
        (ProtocolState.observe owner setup.program sourceCurrent.point) =
          control.execution.application.attempt.phase + first.length := by omega
    rw [positionEq, offset]
    apply congrArg (fun word : List (Option Nat × (Finset Player × Nat × Nat)) =>
      word.reverse ++ [(none, (∅, 0, 0))])
    simp only [PhasePublicView.sourcePublicAddressWord, PhaseRuntimeState.publicView, Nat.sub_self,
      List.range_zero, List.map_nil, List.append_nil, Nat.add_sub_cancel_left,
      List.append_assoc, List.map_map, Function.comp_def]
    rw [← controlSignals]
  have archiveRead := setup.proposalRecoveryArchive_eq_of_commit_window owner cursor.current
    cursor.trace committingStart sourceTrace sourcePast strictWindow.le
  rw [cursor.proposals owner entrySurvives] at archiveRead
  have uniqueStart : (checkpoint.residual.context.map Prod.fst).Nodup := by
    have liftUnique {context : SourceCtx Player L} {names : Finset VarId}
        {program : SourceProgram Player L context names}
        {lift : ProtocolState program → ProtocolState setup.program}
        (origin : ProtocolSuffix setup.program program lift) :
        (context.map Prod.fst).Nodup := by
      induction origin with
      | initial => exact setup.namesNodup
      | sampleTail fresh _ _ _ ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩
      | commitTail fresh _ _ _ ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩
      | revealTail fresh _ _ _ _ ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩
    exact liftUnique splitOrigin
  have middleLive : middleSource.BindingsHoldValues owner :=
    (firstAttempt.own_bindings_success_iff owner uniqueStart
      (cursor.live owner entrySurvives) (middleExcluded.symm ▸ entrySurvives)).mpr
        (fun joint member move selected => (firstProper joint member owner move selected).2)
  have live : ProtocolState.BindingsHoldValues owner setup.program sourceCurrent.point := by
    rw [sourceCurrentEq, middlePoint, splitOrigin.bindingsHoldValues_lift,
      first.bindingsHoldValues_liftPoint, ProtocolState.bindingsHoldValues_entry]
    exact middleLive
  let queryAt := fun (view : ProtocolView owner setup.program)
      (controls : Finset Player × Nat × Nat) =>
    (setup.commitRecoveryErasedInformation owner
      (setup.commitRecoveryNoMissInformation owner
        (setup.commitRecoveryErasedRead owner
          (ProtocolView.virtualBindings owner (setup.context.map Prod.fst).toFinset
            setup.program view) controls
          ((control.execution.application.publicView.sourcePublicAddressWord
            implementation.plan (ProtocolView.position owner setup.program view)).reverse ++
              [(none, (∅, 0, 0))]))),
      PhaseProposal.sourceArchive control.execution.network.inputs)
  have structuralRow {initialContext endContext : SourceCtx Player L}
      {initialNames endNames : Finset VarId}
      (piece : SourceProgram.CommitPrefix initialContext initialNames endContext endNames)
      (endFresh : name ∉ endContext.map Prod.fst)
      (endGuard : SourceGuard L endContext owner name ty)
      (endTail : SourceProgram.CommitPrefix ((name, .commitment owner ty) :: endContext)
        (insert name endNames) Δ Q)
      (endSource : SourceProgram.Config Player L endContext)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        ((piece.append (.commit name owner endFresh endGuard endTail)).prepend suffix))
      (wholeViews : ∀ actor,
        ProtocolView actor
          ((piece.append (.commit name owner endFresh endGuard endTail)).prepend suffix) →
            ProtocolView actor setup.program)
      (position : Fin (eventCount
        ((piece.append (.commit name owner endFresh endGuard endTail)).prepend suffix)))
      (atEnd : position.val = piece.length)
      (typed : outputLayout setup.program (embedding.event position) = .binding owner ty)
      (controls : Finset Player × Nat × Nat) :
      SourceProgram.commitKernel
        (piece.tailProfile (SourceProgram.commit name owner endFresh endGuard
          (endTail.prepend suffix))
          (cast (congrArg SourceProgram.BehavioralProfile
            (piece.prepend_append (.commit name owner endFresh endGuard endTail) suffix))
            (ordinaryBlockProfile setup .concurrent implementation.plan values
              (piece.append (.commit name owner endFresh endGuard endTail)) suffix embedding
                wholeViews controls control.execution.application.publicView
                  (PhaseProposal.sourceArchive control.execution.network.inputs))))
        (endSource.view owner) =
      (if owner ∈ controls.1 then PMF.pure .failure else
        (values owner (queryAt
          (wholeViews owner (ProtocolState.observe owner
            ((piece.append (.commit name owner endFresh endGuard endTail)).prepend suffix)
            (cast (congrArg ProtocolState
              (piece.prepend_append (.commit name owner endFresh endGuard endTail) suffix).symm)
              (piece.liftPoint (SourceProgram.commit name owner endFresh endGuard
                (endTail.prepend suffix))
                (ProtocolState.entry (SourceProgram.commit name owner endFresh endGuard
                  (endTail.prepend suffix)) endSource))))) controls)).map
            (fun sampled => PublicationResult.success
              (phaseRecoveryDomainValue setup .concurrent (embedding.event position)
                owner ty typed sampled.val.val))) := by
    revert typed controls
    revert endFresh endGuard endTail endSource embedding wholeViews position atEnd
    induction piece with
    | nil =>
        intro endFresh endGuard endTail endSource embedding wholeViews position atEnd typed controls
        rcases position with ⟨value, bound⟩
        have zero : value = 0 := atEnd
        cases zero
        rfl
    | @commit Γ O Ξ R prior actor priorTy freshBefore guardBefore remaining ih =>
        intro endFresh endGuard endTail endSource embedding wholeViews position atEnd typed controls
        let terminal := SourceProgram.CommitPrefix.commit name owner endFresh endGuard endTail
        obtain ⟨tail, rfl⟩ :
            ∃ tail : Fin (eventCount ((remaining.append terminal).prepend suffix)),
              position = Fin.succ tail := by
          refine ⟨⟨position.val - 1, ?_⟩, ?_⟩
          · have bound := position.isLt
            change position.val <
              eventCount ((remaining.append terminal).prepend suffix) + 1 at bound
            change position.val = remaining.length + 1 at atEnd
            omega
          · apply Fin.ext
            change position.val = position.val - 1 + 1
            change position.val = remaining.length + 1 at atEnd
            omega
        have tailPosition : tail.val = remaining.length := by
          change tail.val + 1 = remaining.length + 1 at atEnd
          omega
        have transported := SourceProgram.CommitPrefix.afterCommit_cast_tail
          freshBefore guardBefore (remaining.prepend_append terminal suffix)
            (ordinaryBlockProfile setup .concurrent implementation.plan values
              ((SourceProgram.CommitPrefix.commit prior actor freshBefore guardBefore
                remaining).append terminal) suffix embedding wholeViews controls
                  control.execution.application.publicView
                    (PhaseProposal.sourceArchive control.execution.network.inputs))
        simp only [SourceProgram.CommitPrefix.tailProfile] at ⊢
        rw [transported]
        have castTail
            {left right : SourceProgram Player L ((prior, .commitment actor priorTy) :: Γ)
              (insert prior O)}
            (same : left = right) (point : ProtocolState left) :
            cast (congrArg ProtocolState
              (congrArg (SourceProgram.commit prior actor freshBefore guardBefore) same))
                (Sum.inr point) = Sum.inr (cast (congrArg ProtocolState same) point) := by
          cases same
          rfl
        let originalView := ProtocolState.observe owner
          (((SourceProgram.CommitPrefix.commit prior actor freshBefore guardBefore remaining).append
            terminal).prepend suffix)
          (cast (congrArg ProtocolState
            ((SourceProgram.CommitPrefix.commit prior actor freshBefore guardBefore
              remaining).prepend_append terminal suffix).symm)
            ((SourceProgram.CommitPrefix.commit prior actor freshBefore guardBefore
              remaining).liftPoint (terminal.prepend suffix)
              (ProtocolState.entry (terminal.prepend suffix) endSource)))
        have observation : originalView = Sum.inr
            (ProtocolState.observe owner ((remaining.append terminal).prepend suffix)
              (cast (congrArg ProtocolState (remaining.prepend_append terminal suffix).symm)
                (remaining.liftPoint (terminal.prepend suffix)
                  (ProtocolState.entry (terminal.prepend suffix) endSource)))) := by
          change ProtocolState.observe owner
            (SourceProgram.commit prior actor freshBefore guardBefore
              ((remaining.append terminal).prepend suffix))
            (cast (congrArg ProtocolState
              (congrArg (SourceProgram.commit prior actor freshBefore guardBefore)
                (remaining.prepend_append terminal suffix).symm))
                (Sum.inr (remaining.liftPoint (terminal.prepend suffix)
                  (ProtocolState.entry (terminal.prepend suffix) endSource)))) = _
          rw [castTail (remaining.prepend_append terminal suffix).symm]
          rfl
        let drawAt := fun view : ProtocolView owner setup.program =>
          (values owner (queryAt view controls)).map (fun sampled => PublicationResult.success
            (phaseRecoveryDomainValue setup .concurrent (embedding.event tail.succ)
              owner ty typed sampled.val.val))
        change _ = (if owner ∈ controls.1 then PMF.pure .failure else
          drawAt (wholeViews owner originalView))
        rw [observation]
        exact ih endFresh endGuard endTail endSource
          (embedding.tail ((remaining.append terminal).prepend suffix)
            (by rfl) (fun _ => rfl))
          (fun actor view => wholeViews actor (.inr view)) tail tailPosition typed controls
  have row := structuralRow first fresh guard last middleSource cursor.embedding
    (fun actor view => cursor.views.view actor view) selectedIndex firstSize.symm
      (selectedEq.symm ▸ shape)
      (control.execution.application.entry.excluded,
        control.execution.application.generation,
        control.execution.application.attempt.phase)
  have wholeObservation : cursor.views.view owner
      (ProtocolState.observe owner ((first.append head).prepend suffix)
        (cast (congrArg ProtocolState association.symm)
          (first.liftPoint (head.prepend suffix)
            (ProtocolState.entry (head.prepend suffix) middleSource)))) =
      ProtocolState.observe owner setup.program sourceCurrent.point := by
    rw [← cursor.views.observe, sourceCurrentEq, middlePoint]
  let payloadLaw := fun key : setup.ProposalRecoveryComponent owner =>
    (values owner key).map (fun sampled => PublicationResult.success
      (phaseRecoveryDomainValue setup .concurrent (cursor.embedding.event selectedIndex)
        owner ty (selectedEq.symm ▸ shape) sampled.val.val))
  change _ = (if owner ∈ control.execution.application.entry.excluded then PMF.pure .failure
    else payloadLaw (queryAt
      (cursor.views.view owner (ProtocolState.observe owner ((first.append head).prepend suffix)
        (cast (congrArg ProtocolState association.symm)
          (first.liftPoint (head.prepend suffix)
            (ProtocolState.entry (head.prepend suffix) middleSource)))))
      (control.execution.application.entry.excluded, control.execution.application.generation,
        control.execution.application.attempt.phase))) at row
  rw [wholeObservation] at row
  have active : owner ∉ control.execution.application.entry.excluded := by
    have mask := congrArg Prod.fst controlsRead
    change sourceCurrent.excluded = control.execution.application.entry.excluded at mask
    exact (congrArg (fun excluded : Finset Player => owner ∉ excluded) mask).mp surviving
  rw [ite_eq_right active] at row
  have queryRead := ordinary_source_query_readback setup owner sourceCurrent sourceTrace
    surviving live
  rw [controlsRead, addressRead, archiveRead] at queryRead
  change queryAt (ProtocolState.observe owner setup.program sourceCurrent.point)
    (control.execution.application.entry.excluded, control.execution.application.generation,
      control.execution.application.attempt.phase) =
        setup.proposalRecoveryQuery owner
          (setup.proposalRecoveryModel.infoOf owner sourceTrace) at queryRead
  rw [queryRead] at row
  rw [row]
  dsimp only [payloadLaw]
  simp only [selectedEq]
  simp only [PMF.map_comp, Function.comp_def]
  apply congrArg (fun transform =>
    (values owner (setup.proposalRecoveryQuery owner
      (setup.proposalRecoveryModel.infoOf owner sourceTrace))).map transform)
  funext sampled
  let value := phaseRecoveryDomainValue setup .concurrent named owner ty shape sampled.val.val
  let decodeProperty := fun {context : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L context names) =>
    ∀ (position : Fin (eventCount program)), position.val = first.length →
      ∀ (typed : outputLayout program position = .binding owner ty),
        decodeEventAction program position
          (cast (congrArg EventField.Action typed.symm) (.success value)) =
            some (.commit owner name ty (.success value))
  have localDecoder : decodeProperty (first.prepend (head.prepend suffix)) := by
    intro position atEnd typed
    have decoded := decodeCommitPrefix_binding fresh guard (last.prepend suffix) first
      position atEnd typed
        (cast (congrArg EventField.Action typed.symm) (PublicationResult.success value))
    simpa only [head, SourceProgram.CommitPrefix.prepend, cast_cast, cast_eq] using decoded
  have wholeDecoder : decodeProperty ((first.append head).prepend suffix) :=
    association.symm ▸ localDecoder
  have decoded := cursor.views.actionEq selectedIndex
    (cast (congrArg EventField.Action (selectedEq.symm ▸ shape).symm)
      (PublicationResult.success value))
  have localTyped : outputLayout ((first.append head).prepend suffix) selectedIndex =
      .binding owner ty :=
    (cursor.embedding.layout_eq selectedIndex).symm.trans (selectedEq.symm ▸ shape)
  have decoderValue : decodeEventAction setup.program (cursor.embedding.event selectedIndex)
      (cast (congrArg EventField.Action (selectedEq.symm ▸ shape).symm)
        (PublicationResult.success value)) =
        some (.commit owner name ty (.success value)) := by
    calc
      _ = decodeEventAction ((first.append head).prepend suffix) selectedIndex
          (cast (congrArg EventField.Action localTyped.symm)
            (PublicationResult.success value)) := by
        simpa only [cast_cast] using decoded
      _ = _ := wholeDecoder selectedIndex firstSize.symm localTyped
  have eventDecoder {left right : (serviceGraph setup .concurrent).EventId}
      (same : left = right)
      (binding : (serviceGraph setup .concurrent).outputLayout right = .binding owner ty)
      (value : L.Val ty) :
      decodeEventAction setup.program left
          (cast (congrArg EventField.Action (same.symm ▸ binding).symm)
            (PublicationResult.success value)) =
        decodeEventAction setup.program right
          (cast (congrArg EventField.Action binding.symm) (PublicationResult.success value)) := by
    cases same
    rfl
  exact decoderValue.symm.trans (eventDecoder selectedEq shape value)

/-- The true-bit mass of the original ordinary foreign joint is the literal
current foreign queried-draw product of this same supported raw replay. -/
private theorem sourceReplay_issued_binding_word_atom
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    {Δ : SourceCtx Player L} {Q : Finset VarId}
    (suffix : SourceProgram Player L Δ Q)
    (wordBlock : SourceProgram.CommitPrefix
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.context
      (checkpointSelection setup implementation operational
        trace).val.checkpoint.residual.names Δ Q)
    (reconstruct : wordBlock.prepend suffix =
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.tail)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan control phase wordBlock suffix)
    (referenceWord : SourceProgram.Config Player L Δ)
    (owner : Player) (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (drawnValue : L.Val ty)
    (selectedLow : control.execution.application.attempt.phase ≤ named.val)
    (selectedHigh : named.val < control.execution.application.attempt.phase + wordBlock.length)
    (encodedResult : (phaseRecoveryBindingData setup .concurrent named owner ty shape
      (CommitRecoveryMove.lift (wordBlock.wordAction owner
        (named.val - control.execution.application.attempt.phase) (referenceWord.view owner)))).1 =
      .success drawnValue)
    (key : setup.ProposalRecoveryComponent owner) :
    ((values owner key).map (fun sampled =>
      decodeEventAction setup.program named
        (cast (congrArg EventField.Action shape.symm) (.success
          (phaseRecoveryDomainValue setup .concurrent named owner ty shape sampled.val.val)))))
      (wordBlock.wordAction owner (named.val - control.execution.application.attempt.phase)
        (referenceWord.view owner)) =
      ((values owner key).map (fun sampled =>
        phaseRecoveryDomainValue setup .concurrent named owner ty shape sampled.val.val))
          drawnValue := by
  classical
  let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
  have offset : cursor.offset = control.execution.application.attempt.phase := by
    have firstCount := cursor.compiled.countEq
    have selectedCount := checkpoint.compiled.countEq
    change cursor.offset + eventCount (wordBlock.prepend suffix) = eventCount setup.program
      at firstCount
    change control.execution.application.attempt.phase +
      eventCount checkpoint.residual.tail = eventCount setup.program at selectedCount
    rw [← reconstruct] at selectedCount
    omega
  let selectedIndex : Fin (eventCount (wordBlock.prepend suffix)) :=
    ⟨named.val - control.execution.application.attempt.phase, by
      have count := wordBlock.eventCount_prepend suffix
      omega⟩
  have selectedBound : selectedIndex.val < wordBlock.length := by
    dsimp only [selectedIndex]
    omega
  have selectedEq : cursor.embedding.event selectedIndex = named := by
    apply Fin.ext
    rw [cursor.compiled.rankEq, offset]
    dsimp only [selectedIndex]
    omega
  have codec := phaseCommitWordAction_decode setup .concurrent wordBlock suffix
    cursor.embedding cursor.views.actionEq owner selectedIndex selectedBound ty
      (selectedEq.symm ▸ shape) (referenceWord.view owner)
  have transportCodec {left right : (serviceGraph setup .concurrent).EventId}
      (same : left = right)
      (binding : (serviceGraph setup .concurrent).outputLayout right = .binding owner ty)
      (word : Option (OwnAction Player L)) :
      (decodeEventAction setup.program left
        (cast (congrArg EventField.Action (same.symm ▸ binding).symm)
          (phaseRecoveryBindingData setup .concurrent left owner ty
            (same.symm ▸ binding) (CommitRecoveryMove.lift word)).1) = word) →
      decodeEventAction setup.program right
        (cast (congrArg EventField.Action binding.symm)
          (phaseRecoveryBindingData setup .concurrent right owner ty binding
            (CommitRecoveryMove.lift word)).1) = word := by
    cases same
    exact id
  have codecNamed := transportCodec selectedEq shape
    (wordBlock.wordAction owner selectedIndex.val (referenceWord.view owner)) codec
  change decodeEventAction setup.program named
    (cast (congrArg EventField.Action shape.symm)
      (phaseRecoveryBindingData setup .concurrent named owner ty shape
        (CommitRecoveryMove.lift (wordBlock.wordAction owner
          (named.val - control.execution.application.attempt.phase)
            (referenceWord.view owner)))).1) =
      wordBlock.wordAction owner
        (named.val - control.execution.application.attempt.phase)
          (referenceWord.view owner) at codecNamed
  rw [encodedResult] at codecNamed
  rw [← codecNamed]
  have decodeInjective : Function.Injective (fun value : L.Val ty =>
      decodeEventAction setup.program named
        (cast (congrArg EventField.Action shape.symm) (.success value))) := by
    have inverse (value : L.Val ty) :
        (decodeEventAction setup.program named
          (cast (congrArg EventField.Action shape.symm) (.success value))).bind
            (encodeEventAction? setup.program named) =
              some (cast (congrArg EventField.Action shape.symm) (.success value)) := by
      let sourceEvent : Fin (eventCount setup.program) := ⟨named.val, named.isLt⟩
      have sourceShape : outputLayout setup.program sourceEvent = .binding owner ty :=
        shape
      have decoded := SourceProgram.decodeEventAction_binding_cell setup.program
        sourceEvent.val sourceEvent.isLt sourceShape (PublicationResult.success value)
      have encoding := encodeEventAction?_decodeEventAction_eq_some setup.program
        sourceEvent _ _ decoded
      have transported := congrArg (fun result : Option (OwnAction Player L) =>
        result.bind (encodeEventAction? setup.program sourceEvent)) decoded
      exact transported.trans encoding
    intro left right same
    have encoded := congrArg (fun action => action.bind
      (encodeEventAction? setup.program named)) same
    have encodedValues := (inverse left).symm.trans (encoded.trans (inverse right))
    have raw := congrArg (cast (congrArg EventField.Action shape))
      (Option.some.inj encodedValues)
    simpa only [cast_cast, cast_eq, PublicationResult.success.injEq] using raw
  simpa only [PMF.map_comp, Function.comp_def] using
    (pmf_map_apply_of_injective
      ((values owner key).map
          (fun sampled => phaseRecoveryDomainValue setup .concurrent named owner ty shape
            sampled.val.val)) decodeInjective drawnValue)

private theorem sourceReplay_current_issued_source_product
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (who : Player) (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (acting : reference.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who
      (reference.execution.recall who)
      (reference.execution.observe nativeApplication who) event payload)
    (good : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner ⟨some reference, referenceTrace⟩)
    (entry : NativeBindingEntry setup implementation operational reference referenceTrace
      who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who
        (entry.canonicalCut setup values implementation operational fullValues reference
          referenceTrace who acting event payload clean good).trace)
    (sourceGood : setup.proposalRecoveryForeignGood who g)
    (sourceChoice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, sourceChoice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (supported : (⟨some targetCurrent, targetTrace⟩ :
      setup.proposalRecoveryProtocol.History) ∈
        (sourceForcedBlock setup values who g sourceChoice).support)
    (scale nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (law : SourceRawReplayLaw (setup := setup) (values := values)
      (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩ reference
        ⟨some reference, referenceTrace⟩)
    (script : List (RawReplayChoice setup implementation))
    (member : script ∈ law.choices.support)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (actualReplay : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
      reference ⟨some reference, referenceTrace⟩ script = some ⟨some control, trace⟩)
    {Δ : SourceCtx Player L} {Q : Finset VarId}
    (suffix : SourceProgram Player L Δ Q)
    (wordBlock : SourceProgram.CommitPrefix
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.context
      (checkpointSelection setup implementation operational
        trace).val.checkpoint.residual.names Δ Q)
    (reconstruct : wordBlock.prepend suffix =
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.tail)
    (boundary : IsCommitBoundary suffix)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan control phase wordBlock suffix)
    (positive : 0 < wordBlock.length)
    (ordinarySupported : (⟨some targetCurrent, targetTrace⟩ :
      setup.proposalRecoveryProtocol.History) ∈
      (setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup values)
        wordBlock.length ⟨some cursor.current, cursor.trace⟩).support)
    (referenceWord : SourceProgram.Config Player L Δ)
    (referenceSupported : referenceWord ∈ (wordBlock.prefixLaw suffix
      (ordinaryBlockProfile setup .concurrent implementation.plan values wordBlock suffix
        cursor.embedding (fun owner view => cursor.views.view owner view)
        (control.execution.application.entry.excluded, control.execution.application.generation,
          control.execution.application.attempt.phase)
        control.execution.application.publicView
        (PhaseProposal.sourceArchive control.execution.network.inputs)) cursor.source).support)
    (ledger : ∀ owner, issuedLedger setup implementation wordBlock
      control.execution.application.attempt.phase control
        (control.execution.application.attempt.phase + wordBlock.length) owner
          (referenceWord.view owner))
    (finished : SourceProgram.Config Player L Δ)
    (attempt : wordBlock.Attempt cursor.source cursor.current.excluded finished
      targetCurrent.excluded)
    (finishedPoint : targetCurrent.point = cursor.lift
      (wordBlock.liftPoint suffix (ProtocolState.entry suffix finished)))
    (exclusions : targetCurrent.excluded = cursor.current.excluded)
    (referenceEq : referenceWord = attempt.withoutMisses ∅ cursor.source) :
    sourceReplayIssuedSourceProduct setup implementation wordBlock suffix
      (ordinaryBlockProfile setup .concurrent implementation.plan values wordBlock suffix
        cursor.embedding (fun owner view => cursor.views.view owner view)
        (control.execution.application.entry.excluded, control.execution.application.generation,
          control.execution.application.attempt.phase)
        control.execution.application.publicView
        (PhaseProposal.sourceArchive control.execution.network.inputs)) cursor.source
      control.execution.application.attempt.phase control who referenceWord =
        sourceReplayCurrentIssuedProduct setup values implementation who ⟨some control, trace⟩ := by
  classical
  obtain ⟨selectedAgreement, completedVisits⟩ :=
    sourceReplayCorrespondence setup values implementation operational fullValues who reference
      referenceTrace acting event payload clean good entry g sameInfo sourceGood sourceChoice
        properChoice targetCurrent targetTrace supported
  obtain ⟨image, imageReplay, imageRelated, _imageMechanical, _imageGood⟩ :=
    law.replayed script member
  have imageEq : image = ⟨some control, trace⟩ :=
    Option.some.inj (imageReplay.symm.trans actualReplay)
  rw [imageEq] at imageRelated
  simp only [sourceReplayIssuedSourceProduct, sourceReplayCurrentIssuedProduct]
  apply Finset.prod_congr rfl
  intro owner _member
  by_cases focal : owner = who
  · simp only [focal, ite_true]
  · simp only [focal, ite_false]
    rw [Finset.prod_range, ← Fin.prod_univ_fun_getElem]
    conv_rhs =>
      rw [← Fin.prod_congr' _ (show (control.execution.recall owner).length =
        ((control.execution.recall owner).zipIdx).length from List.length_zipIdx.symm)]
    simp only [List.getElem_zipIdx, Nat.zero_add]
    apply Finset.prod_congr rfl
    intro index _indexed
    simp only [Fin.val_cast]
    rw [List.getElem?_eq_getElem index.isLt]
    cases emitted : (control.execution.recall owner)[index.val].emitted with
    | none => simp only [sourceIssuedRecordPosition, emitted]
    | some message =>
      by_cases signed : message.payload.attempt = control.execution.application.attempt
      · cases call : message.payload.packet.call with
        | opening => simp only [sourceIssuedRecordPosition, emitted, signed, ite_true, call]
        | malformed => simp only [sourceIssuedRecordPosition, emitted, signed, ite_true, call]
        | commitment named handle =>
          have recorded : (control.execution.recall owner)[index.val] ∈
              control.execution.recall owner := List.getElem_mem index.isLt
          have output : message ∈ (nativeApplication).outputs (control.execution.recall owner) :=
            List.mem_filterMap.mpr ⟨_, recorded, emitted⟩
          have recalled := (nativeApplication).history_inputRecall nativeInitial
            implementation.horizon implementation.scheduler
              ((nativeMenu).toRawTrace nativeInitial implementation.horizon
                implementation.scheduler trace) owner
          have input : message ∈ control.execution.network.inputs := by
            rw [← recalled] at output
            exact (List.mem_filter.mp output).1
          have sender : message.sender = owner := by
            rw [← recalled] at output
            simpa only [decide_eq_true_eq] using (List.mem_filter.mp output).2
          have initialEq : nativeInitial = (setup.initialLaw.map encodeInputs).map
              (PhaseRuntimeState.initial implementation.plan) := by
            simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
          have physical := PhaseCount.physicalBindings_history implementation.runtime
            implementation.leaks implementation.bounds implementation.plan
              (setup.initialLaw.map encodeInputs) implementation.horizon
                implementation.scheduler (initialEq ▸ trace)
          have correct := ((PhaseCount.permits_eq_true_iff _ _).mp
            (physical.clean.2 message input)).2.1
          change CountCallCorrect _ (PhaseCount.nativeMessage message) at correct
          simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
          obtain ⟨owned, _evidenceFree, _candidateOwner, _preparedSlot, _unused⟩ := correct
          change bindingOwnedBy (serviceGraph setup .concurrent) message.sender named =
            true at owned
          rw [sender] at owned
          obtain ⟨ty, shape⟩ : ∃ ty,
              (serviceGraph setup .concurrent).outputLayout named = .binding owner ty := by
            cases layout : (serviceGraph setup .concurrent).outputLayout named with
            | binding actor ty =>
                have same : actor = owner := by
                  simpa only [bindingOwnedBy, layout, decide_eq_true_eq] using owned
                subst actor
                exact ⟨ty, rfl⟩
            | publicData ty => simp only [bindingOwnedBy, layout, Bool.false_eq_true] at owned
            | privateInput actor ty =>
                simp only [bindingOwnedBy, layout, Bool.false_eq_true] at owned
            | publication ty => simp only [bindingOwnedBy, layout, Bool.false_eq_true] at owned
          obtain ⟨serial, opening, evidence, handleEq, _sender, action, _fresh, signedNamespace,
            meaning⟩ := sourceReplay_recorded_binding_registration setup implementation control
              trace owner _ recorded message emitted named ty shape handle call
          obtain ⟨before, after, prior, joint, legal, moved, earlier, earlierMass, actualBefore,
            actualPrior, _actualAfter, kernel, choice, originalKept, actualKept, beforeActing,
            earlierSupported,
            earlierReplay, related, restricted, _afterReplay, _afterKept, _afterRelated,
            _afterRestricted, atoms, _description, choiceSupported,
            choiceAction, past, viewed⟩ :=
            sourceReplay_recorded_foreign_callback setup values implementation scale who
              ⟨some targetCurrent, targetTrace⟩ reference ⟨some reference, referenceTrace⟩
                ⟨some control, trace⟩ ⟨some reference, referenceTrace⟩ script (law.choices script)
                  (law.atoms script member) .refl control trace actualReplay .refl owner focal
                    index.val index.isLt imageRelated (law.restricted script member)
          obtain ⟨_tag, response, responseEq, proper, _form⟩ := atoms choice choiceSupported
          have responseAction : response.val = (control.execution.recall owner)[index.val].action :=
            Option.some.inj (responseEq.symm.trans choiceAction)
          have actualActing : actualBefore.actor = some owner := related.2.1.trans beforeActing
          let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
            ⟨⟨.commitment named (owner, .prepared serial), opening⟩, evidence⟩
          have transmitted : response.val.transmission = some material :=
            congrArg ReactiveApplication.Action.transmission (responseAction.trans action)
          have activeTrace : (nativeProtocol).Trace
              (some ⟨actualBefore.remaining, some owner, actualBefore.execution⟩) := by
            have state : actualBefore =
                ⟨actualBefore.remaining, some owner, actualBefore.execution⟩ := by
              cases actualBefore
              cases actualActing
              rfl
            exact state ▸ actualPrior
          obtain ⟨otherTy, otherShape, key, otherSerial, drawnValue, _slot, request, queried,
            prepared, _baseAtom, _responseAtom⟩ := sourceReplay_proper_callback_atom setup values
              implementation operational fullValues ⟨nativeBad, scale, scale, scale⟩
                scalePositive scaleBelow scalePositive nativeBadPositive nativeBadBelow
                  actualBefore.remaining owner actualBefore.execution activeTrace response proper
                    material transmitted named (owner, .prepared serial) rfl choice.1
          have typeEq : ty = otherTy := (EventField.binding.inj (shape.symm.trans otherShape)).2
          subst otherTy
          have beforeKept : TracePrefix prior referenceTrace :=
            (TracePrefix.extend .refl joint legal moved).trans originalKept
          have application := congrArg (fun execution : (nativeApplication).Execution =>
            execution.application) related.2.2.1
          have network := congrArg (fun execution : (nativeApplication).Execution =>
            execution.network) related.2.2.1
          have receipts := congrArg (fun execution : (nativeApplication).Execution =>
            execution.receipts) related.2.2.1
          have environmentRecall := congrArg (fun execution : (nativeApplication).Execution =>
            execution.environmentRecall) related.2.2.1
          obtain ⟨sourceCurrent, sourceTrace, sourceKept, sourceRank, sourceGeneration,
            sourceSaved, surviving, sourceQuery⟩ := sourceReplay_query_binding setup values
              implementation operational fullValues who reference referenceTrace acting event
                payload
                clean good entry g sameInfo sourceGood sourceChoice properChoice targetCurrent
                  targetTrace supported selectedAgreement completedVisits
                    (rawReplayLost setup implementation earlier) restricted before prior beforeKept
                      actualBefore actualPrior owner focal named ty shape actualActing application
                        network receipts environmentRecall related.2.2.2.1 request
          have keyEq : key = setup.proposalRecoveryQuery owner
              (setup.proposalRecoveryModel.infoOf owner sourceTrace) :=
            Option.some.inj (queried.symm.trans sourceQuery)
          have typedDraw : sourceReplayBindingDrawAtom setup values implementation owner
              ((control.execution.recall owner).take index.val)
                (control.execution.recall owner)[index.val].beforeView
                  (control.execution.recall owner)[index.val].action =
              ((values owner (setup.proposalRecoveryQuery owner
                (setup.proposalRecoveryModel.infoOf owner sourceTrace))).map (fun sampled =>
                  phaseRecoveryDomainValue setup .concurrent named owner ty shape
                    sampled.val.val)) drawnValue := by
            rw [← past, viewed, ← responseAction]
            simp only [sourceReplayBindingDrawAtom, transmitted, material, prepared,
              dite_eq_left otherShape, queried, keyEq]
          rw [typedDraw]
          have sameAttempt : actualBefore.execution.application.attempt =
              control.execution.application.attempt := by
            rw [viewed] at signedNamespace
            change actualBefore.execution.application.attempt = message.payload.attempt
              at signedNamespace
            exact signedNamespace.trans signed
          have sourceCurrentGeneration : sourceCurrent.generation =
              control.execution.application.generation := by
            have beforeGeneration := congrArg PhaseRuntimeState.generation application
            have callbackGeneration := congrArg CommitAttemptId.generation sameAttempt
            change actualBefore.execution.application.generation =
              control.execution.application.generation at callbackGeneration
            change actualBefore.execution.application.generation =
              before.execution.application.generation at beforeGeneration
            exact sourceGeneration.trans (beforeGeneration.symm.trans callbackGeneration)
          have responseMaterial : response.val = (⟨some material⟩ :
              (nativeApplication).Action) :=
            congrArg (fun selected => (⟨selected⟩ : (nativeApplication).Action)) transmitted
          have available : (⟨some material⟩ : (nativeApplication).Action) ∈
              PhaseCount.onePacketActions implementation.runtime implementation.leaks
                implementation.bounds owner (actualBefore.execution.recall owner)
                  (actualBefore.execution.observe nativeApplication owner) :=
            responseMaterial ▸ response.property
          have rawOpening := properBinding_opening setup material named
            (owner, .prepared serial) owner ty shape drawnValue rfl prepared
          have opened : opening = some (⟨ty, drawnValue⟩ : Raw L) := rawOpening
          have meaningValue : control.execution.application.current.native.bindingResult handle ty =
              .success drawnValue := by
            rw [meaning, opened]
            simp only [Option.bind_some, Raw.as?_mk, Option.elim_some]
          have unsent := PhaseCount.unsent_of_nonsilent implementation.runtime implementation.leaks
            implementation.bounds implementation.plan
              (serviceGraph_revealRelaxedOrdered setup .concurrent)
                (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
                  actualBefore.remaining owner actualBefore.execution (initialEq ▸ activeTrace)
                    ⟨actualBefore.execution.application.attempt, named⟩ request material available
          obtain ⟨selectedLow, selectedHigh, conditional⟩ :=
            sourceReplay_issued_source_callback_atom setup values implementation operational control
              trace suffix wordBlock reconstruct.symm boundary phase cursor positive targetCurrent
              targetTrace ordinarySupported referenceWord
              referenceSupported ledger finished attempt finishedPoint exclusions referenceEq owner
              index.val named ty shape actualBefore actualPrior actualKept past
              sameAttempt unsent request sourceCurrent sourceTrace sourceKept sourceRank
              sourceCurrentGeneration surviving
          have registrationPosition : sourceIssuedRecordPosition setup implementation wordBlock
              control.execution.application.attempt.phase control owner
                (control.execution.recall owner)[index.val] =
                  some (named.val - control.execution.application.attempt.phase) := by
            simp only [sourceIssuedRecordPosition, emitted, signed, ite_true, call]
            exact ite_eq_left ⟨selectedLow, selectedHigh, ty, shape⟩
          dsimp only
          rw [registrationPosition]
          dsimp only
          simp only [signed, ite_true, call]
          rw [conditional]
          have encodedResult := (issuedLedger_iff_binding_results setup implementation wordBlock
            control.execution.application.attempt.phase control trace
              (control.execution.application.attempt.phase + wordBlock.length) owner
                (referenceWord.view owner)).mp (ledger owner) named ty shape handle message output
                  signed call ⟨selectedLow, selectedHigh⟩
          rw [meaningValue] at encodedResult
          exact sourceReplay_issued_binding_word_atom setup values implementation operational
            control trace suffix wordBlock reconstruct phase cursor referenceWord owner named ty
              shape drawnValue selectedLow selectedHigh encodedResult
                (setup.proposalRecoveryQuery owner
                  (setup.proposalRecoveryModel.infoOf owner sourceTrace))
      · simp only [sourceIssuedRecordPosition, emitted, signed, ite_false]

theorem sourceRawReplay_current_issued_mass
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (who : Player) (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (acting : reference.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who
      (reference.execution.recall who)
      (reference.execution.observe nativeApplication who) event payload)
    (good : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner ⟨some reference, referenceTrace⟩)
    (entry : NativeBindingEntry setup implementation operational reference referenceTrace
      who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who
        (entry.canonicalCut setup values implementation operational fullValues reference
          referenceTrace who acting event payload clean good).trace)
    (sourceGood : setup.proposalRecoveryForeignGood who g)
    (sourceChoice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, sourceChoice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (supported : (⟨some targetCurrent, targetTrace⟩ :
      setup.proposalRecoveryProtocol.History) ∈
        (sourceForcedBlock setup values who g sourceChoice).support)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativeProfile : ∀ owner, ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).BehavioralPolicy owner)
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        nativeInitial implementation.horizon implementation.scheduler values
          ⟨nativeBad, scale, scale, scale⟩)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (referenceInformation : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).infoOf who referenceTrace = site.1)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site
      (reference.execution.recall who) (reference.execution.observe nativeApplication who)
        event payload clean.binding)
    (gInfo : setup.proposalRecoveryModel.infoOf who g.trace = source.site.1)
    (value : L.Val payload)
    (encoded : sourceChoice = gInfo.symm ▸ source.encode value)
    (law : SourceRawReplayLaw (setup := setup) (values := values)
      (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩ reference
        ⟨some reference, referenceTrace⟩)
    (script : List (RawReplayChoice setup implementation))
    (member : script ∈ law.choices.support)
    (actual : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationHistory who
        (((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).infoOf who referenceTrace))
    (replayed : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
      reference ⟨some reference, referenceTrace⟩ script = some actual.val)
    (nativePositive : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).historyReachWeight nativeProfile actual.val ≠ 0)
    (actualGood : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner actual.val)
    (actualAlive : actual.val.state.elim True (fun control =>
      who ∉ control.execution.application.current.excluded))
    (q : setup.proposalRecoveryProtocol.History)
    (qKept : TracePrefix q.trace g.trace)
    (qDepth : q.trace.length =
      (canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩).trace.length)
    (sameKey : setup.proposalRecoveryClosedKey who
        (canonicalSource setup implementation operational actual.val) =
      setup.proposalRecoveryClosedKey who q) :
    ((ordinaryForeignJoint setup values implementation operational who actual.val q).map
      Prod.snd) true =
        sourceReplayCurrentIssuedProduct setup values implementation who actual.val := by
  classical
  obtain ⟨control, trace, actualEq, phase, cursor, cursorEq, positive, embedding, lift, views,
    ordinarySupported, referenceWord, referenceSupported, ledger, finished, attempt,
    finishedPoint, exclusions, targetWord, targetLabels, referenceEq⟩ :=
    sourceRawReplay_ordinary_completion setup values implementation operational fullValues who
      reference referenceTrace acting event payload clean good entry g sameInfo sourceGood
      sourceChoice properChoice targetCurrent targetTrace supported scale sourceBad nativeBad
      scalePositive scaleBelow sourceBadPositive sourceBadBelow nativeBadPositive nativeBadBelow
      sourceProfile sourcePrescribed nativeProfile nativePrescribed site referenceInformation
      source gInfo value encoded law script member actual replayed nativePositive actualGood
      actualAlive q qKept qDepth sameKey
  let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
  have actualReplay : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
      reference ⟨some reference, referenceTrace⟩ script = some ⟨some control, trace⟩ := by
    simpa only [actualEq] using replayed
  have mass := ordinaryForeignJoint_issued_source_product setup values implementation operational
    who control trace phase cursor positive embedding lift views referenceWord referenceSupported
      (fun owner _different => ledger owner)
  rw [actualEq, ← cursorEq, mass]
  clear mass
  generalize blockEq : SourceProgram.commitPhase checkpoint.residual.tail = segment
    at cursor cursorEq positive embedding lift views ordinarySupported referenceWord
      referenceSupported ledger finished attempt finishedPoint exclusions targetWord targetLabels
      referenceEq ⊢
  rcases segment with ⟨Δ, Q, suffix, wordBlock, reconstruct, boundary⟩
  dsimp only at cursor cursorEq positive embedding lift views ordinarySupported
  dsimp only at referenceWord referenceSupported ledger finished attempt finishedPoint exclusions
  dsimp only at targetWord targetLabels referenceEq ⊢
  exact sourceReplay_current_issued_source_product setup values implementation operational
    fullValues who reference referenceTrace acting event payload clean good entry g sameInfo
      sourceGood sourceChoice properChoice targetCurrent targetTrace supported scale nativeBad
        scalePositive scaleBelow nativeBadPositive nativeBadBelow law script member control trace
          actualReplay suffix wordBlock reconstruct boundary phase cursor positive
            (by simpa only [cursorEq] using ordinarySupported) referenceWord referenceSupported
              ledger finished attempt finishedPoint exclusions referenceEq

-- END CURRENT ISSUED QUERY PRODUCT

open Classical in
/-- Literal historical registrations are separated by their permanent
acceptance receipt. Each factor retains its original callback occurrence. -/
private def sourceReplayHistoricalDrawProducts (who : Player)
    (history : (nativeProtocol).History) : ℝ≥0∞ × ℝ≥0∞ :=
  match history.state with
  | none => (1, 1)
  | some control => ∏ owner, if owner = who then (1, 1) else
      (((control.execution.recall owner).zipIdx).map fun indexed =>
        match indexed.1.emitted with
        | none => (1, 1)
        | some message =>
            if message.payload.attempt = control.execution.application.attempt then (1, 1) else
              match message.payload.packet.call with
              | .commitment event _ =>
                  let draw := sourceReplayBindingDrawAtom setup values implementation owner
                    ((control.execution.recall owner).take indexed.2)
                      indexed.1.beforeView indexed.1.action
                  if PhaseService.BindingAccepted implementation.runtime implementation.leaks
                      ⟨message.payload.attempt, event⟩ owner control.execution then
                    (draw, 1) else (1, draw)
              | .opening .. | .malformed .. => (1, 1)).prod

open Classical in
/-- The product over the actual signed binding registrations. The finite
index is the chronological recall position, so equal values are not merged. -/
private def sourceReplayRegisteredDrawProduct (who : Player)
    (history : (nativeProtocol).History) : ℝ≥0∞ :=
  match history.state with
  | none => 1
  | some control => ∏ owner, if owner = who then 1 else
      (((control.execution.recall owner).zipIdx).map fun indexed =>
        match indexed.1.emitted with
        | none => 1
        | some message => match message.payload.packet.call with
          | .commitment _ _ => sourceReplayBindingDrawAtom setup values implementation owner
              ((control.execution.recall owner).take indexed.2)
                indexed.1.beforeView indexed.1.action
          | .opening .. | .malformed .. => 1).prod

/-- The signed occurrence partition is exhaustive and disjoint. Current
registrations and historical accepted or unaccepted registrations contribute
once each; no probability cancellation is used. -/
private theorem sourceReplay_registered_draw_partition
    (who : Player) (history : (nativeProtocol).History) :
    sourceReplayRegisteredDrawProduct setup values implementation who history =
      (sourceReplayHistoricalDrawProducts setup values implementation who history).1 *
        sourceReplayCurrentIssuedProduct setup values implementation who history *
          (sourceReplayHistoricalDrawProducts setup values implementation who history).2 := by
  classical
  rcases history with ⟨state, trace⟩
  cases state with
  | none => simp only [sourceReplayRegisteredDrawProduct, sourceReplayHistoricalDrawProducts,
      sourceReplayCurrentIssuedProduct, mul_one]
  | some control =>
      let factor (owner : Player) (indexed : (nativeApplication).PlayerEntry × Nat) :
          ℝ≥0∞ × ℝ≥0∞ :=
        match indexed.1.emitted with
        | none => (1, 1)
        | some message =>
            if message.payload.attempt = control.execution.application.attempt then (1, 1) else
              match message.payload.packet.call with
              | .commitment event _ =>
                  let draw := sourceReplayBindingDrawAtom setup values implementation owner
                    ((control.execution.recall owner).take indexed.2)
                      indexed.1.beforeView indexed.1.action
                  if PhaseService.BindingAccepted implementation.runtime implementation.leaks
                      ⟨message.payload.attempt, event⟩ owner control.execution then
                    (draw, 1) else (1, draw)
              | .opening .. | .malformed .. => (1, 1)
      let current (owner : Player) (indexed : (nativeApplication).PlayerEntry × Nat) : ℝ≥0∞ :=
        match indexed.1.emitted with
        | none => 1
        | some message =>
            if message.payload.attempt = control.execution.application.attempt then
              match message.payload.packet.call with
              | .commitment _ _ => sourceReplayBindingDrawAtom setup values implementation owner
                  ((control.execution.recall owner).take indexed.2)
                    indexed.1.beforeView indexed.1.action
              | .opening .. | .malformed .. => 1
            else 1
      let all (owner : Player) (indexed : (nativeApplication).PlayerEntry × Nat) : ℝ≥0∞ :=
        match indexed.1.emitted with
        | none => 1
        | some message => match message.payload.packet.call with
          | .commitment _ _ => sourceReplayBindingDrawAtom setup values implementation owner
              ((control.execution.recall owner).take indexed.2)
                indexed.1.beforeView indexed.1.action
          | .opening .. | .malformed .. => 1
      have split (owner : Player) (indexed : (nativeApplication).PlayerEntry × Nat) :
          all owner indexed = (factor owner indexed).1 * current owner indexed *
            (factor owner indexed).2 := by
        cases sent : indexed.1.emitted with
        | none => simp only [all, factor, current, sent, mul_one]
        | some message =>
            cases packet : message.payload.packet.call <;>
              simp only [all, factor, current, sent, packet] <;>
              split_ifs <;> simp only [mul_one, one_mul]
      have ownerSplit (owner : Player) :
          (((control.execution.recall owner).zipIdx).map (all owner)).prod =
            ((((control.execution.recall owner).zipIdx).map (factor owner)).prod).1 *
              (((control.execution.recall owner).zipIdx).map (current owner)).prod *
                ((((control.execution.recall owner).zipIdx).map (factor owner)).prod).2 := by
        have fold (entries : List ((nativeApplication).PlayerEntry × Nat)) :
            (entries.map (all owner)).prod =
              ((entries.map (factor owner)).prod).1 *
                (entries.map (current owner)).prod *
                  ((entries.map (factor owner)).prod).2 := by
          induction entries with
          | nil => simp
          | cons indexed rest ih =>
              simp only [List.map_cons, List.prod_cons, Prod.fst_mul, Prod.snd_mul,
                split owner indexed, ih]
              ring
        exact fold _
      change (∏ owner, if owner = who then 1 else
          (((control.execution.recall owner).zipIdx).map (all owner)).prod) =
        (∏ owner, if owner = who then (1, 1) else
          (((control.execution.recall owner).zipIdx).map (factor owner)).prod).1 *
        (∏ owner, if owner = who then 1 else
          (((control.execution.recall owner).zipIdx).map (current owner)).prod) *
        (∏ owner, if owner = who then (1, 1) else
          (((control.execution.recall owner).zipIdx).map (factor owner)).prod).2
      simp only [Prod.fst_prod, Prod.snd_prod]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro owner _member
      by_cases focal : owner = who
      · simp only [focal, ite_true, mul_one]
      · simpa only [focal, ite_false] using ownerSplit owner




/-- The auxiliary value tag changes no raw alias probability at the
same actual callback input and response class. -/
private theorem sourceReplay_alias_atom_tag
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (tag : Option (Handle (serviceGraph setup .concurrent) × Raw L))
    (action : (nativeApplication).Action)
    (offered : action ∈ PhaseCount.onePacketActions implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner)) :
    sourceReplayAliasAtom setup implementation scale owner execution (tag, some action) =
      sourceReplayAliasAtom setup implementation scale owner execution (none, some action) := by
  let response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner) := ⟨action, offered⟩
  simp only [sourceReplayAliasAtom, dite_eq_left offered]
  exact (sourceReplayAliases_atom setup implementation scale owner execution tag _ response).trans
    (sourceReplayAliases_atom setup implementation scale owner execution none _ response).symm

/-- A tagged lost draw is the actual callback's typed draw at that same
input. Untagged choices contribute one; the literal signed call fixes the event. -/
private theorem sourceReplay_lost_draw_at_actual_callback
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control) (original action : (nativeApplication).Action)
    (kernel : PMF (RawReplayChoice setup implementation))
    (atoms : SourceReplayCallbackAtoms (setup := setup) (values := values)
      (implementation := implementation) scale owner execution target reference original kernel)
    (choice : RawReplayChoice setup implementation) (supported : choice ∈ kernel.support)
    (selected : choice.2 = some action)
    (call : original.transmission.map (fun material => material.call.packet) =
      action.transmission.map (fun material => material.call.packet)) :
    sourceReplayLostDrawAtom setup values implementation owner execution original choice =
      if choice.1.isSome then
        sourceReplayBindingDrawAtom setup values implementation owner (execution.recall owner)
          (execution.observe nativeApplication owner) action
      else 1 := by
  classical
  obtain ⟨_tag, response, responseEq, _proper, aliases | lost⟩ := atoms choice supported
  · simp only [sourceReplayLostDrawAtom, aliases.1, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte]
  · obtain ⟨event, payload, binding, key, handle, value,
        ⟨material, transmitted, packet⟩, queried, drawn, prepared, _atom⟩ := lost
    have same : response.val = action := Option.some.inj (responseEq.symm.trans selected)
    rw [same] at prepared
    obtain ⟨actualMaterial, actualSent, actualPrepared⟩ := Option.bind_eq_some_iff.mp prepared
    have actualPacket : actualMaterial.call.packet = .commitment event handle := by
      simp only [transmitted, actualSent, Option.map_some, Option.some.injEq] at call
      exact call.symm.trans packet
    simp only [sourceReplayLostDrawAtom, sourceReplayBindingDrawAtom, drawn, transmitted,
      packet, actualSent, actualPacket, actualPrepared, Option.isSome_some, ↓reduceIte,
      dite_eq_left binding, queried]


/-- The actual callback kernel contributes its queried draw precisely at a
lost tag, and its genuine raw alias atom at every callback. -/
private theorem sourceReplay_callback_atom_partition
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control) (original action : (nativeApplication).Action)
    (kernel : PMF (RawReplayChoice setup implementation))
    (atoms : SourceReplayCallbackAtoms (setup := setup) (values := values)
      (implementation := implementation) scale owner execution target reference original kernel)
    (choice : RawReplayChoice setup implementation) (supported : choice ∈ kernel.support)
    (selected : choice.2 = some action)
    (call : original.transmission.map (fun material => material.call.packet) =
      action.transmission.map (fun material => material.call.packet)) :
    kernel choice =
      (if choice.1.isSome then
        sourceReplayBindingDrawAtom setup values implementation owner (execution.recall owner)
          (execution.observe nativeApplication owner) action
      else 1) *
        sourceReplayAliasAtom setup implementation scale owner execution (none, some action) := by
  classical
  obtain ⟨_tag, response, responseEq, _proper, _description⟩ := atoms choice supported
  have responseSame : response.val = action :=
    Option.some.inj (responseEq.symm.trans selected)
  have offered : action ∈ PhaseCount.onePacketActions implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner) := responseSame ▸ response.property
  have pair : choice = (choice.1, some action) := Prod.ext rfl selected
  have aliasEq : sourceReplayAliasAtom setup implementation scale owner execution choice =
      sourceReplayAliasAtom setup implementation scale owner execution (none, some action) := by
    calc
      _ = sourceReplayAliasAtom setup implementation scale owner execution
          (choice.1, some action) := congrArg _ pair
      _ = _ := sourceReplay_alias_atom_tag setup implementation scale owner execution choice.1
        action offered
  rw [sourceReplayCallbackAtoms_factor setup values implementation scale owner execution target
    reference original kernel atoms choice supported,
    sourceReplay_lost_draw_at_actual_callback setup values implementation scale owner execution
      target reference original action kernel atoms choice supported selected call, aliasEq]

/-- Both actual response products are finite products of nonnegative atoms. -/
private theorem sourceReplay_response_products_nonnegative
    (rates : PhaseProposalRates) (who : Player)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    0 ≤ (sourceReplayResponseProducts setup values implementation rates who trace).2.1 ∧
      0 ≤ (sourceReplayResponseProducts setup values implementation rates who trace).2.2 := by
  induction trace with
  | start => exact ⟨zero_le_one, zero_le_one⟩
  | @extend before after prior joint legal moved ih =>
    cases before with
    | none => simpa only [sourceReplayResponseProducts, mul_one] using ih
    | some control =>
      cases actor : control.actor with
      | none => simpa only [sourceReplayResponseProducts, actor, mul_one] using ih
      | some owner =>
        by_cases focal : owner = who
        · simpa only [sourceReplayResponseProducts, actor, focal, ↓reduceIte, mul_one] using ih
        · cases selected : joint owner with
          | none => simp only [sourceReplayResponseProducts, actor, focal, ↓reduceIte,
              selected, mul_zero, le_refl, and_self]
          | some action =>
            simpa only [sourceReplayResponseProducts, actor, focal, ↓reduceIte, selected] using
              And.intro (mul_nonneg ih.1 (ENNReal.toReal_nonneg (a :=
                sourceReplayBindingDrawAtom setup values implementation owner
                  (control.execution.recall owner)
                  (control.execution.observe nativeApplication owner) action)))
                (mul_nonneg ih.2 (ENNReal.toReal_nonneg (a := sourceReplayAliasAtom setup
                  implementation rates.aliases owner control.execution (none, some action))))

private theorem sourceReplay_foreign_own_play_extend
    (who : Player)
    (weight : ∀ owner, (nativeModel).InfoState owner × (nativeApplication).Action → ℝ≥0∞)
    {before after : (nativeProtocol).State} (prior : (nativeProtocol).Trace before)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support) :
    (∏ owner, if owner = who then 1 else
      (((nativeModel).ownPlay owner (prior.extend joint legal moved)).map (weight owner)).prod) =
      (∏ owner, if owner = who then 1 else
        (((nativeModel).ownPlay owner prior).map (weight owner)).prod) *
          ∏ owner, if owner = who then 1 else match joint owner with
            | none => 1
            | some action => weight owner ((nativeModel).infoOf owner prior, action) := by
  classical
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro owner _
  by_cases focal : owner = who
  · simp only [focal, ite_true, one_mul]
  · rw [ite_eq_right focal, ite_eq_right focal, ite_eq_right focal,
      InfoSignals.ownPlay_extend]
    cases selected : joint owner with
    | none => simp only [mul_one]
    | some action =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_comm _ _

private theorem sourceReplay_recall_own_play_product
    (owner : Player)
    (weight : (nativeModel).InfoState owner × (nativeApplication).Action → ℝ≥0∞)
    (past : List (nativeApplication).PlayerEntry) :
    (((nativeApplication).recallOwnPlay past).map weight).prod =
      ((past.zipIdx).map fun indexed =>
        weight (some (past.take indexed.2, indexed.1.beforeView),
          indexed.1.action)).prod := by
  classical
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past record ih =>
    rw [ReactiveApplication.recallOwnPlay_append, List.map_cons, List.prod_cons, ih,
      List.zipIdx_append, List.map_append, List.prod_append]
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, Nat.zero_add, List.take_left, mul_one]
    have retained : ((past.zipIdx).map fun indexed =>
          weight (some ((past ++ [record]).take indexed.2, indexed.1.beforeView),
            indexed.1.action)) =
        (past.zipIdx).map (fun indexed =>
          weight (some (past.take indexed.2, indexed.1.beforeView), indexed.1.action)) := by
      apply List.map_congr_left
      intro indexed member
      have bounded : indexed.2 < past.length := by
        simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx member
      rw [List.take_append_of_le_length (Nat.le_of_lt bounded)]
    rw [retained]
    exact mul_comm _ _

private theorem sourceReplay_registered_draw_product
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player)
    (scale : Set.Icc (0 : ℝ) 1)
    (nativeBad : Set.Icc (0 : ℝ) 1) : ENNReal.ofReal
    (sourceReplayResponseProducts setup values implementation
      ⟨nativeBad, scale, scale, scale⟩ who trace).2.1 =
    sourceReplayRegisteredDrawProduct setup values implementation who
      ⟨some control, trace⟩ := by
  classical
  have ownProductExtend := sourceReplay_foreign_own_play_extend (setup := setup)
    (implementation := implementation) (who := who)
  have recallWord := sourceReplay_recall_own_play_product (setup := setup)
    (implementation := implementation)
  let model := (nativeMenu).information nativeInitial implementation.horizon
    implementation.scheduler
  let drawAt := fun (owner : Player) (record : model.InfoState owner ×
      (nativeApplication).Action) =>
    match record.1 with
    | none => (1 : ℝ≥0∞)
    | some observed => sourceReplayBindingDrawAtom setup values implementation owner
        observed.1 observed.2 record.2
  have drawFinite (owner : Player) (past : List (nativeApplication).PlayerEntry)
      (view : (nativeApplication).PlayerView) (action : (nativeApplication).Action) :
      sourceReplayBindingDrawAtom setup values implementation owner past view action ≠ ⊤ := by
    unfold sourceReplayBindingDrawAtom
    split
    · exact ENNReal.one_ne_top
    · split
      · split
        · exact ENNReal.zero_ne_top
        · split_ifs
          · split
            · exact ENNReal.zero_ne_top
            · exact PMF.apply_ne_top _ _
          · exact ENNReal.zero_ne_top
      · exact ENNReal.one_ne_top
      · exact ENNReal.one_ne_top
  have nativeWord {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
      ENNReal.ofReal
        (sourceReplayResponseProducts setup values implementation
          ⟨nativeBad, scale, scale, scale⟩ who trace).2.1 =
        ∏ owner, if owner = who then 1 else
          ((model.ownPlay owner trace).map (drawAt owner)).prod := by
    induction trace with
    | start => simp only [sourceReplayResponseProducts, InfoSignals.ownPlay,
        List.map_nil, List.prod_nil, ite_self, Finset.prod_const_one, ENNReal.ofReal_one]
    | @extend before after prior joint legal moved ih =>
      have nonnegative := (sourceReplay_response_products_nonnegative setup values
        implementation ⟨nativeBad, scale, scale, scale⟩ who prior).1
      have product := ownProductExtend drawAt prior joint legal moved
      rw [product, ← ih]
      cases before with
      | none =>
        have quiet (owner : Player) : joint owner = none := by
          have offered := legal.2 owner
          cases selected : joint owner with
          | none => rfl
          | some action =>
            have active := (selected ▸ offered).1
            change none = some owner at active
            cases active
        simp only [sourceReplayResponseProducts, quiet, ite_self,
          Finset.prod_const_one, mul_one]
      | some control =>
        cases acting : control.actor with
        | none =>
          have quiet (owner : Player) : joint owner = none := by
            have offered := legal.2 owner
            cases selected : joint owner with
            | none => rfl
            | some action =>
              have active := (selected ▸ offered).1
              change control.actor = some owner at active
              rw [acting] at active
              cases active
          simp only [sourceReplayResponseProducts, acting, quiet, ite_self,
            Finset.prod_const_one, mul_one]
        | some owner =>
          have quiet (other : Player) (different : other ≠ owner) : joint other = none := by
            have offered := legal.2 other
            cases selected : joint other with
            | none => rfl
            | some action =>
              have active := (selected ▸ offered).1
              change control.actor = some other at active
              rw [acting] at active
              exact (different (Option.some.inj active).symm).elim
          by_cases focal : owner = who
          · subst owner
            simp only [sourceReplayResponseProducts, acting, ite_true, mul_one]
            refine (mul_one (ENNReal.ofReal
              (sourceReplayResponseProducts setup values implementation
                ⟨nativeBad, scale, scale, scale⟩ who prior).2.1)).symm.trans ?_
            apply congrArg (fun atom : ℝ≥0∞ => ENNReal.ofReal
              (sourceReplayResponseProducts setup values implementation
                ⟨nativeBad, scale, scale, scale⟩ who prior).2.1 * atom)
            symm
            apply Finset.prod_eq_one
            intro other _member
            by_cases same : other = who
            · exact ite_eq_left same
            · have silent := quiet other same
              cases response : joint other with
              | none => simp only [ite_self]
              | some action =>
                  rw [response] at silent
                  cases silent
          · obtain ⟨action, selected⟩ : ∃ action, joint owner = some action := by
              cases selected : joint owner with
              | none =>
                have inactive := selected ▸ legal.2 owner
                exact (inactive acting).elim
              | some action => exact ⟨action, rfl⟩
            have information : model.infoOf owner prior =
                some (control.execution.recall owner,
                  control.execution.observe nativeApplication owner) := by
              change ((nativeMenu).signals nativeInitial implementation.horizon
                implementation.scheduler).infoOf owner prior = _
              simpa only [ReactiveApplication.observe, acting, ite_true] using
                (nativeMenu).info nativeInitial implementation.horizon
                  implementation.scheduler owner prior
            simp only [sourceReplayResponseProducts, acting, ite_eq_right focal, selected,
              ENNReal.ofReal_mul nonnegative,
              ENNReal.ofReal_toReal (drawFinite owner _ _ action)]
            apply congrArg (fun atom : ℝ≥0∞ => ENNReal.ofReal
              (sourceReplayResponseProducts setup values implementation
                ⟨nativeBad, scale, scale, scale⟩ who prior).2.1 * atom)
            symm
            refine (Finset.prod_eq_single owner ?_ ?_).trans ?_
            · intro other _member different
              have silent := quiet other different
              cases response : joint other with
              | none => simp only [ite_self]
              | some action =>
                  rw [response] at silent
                  cases silent
            · intro impossible
              exact (impossible (Finset.mem_univ owner)).elim
            · cases response : joint owner with
              | none =>
                  have impossible := response.symm.trans selected
                  cases impossible
              | some actualAction =>
                  have same : actualAction = action :=
                    Option.some.inj (response.symm.trans selected)
                  subst actualAction
                  refine (ite_eq_right focal).trans ?_
                  change drawAt owner (model.infoOf owner prior, action) = _
                  simp only [information, drawAt]
  rw [nativeWord]
  unfold sourceReplayRegisteredDrawProduct
  apply Finset.prod_congr rfl
  intro owner _
  by_cases focal : owner = who
  · simp only [focal, ite_true]
  · rw [ite_eq_right focal, ite_eq_right focal,
      HiddenSwap.phase_trace_ownPlay implementation.bounds nativeInitial
        implementation.horizon implementation.scheduler control trace owner,
        recallWord owner (drawAt owner)]
    apply congrArg List.prod
    apply List.map_congr_left
    intro indexed member
    have recorded : indexed.1 ∈ control.execution.recall owner :=
      List.fst_mem_of_mem_zipIdx member
    change sourceReplayBindingDrawAtom setup values implementation owner
        ((control.execution.recall owner).take indexed.2) indexed.1.beforeView
          indexed.1.action = _
    cases sent : indexed.1.action.transmission with
    | none =>
      cases emitted : indexed.1.emitted with
      | none => simp only [sourceReplayBindingDrawAtom, sent]
      | some message =>
        cases call : message.payload.packet.call <;>
          simp only [sourceReplayBindingDrawAtom, sent, call]
    | some material =>
      obtain ⟨message, emitted, _sender, packet⟩ := PhaseCount.recalled_submission_emitted
        implementation.runtime implementation.leaks nativeInitial implementation.horizon
          implementation.scheduler
            ((nativeMenu).toRawTrace nativeInitial implementation.horizon
              implementation.scheduler trace) owner indexed.1 recorded material sent
      rw [emitted]
      dsimp only
      rw [packet]
      cases call : material.call.packet <;>
        simp only [sourceReplayBindingDrawAtom, sent, call]

private theorem sourceReplay_same_handle_messages
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (left right : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (leftInput : left ∈ control.execution.network.inputs)
    (rightInput : right ∈ control.execution.network.inputs)
    (leftEvent rightEvent : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent))
    (leftCall : left.payload.packet.call = .commitment leftEvent handle)
    (rightCall : right.payload.packet.call = .commitment rightEvent handle)
    (sender : left.sender = right.sender) : left = right := by
  classical
  have rawTrace := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have cleanHistory := (PhaseCount.onePacketMenu_countClean implementation.runtime
    implementation.leaks implementation.bounds implementation.scheduler).history nativeInitial
      implementation.horizon (fun state _ => PhaseCount.countClean_initial
        implementation.runtime implementation.leaks state) trace
  have leftCorrect := ((PhaseCount.permits_eq_true_iff _ _).mp
    (cleanHistory.2 left leftInput)).2.1
  have rightCorrect := ((PhaseCount.permits_eq_true_iff _ _).mp
    (cleanHistory.2 right rightInput)).2.1
  change CountCallCorrect _ (PhaseCount.nativeMessage left) at leftCorrect
  change CountCallCorrect _ (PhaseCount.nativeMessage right) at rightCorrect
  simp only [CountCallCorrect, PhaseCount.nativeMessage, leftCall] at leftCorrect
  simp only [CountCallCorrect, PhaseCount.nativeMessage, rightCall] at rightCorrect
  rcases lt_trichotomy left.id.2 right.id.2 with earlier | equal | later
  · exact (rightCorrect.2.2.2.2 (PhaseCount.nativeMessage left)
      ⟨List.mem_map.mpr ⟨left, leftInput, rfl⟩, sender, earlier⟩ leftEvent leftCall).elim
  · exact (nativeApplication).input_identifier_injective_history nativeInitial
      implementation.horizon implementation.scheduler control rawTrace left right
        leftInput rightInput (Prod.ext sender equal)
  · exact (leftCorrect.2.2.2.2 (PhaseCount.nativeMessage right)
      ⟨List.mem_map.mpr ⟨right, rightInput, rfl⟩, sender.symm, later⟩ rightEvent
        rightCall).elim

open scoped Classical in
private theorem sourceReplay_tagged_registration
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (who : Player)
    (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (acting : reference.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who
          (reference.execution.recall who)
          (reference.execution.observe nativeApplication who) event payload)
    (g : setup.proposalRecoveryProtocol.History)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (scale : Set.Icc (0 : ℝ) 1)
    (sourceBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val)
    (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val)
    (sourceBadBelow : sourceBad.val < 1)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
          ¬ setup.proposalRecoveryProtocol.terminal history.state →
          sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
            setup.proposalRecoveryNormalizedTrembledProfile
              scale.val scale.property.1 scale.property.2
              sourceBad.val sourceBad.property.1 sourceBad.property.2
              scale.val scale.property.1 scale.property.2 values owner
                (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (value : L.Val payload)
    (script : List (RawReplayChoice setup implementation))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (q : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (annotation : annotatedPrefixWeight setup values implementation operational sourceProfile
          nativeProfile who ⟨some control, trace⟩ tape q word *
            (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
              then 1 else 0) *
            sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
              event payload q word value (g, ⟨some targetCurrent, targetTrace⟩) ≠ 0)
    (related : RawReplayState setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
          (rawReplayLost setup implementation script) ⟨some reference, referenceTrace⟩
            ⟨some control, trace⟩)
    (owner : Player) (_different : owner ≠ who)
    (record : (nativeApplication).PlayerEntry)
    (recorded : record ∈ control.execution.recall owner)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (sent : record.action.transmission = some material)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (emitted : record.emitted = some message)
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (handle : Handle (serviceGraph setup .concurrent))
    (call : message.payload.packet.call = .commitment named handle)
    (materialCall : material.call.packet = .commitment named handle)
    (actualBefore : (nativeApplication).Control)
    (originalAction : (nativeApplication).Action)
    (kernel : PMF (RawReplayChoice setup implementation))
    (atoms : SourceReplayCallbackAtoms (setup := setup) (values := values)
      (implementation := implementation) scale owner actualBefore.execution
        ⟨some targetCurrent, targetTrace⟩ reference originalAction kernel)
    (choice : RawReplayChoice setup implementation) (chosen : choice ∈ kernel.support)
    (sameCall : originalAction.transmission.map (fun material => material.call.packet) =
      record.action.transmission.map (fun material => material.call.packet))
    (earlier : List (RawReplayChoice setup implementation))
    (restricted : SourceReplayLostRestricted setup implementation
      ⟨some targetCurrent, targetTrace⟩ reference who
        (rawReplayLost setup implementation (choice :: earlier))) :
    choice.1.isSome = decide
      (message.payload.attempt ≠ control.execution.application.attempt ∧
        ¬ PhaseService.BindingAccepted implementation.runtime implementation.leaks
          ⟨message.payload.attempt, named⟩ owner control.execution) := by
  classical
  have actualActing : control.actor = some who := related.2.1.trans acting
  have actualClean : CleanUnsentBinding setup implementation who
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        event payload := by
    rw [related.2.2.2.1, related.2.2.2.2]
    exact clean
  have canonicalPositive : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0 :=
    (prescribed_source_history_positive setup values scale sourceBad scalePositive scaleBelow
      sourceBadPositive sourceBadBelow fullValues sourceProfile sourcePrescribed _).ne'
  have finalProjection := RawReplayState.mechanicalProjection setup implementation who
    ⟨some targetCurrent, targetTrace⟩ reference (rawReplayLost setup implementation script)
      ⟨some reference, referenceTrace⟩ ⟨some control, trace⟩ related
  have finalOutputs (owner : Player) :=
    (mechanicalProjection_foreign_input setup implementation who owner control reference trace
      referenceTrace finalProjection).2.1
  have finalAttempt : control.execution.application.attempt =
      reference.execution.application.attempt := by
    exact congrArg (fun view => view.attempt)
      (mechanicalProjection_foreign_input setup implementation who who control reference trace
        referenceTrace finalProjection).1
  have rawTrace := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have finalInputs := (nativeApplication).history_inputRecall nativeInitial
    implementation.horizon implementation.scheduler rawTrace
  have sameHandleMessages := sourceReplay_same_handle_messages (setup := setup)
    (implementation := implementation) (control := control) (trace := trace)
  have output : message ∈ (nativeApplication).outputs (control.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
  have input : message ∈ control.execution.network.inputs := by
    rw [← finalInputs owner] at output
    exact (List.mem_filter.mp output).1
  have sender : message.sender = owner := by
    rw [← finalInputs owner] at output
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp output).2
  obtain ⟨serial, opening, evidence, handleEq, _sender, _declared, _fresh,
    _signed, _meaning⟩ := sourceReplay_recorded_binding_registration setup implementation
      control trace owner record recorded message emitted named ty shape handle call
  have handleOwner : handle.1 = owner := congrArg Prod.fst handleEq
  have packetEq := sourceReplayLostSlot_eq_of_signed_call setup implementation who
    ⟨some targetCurrent, targetTrace⟩ reference control referenceTrace trace
      finalProjection.symm originalAction record.action sameCall
  have tag := (atoms choice chosen).1
  rw [packetEq] at tag
  simp only [sourceReplayLostSlot, sent, Option.bind_some, materialCall] at tag
  cases selected : choice.1 with
  | none =>
    simp only [Option.isSome_none]
    symm
    apply decide_eq_false
    rintro ⟨historical, unaccepted⟩
    have noMeaning := positive_original_annotated_unaccepted_meaning setup values
      implementation operational fullValues sourceProfile nativeProfile who control trace
        actualActing tape q g ⟨some targetCurrent, targetTrace⟩ word canonicalPositive event
          payload actualClean value annotation owner record recorded material sent message
            emitted named ty shape handle call historical handleOwner unaccepted
    simp only [selected, Option.map_none, noMeaning, ite_true] at tag
    cases tag
  | some drawn =>
    have slot : drawn.1 = handle := by
      simp only [selected, Option.map_some] at tag
      split at tag
      · exact Option.some.inj tag
      · cases tag
    obtain ⟨foreignHandle, prepared, noMeaning, originalRecord, originalMessage,
      originalEvent, originalTy, old, originalMember, originalEmitted, originalSender,
      originalCall, historical, originalShape, _rawShape, _prepared,
      unaccepted⟩ := restricted drawn.1 drawn.2 (by
        simp only [rawReplayLost, List.findSome?_cons, selected, Option.bind_some,
          ite_true])
    rw [slot] at foreignHandle prepared noMeaning
    rw [slot] at originalMember originalSender originalCall originalShape unaccepted
    have originalOutput : originalMessage ∈
        (nativeApplication).outputs (control.execution.recall owner) := by
      rw [finalOutputs owner]
      rw [handleOwner] at originalMember
      exact List.mem_filterMap.mpr ⟨originalRecord, originalMember, originalEmitted⟩
    have originalInput : originalMessage ∈ control.execution.network.inputs := by
      rw [← finalInputs owner] at originalOutput
      exact (List.mem_filter.mp originalOutput).1
    have identical : message = originalMessage := sameHandleMessages message originalMessage
      input originalInput named originalEvent handle call originalCall
        (sender.trans (originalSender.trans handleOwner).symm)
    have sameEvent : named = originalEvent := by
      have namedEq := congrArg (fun signed => signed.payload.packet.call) identical
      rw [call, originalCall] at namedEq
      exact (Payload.commitment.inj namedEq).1
    subst originalEvent
    have actualUnaccepted : ¬ PhaseService.BindingAccepted implementation.runtime
        implementation.leaks ⟨message.payload.attempt, named⟩ owner control.execution := by
      rw [identical]
      rw [← handleOwner] at ⊢
      exact fun accepted => unaccepted
        ((bindingAccepted_iff_of_mechanicalProjection setup implementation who control
          reference finalProjection ⟨originalMessage.payload.attempt, named⟩
            handle.1).mp accepted)
    simp only [Option.isSome_some]
    symm
    apply decide_eq_true
    exact ⟨by rw [identical, finalAttempt]; exact historical, actualUnaccepted⟩

private theorem sourceReplay_canonical_registration
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (operational : implementation.Operational)
    (current next : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (moved : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (kept : TracePrefix (prior.extend joint legal moved)
      (canonicalSource setup implementation operational ⟨some control, trace⟩).trace)
    (owner : Player) (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (rank : named.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point)
    (active : owner ∉ current.excluded) (raw : L.Val ty)
    (data : phaseRecoveryBindingData setup .concurrent named owner ty shape
      ((joint owner).map (·.semantic)) = (.success raw, false)) :
    ∃ (handle : Handle (serviceGraph setup .concurrent))
      (record : (nativeApplication).PlayerEntry)
      (material : WitnessedSubmission (serviceGraph setup .concurrent))
      (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
      record ∈ control.execution.recall owner ∧
      record.action.transmission = some material ∧ record.emitted = some message ∧
      message.sender = owner ∧ message.payload.packet.call = .commitment named handle ∧
      current.generation = message.payload.attempt.generation ∧
      instructionCount setup.program - ProtocolState.remaining setup.program current.saved =
        message.payload.attempt.phase ∧
      message.payload.attempt ≠ control.execution.application.attempt ∧
      PhaseService.BindingAccepted implementation.runtime implementation.leaks
        ⟨message.payload.attempt, named⟩ owner control.execution ∧
      control.execution.application.current.native.bindingResult handle ty =
        .success raw := by
  classical
  have rawTrace := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have finalInputs := (nativeApplication).history_inputRecall nativeInitial
    implementation.horizon implementation.scheduler rawTrace
  let canonical := canonicalSource setup implementation operational ⟨some control, trace⟩
  obtain ⟨committing, acting, _decode⟩ := source_binding_at_rank setup.program current.point
    named owner ty shape rank
  obtain ⟨before, after, nativePrior, nativeJoint, nativeLegal, nativeMoved, phase, rest,
    physical, retained, installed, commitment, normalized, finished, effect, changed,
    binding, stamp, receipts, last, closed, _fuel, path, instructions, closedKept,
    lower, upper⟩ := source_commit_row_closing_origin setup implementation operational
      control trace current next prior joint legal moved kept committing owner acting active
  let first :=
    (checkpointSelection setup implementation operational nativePrior).val.checkpoint
  obtain ⟨saved, generation, decoded⟩ := source_decoded_binding_row setup first
    (phase.drain physical).native ⟨some last, closed⟩ path instructions canonical closedKept
      current next prior joint legal moved kept lower upper
  have blockGeometry := first.commit_phase_geometry phase rest installed commitment
    (checkpointSelection setup implementation operational nativePrior).val.order.frontier
      (operational.maximalPhases.suffix
        (checkpointSelection setup implementation operational nativePrior).val.suffix)
  generalize decomposition : commitPhase first.residual.tail = segment
    at decoded blockGeometry
  rcases segment with ⟨Ξ, Q, suffix, block, reconstruct, boundary⟩
  dsimp only at decoded blockGeometry
  obtain ⟨decodedEvent, decodedOwner, decodedType, decodedShape, decodedRank,
    _receiptActive, decoded⟩ := decoded
  have sameEvent : decodedEvent = named := Fin.ext (decodedRank.trans rank.symm)
  subst decodedEvent
  have sameShape := EventField.binding.inj (decodedShape.symm.trans shape)
  obtain ⟨sameOwner, sameType⟩ := sameShape
  subst decodedOwner
  subst decodedType
  obtain ⟨Δ, P, name, fresh, guard, earlier, remaining, earlierSize, splitBlock,
    selected, _terminal, decodedData, _cell⟩ := decoded active
  have actualData := data.symm.trans decodedData
  obtain ⟨candidate, accepted⟩ : ∃ candidate,
      (phase.drain physical).native.accepted (.inr named) = some candidate := by
    cases found : (phase.drain physical).native.accepted (.inr named) with
    | none =>
      have impossible := congrArg Prod.snd actualData
      simp only [found, Option.isNone_none] at impossible
      cases impossible
    | some candidate => exact ⟨candidate, rfl⟩
  have proper : (phase.drain physical).native.bindingResult candidate ty = .success raw := by
    have read := congrArg Prod.fst actualData
    simpa only [accepted, Option.elim_some] using read.symm
  have candidateOwner : candidate.1 = owner := by
    obtain ⟨_domain, typed⟩ := binding.accepted_typed (.inr named) candidate accepted
    exact (EventField.binding.inj (typed.symm.trans shape)).1
  obtain ⟨selected, selectedSize, selectedEvent⟩ := selected
  have eventRank : named.val = before.execution.application.attempt.phase +
      earlier.length := by
    have castRank {Γ : SourceCtx Player L} {O : Finset VarId}
        {left right : SourceProgram Player L Γ O} (equal : left = right)
        (embedding : OutputEmbedding (inputLayout setup.context)
          (outputLayout setup.program) right)
        (low : Nat) (rank : ∀ index, (embedding.event index).val = low + index.val) :
        ∀ index, ((cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) equal.symm)
            embedding).event index).val = low + index.val := by
      cases equal
      exact rank
    have actualRank := castRank reconstruct first.embedding _ first.compiled.rankEq selected
    rw [selectedEvent, selectedSize] at actualRank
    exact actualRank
  have inside : named ∈ phase.events := by
    apply (phase.mem_events named).mpr
    have low : before.execution.application.attempt.phase = phase.low := by
      simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
        Option.getD_some]
    have length := congrArg SourceProgram.CommitPrefix.length splitBlock
    simp only [SourceProgram.CommitPrefix.length_append,
      SourceProgram.CommitPrefix.length] at length
    rw [low] at eventRank
    exact ⟨by omega, by omega⟩
  have lowerRank : before.execution.application.attempt.phase ≤ named.val := by
    rw [eventRank]
    exact Nat.le_add_right _ _
  obtain ⟨message, authored, sender, call, signedNamespace⟩ :=
    (stamp named candidate accepted).resolve_left (Nat.not_lt.mpr lowerRank)
  rw [candidateOwner] at authored sender
  obtain ⟨record, recordBefore, emitted⟩ := List.mem_filterMap.mp authored
  have beforeKept : TracePrefix nativePrior trace :=
    (TracePrefix.extend .refl nativeJoint nativeLegal nativeMoved).trans retained
  have rawBeforeKept := (nativeMenu).reaches_raw nativeInitial implementation.horizon
    implementation.scheduler beforeKept.reachesWithin
  have recalled := (nativeApplication).reaches_recall_prefix nativeInitial
    implementation.horizon implementation.scheduler rawBeforeKept before control rfl rfl owner
  have recorded := recalled.subset recordBefore
  obtain ⟨serial, opening, evidence, handleEq, _sender, recordAction, _fresh,
    _namespace, _meaning⟩ := sourceReplay_recorded_binding_registration setup implementation
      control trace owner record recorded message emitted named ty shape candidate call
  let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.commitment named (owner, .prepared serial), opening⟩, evidence⟩
  have transmitted : record.action.transmission = some material :=
    congrArg ReactiveApplication.Action.transmission recordAction
  let afterTrace := nativePrior.extend nativeJoint nativeLegal nativeMoved
  have acceptedAfter := receipts named candidate lowerRank accepted
  rw [candidateOwner] at acceptedAfter
  have acceptedFinal : PhaseService.BindingAccepted implementation.runtime
    implementation.leaks
      ⟨message.payload.attempt, named⟩ owner control.execution := by
    obtain ⟨acceptedMessage, acceptedInput, acceptedSender, acceptedAttempt, acceptedEvent,
      received⟩ := acceptedAfter
    have afterRecall := (nativeApplication).history_inputRecall nativeInitial
      implementation.horizon implementation.scheduler
        ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler afterTrace) owner
    have output : acceptedMessage ∈
        (nativeApplication).outputs (after.execution.recall owner) :=
      by rw [← afterRecall]
         exact List.mem_filter.mpr ⟨acceptedInput,
           by simpa only [decide_eq_true_eq] using acceptedSender⟩
    have path := (nativeMenu).reaches_raw nativeInitial implementation.horizon
      implementation.scheduler retained.reachesWithin
    have laterRecall := (nativeApplication).reaches_recall_prefix nativeInitial
      implementation.horizon implementation.scheduler path after control rfl rfl owner
    obtain ⟨entry, entered, emitted⟩ := List.mem_filterMap.mp output
    have finalOutput : acceptedMessage ∈ (nativeApplication).outputs
        (control.execution.recall owner) :=
      List.mem_filterMap.mpr ⟨entry, laterRecall.subset entered, emitted⟩
    rw [← finalInputs owner] at finalOutput
    have keptReceipts := (nativeApplication).reaches_receipts_prefix nativeInitial
      implementation.horizon implementation.scheduler path after control rfl rfl
    exact ⟨acceptedMessage, (List.mem_filter.mp finalOutput).1, acceptedSender,
      acceptedAttempt.trans signedNamespace.symm, acceptedEvent, keptReceipts.subset received⟩
  have typedRead := binding.binding_read
    (⟨.inr named, shape⟩ : FieldRef (graphLayout setup.program) (.binding owner ty))
      named rfl (finished inside)
  simp only [accepted, Option.elim_some, proper] at typedRead
  have castSome {α β : Type} (same : α = β) (item : α) :
      cast (congrArg Option same) (some item) = some (cast same item) := by
    cases same
    rfl
  have stored : (phase.drain physical).native.config.store (.inr named) =
      some (cast (congrArg EventField.Value shape.symm) (.success raw)) := by
    have pushed := congrArg
      (cast (congrArg (fun kind : EventField Player L => Option kind.Value) shape.symm))
        typedRead
    have rawEq : (phase.drain physical).native.config.store (.inr named) =
        cast (congrArg Option (congrArg EventField.Value shape.symm))
          (some (.success raw)) := by
      simpa only [FieldRef.get?, cast_cast, cast_eq] using pushed
    exact rawEq.trans (castSome (congrArg EventField.Value shape.symm) (.success raw))
  have settled : after.execution.application = PhaseRuntimeState.settle (phase :: rest)
      before.execution.application.generation before.execution.application.entry physical
        before.execution.application.retired := by
    simpa only [PhaseRuntimeState.normalize, installed] using normalized
  have retainedValue := completed_binding_retained setup phase rest
    before.execution.application.generation before.execution.application.entry physical
      before.execution.application.retired finished (.inr named) candidate _ accepted stored
  have retain (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
      (selected : snapshot = after.execution.application.current.native ∨
        snapshot = after.execution.application.entry.native ∨
        ∃ retired ∈ after.execution.application.retired, snapshot = retired.state)
      (accepted : snapshot.accepted (.inr named) = some candidate)
      (read : (⟨.inr named, shape⟩ : FieldRef (graphLayout setup.program)
        (.binding owner ty)).get? snapshot.config.store = some (.success raw)) :
      control.execution.application.current.native.bindingResult candidate ty =
        .success raw := by
    obtain ⟨valid, catalogue⟩ := accepted_snapshot_catalogue setup implementation control
      trace after afterTrace retained snapshot selected owner ty ⟨.inr named, shape⟩
        candidate accepted
    obtain ⟨other, associated, _owned, opened⟩ := valid.success_provenance
      ⟨.inr named, shape⟩ raw read
    have same : other = candidate := Option.some.inj (associated.symm.trans accepted)
    subst other
    have result := catalogue.trans opened
    simp only [State.bindingResult, result, Raw.as?_mk, Option.elim_some]
  have finalValue : control.execution.application.current.native.bindingResult candidate ty =
      .success raw := by
    rcases retainedValue with ⟨retired, member, image⟩ | ⟨acceptedSaved, storedSaved⟩
    · exact retain (phase.drain physical).native
        (Or.inr (Or.inr ⟨retired, by rw [settled]; exact member, image.symm⟩))
          accepted typedRead
    · apply retain after.execution.application.entry.native (Or.inr (Or.inl rfl))
      · simpa only [settled] using acceptedSaved
      · have savedStore : after.execution.application.entry.native.config.store (.inr named) =
            some (cast (congrArg EventField.Value shape.symm) (.success raw)) := by
          simpa only [settled] using storedSaved
        change cast (congrArg (fun kind : EventField Player L => Option kind.Value) shape)
          (after.execution.application.entry.native.config.store (.inr named)) = _
        rw [savedStore]
        rw [castSome (congrArg EventField.Value shape), cast_cast]
        simp only [cast_eq]
  have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
    exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
  have ordered := (phaseApplication_seedOrder implementation.runtime
    implementation.leaks).history
    nativeInitial implementation.horizon implementation.scheduler initialized
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler nativePrior)
  have afterOrdered := (phaseApplication_seedOrder implementation.runtime
    implementation.leaks).history
    nativeInitial implementation.horizon implementation.scheduler initialized
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler afterTrace)
  have firstProgress := (phaseApplication_namespace_progress implementation.runtime
    implementation.leaks).transition nativeInitial implementation.horizon
      implementation.scheduler before after nativeJoint nativeMoved ordered
  have laterProgress := phase_attempt_progress_of_prefix implementation.runtime
    implementation.leaks nativeMenu nativeInitial initialized implementation.horizon
      implementation.scheduler after control afterTrace trace retained afterOrdered
  have historical : message.payload.attempt ≠ control.execution.application.attempt := by
    intro same
    have lastSame := signedNamespace.symm.trans same
    have generation := congrArg CommitAttemptId.generation lastSame
    have phase := congrArg CommitAttemptId.phase lastSame
    have firstGeneration : before.execution.application.attempt.generation ≤
        after.execution.application.attempt.generation := firstProgress.1
    have firstPhase : before.execution.application.attempt.phase ≤
        after.execution.application.attempt.phase := firstProgress.2
    have lastGeneration : after.execution.application.attempt.generation ≤
        control.execution.application.attempt.generation := laterProgress.1
    have lastPhase : after.execution.application.attempt.phase ≤
        control.execution.application.attempt.phase := laterProgress.2.1
    apply changed
    exact congrArg₂ CommitAttemptId.mk
      (Nat.le_antisymm (lastPhase.trans phase.symm.le) firstPhase)
      (Nat.le_antisymm (lastGeneration.trans generation.symm.le) firstGeneration)
  refine ⟨candidate, record, material, message, recorded, transmitted, emitted, sender,
    call, ?_, ?_, historical, acceptedFinal, finalValue⟩
  · exact generation.trans (congrArg CommitAttemptId.generation signedNamespace.symm)
  · rw [saved, first.saved_position]
    exact congrArg CommitAttemptId.phase signedNamespace.symm

private theorem sourceReplay_registration_source_row
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (who : Player)
    (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (acting : reference.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who
          (reference.execution.recall who)
          (reference.execution.observe nativeApplication who) event payload)
    (g : setup.proposalRecoveryProtocol.History)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (scale : Set.Icc (0 : ℝ) 1)
    (sourceBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val)
    (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val)
    (sourceBadBelow : sourceBad.val < 1)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
          ¬ setup.proposalRecoveryProtocol.terminal history.state →
          sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
            setup.proposalRecoveryNormalizedTrembledProfile
              scale.val scale.property.1 scale.property.2
              sourceBad.val sourceBad.property.1 sourceBad.property.2
              scale.val scale.property.1 scale.property.2 values owner
                (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (value : L.Val payload)
    (law : SourceRawReplayLaw (setup := setup) (values := values)
          (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩ reference
            ⟨some reference, referenceTrace⟩)
    (script : List (RawReplayChoice setup implementation))
    (member : script ∈ law.choices.support)
    (replayed : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
          reference ⟨some reference, referenceTrace⟩ script =
            some (⟨some control, trace⟩ : (nativeProtocol).History))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (q : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (annotation : annotatedPrefixWeight setup values implementation operational sourceProfile
          nativeProfile who ⟨some control, trace⟩ tape q word *
            (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
              then 1 else 0) *
            sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
              event payload q word value (g, ⟨some targetCurrent, targetTrace⟩) ≠ 0)
    (related : RawReplayState setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
          (rawReplayLost setup implementation script) ⟨some reference, referenceTrace⟩
            ⟨some control, trace⟩)
    (owner : Player) (different : owner ≠ who)
    (index : Fin (control.execution.recall owner).length)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (sent : (control.execution.recall owner)[index].action.transmission = some material)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (emitted : (control.execution.recall owner)[index].emitted = some message)
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (handle : Handle (serviceGraph setup .concurrent))
    (call : message.payload.packet.call = .commitment named handle)
    (historical : message.payload.attempt ≠ control.execution.application.attempt)
    (accepted : PhaseService.BindingAccepted implementation.runtime implementation.leaks
      ⟨message.payload.attempt, named⟩ owner control.execution) :
    ∃ (actualBefore : (nativeApplication).Control)
      (actualPrior : (nativeProtocol).Trace (some actualBefore))
      (current next : CommitRecoveryState setup.program)
      (sourcePrior : setup.proposalRecoveryProtocol.Trace (some current))
      (sourceJoint : Player → Option (ProposalRecoveryMove Player L))
      (sourceLegal : setup.proposalRecoveryProtocol.Legal (some current) sourceJoint)
      (sourceMoved : some next ∈ (setup.proposalRecoveryProtocol.step (some current)
        ⟨sourceJoint, sourceLegal⟩).support)
      (serial : Nat) (opening : Option (Raw L))
      (evidence : EvidenceRequest (serviceGraph setup .concurrent)) (drawn : L.Val ty),
      TracePrefix actualPrior trace ∧
      actualBefore.actor = some owner ∧
      actualBefore.execution.recall owner = (control.execution.recall owner).take index.val ∧
      (control.execution.recall owner)[index].beforeView =
        actualBefore.execution.observe nativeApplication owner ∧
      actualBefore.execution.application.attempt = message.payload.attempt ∧
      actualBefore.execution.application.SeedRequest owner
        ⟨actualBefore.execution.application.attempt, named⟩ ∧
      TracePrefix (sourcePrior.extend sourceJoint sourceLegal sourceMoved)
        (canonicalSource setup implementation operational ⟨some control, trace⟩).trace ∧
      current.generation = message.payload.attempt.generation ∧
      instructionCount setup.program - ProtocolState.remaining setup.program current.saved =
        message.payload.attempt.phase ∧
      instructionCount setup.program - ProtocolState.remaining setup.program current.point =
        named.val ∧ owner ∉ current.excluded ∧
      phaseRecoveryBindingData setup .concurrent named owner ty shape
        ((sourceJoint owner).map (·.semantic)) = (.success drawn, false) ∧
      (control.execution.recall owner)[index].action =
        ⟨some ⟨⟨.commitment named (owner, .prepared serial), opening⟩, evidence⟩⟩ ∧
      opening.bind (fun raw => raw.as? ty) = some drawn := by
  classical
  have actualActing : control.actor = some who := related.2.1.trans acting
  have actualClean : CleanUnsentBinding setup implementation who
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        event payload := by
    rw [related.2.2.2.1, related.2.2.2.2]
    exact clean
  have canonicalPositive : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0 :=
    (prescribed_source_history_positive setup values scale sourceBad scalePositive scaleBelow
      sourceBadPositive sourceBadBelow fullValues sourceProfile sourcePrescribed _).ne'
  have finalProjection := RawReplayState.mechanicalProjection setup implementation who
    ⟨some targetCurrent, targetTrace⟩ reference (rawReplayLost setup implementation script)
      ⟨some reference, referenceTrace⟩ ⟨some control, trace⟩ related
  have rawTrace := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  let canonical := canonicalSource setup implementation operational ⟨some control, trace⟩
  have taggedRegistration := sourceReplay_tagged_registration (setup := setup) (values := values)
    (implementation := implementation) (control := control) (trace := trace)
    (operational := operational) (fullValues := fullValues) (who := who) (reference := reference)
    (referenceTrace := referenceTrace) (acting := acting) (event := event) (payload := payload)
    (clean := clean) (g := g) (targetCurrent := targetCurrent) (targetTrace := targetTrace)
    (scale := scale) (sourceBad := sourceBad) (scalePositive := scalePositive)
    (scaleBelow := scaleBelow) (sourceBadPositive := sourceBadPositive)
    (sourceBadBelow := sourceBadBelow) (sourceProfile := sourceProfile)
    (sourcePrescribed := sourcePrescribed) (nativeProfile := nativeProfile) (value := value)
    (script := script) (tape := tape) (q := q) (word := word) (annotation := annotation)
    (related := related)
  have recorded : (control.execution.recall owner)[index] ∈ control.execution.recall owner :=
    List.getElem_mem _
  obtain ⟨serial, opening, evidence, handleEq, _sender, action, _fresh,
    signedNamespace, meaning⟩ := sourceReplay_recorded_binding_registration setup
      implementation
      control trace owner _ recorded message emitted named ty shape handle call
  obtain ⟨before, after, prior, joint, legal, moved, earlier, earlierMass, actualBefore,
    actualPrior, actualAfter, kernel, choice, _originalKept, actualKept, beforeActing,
    _earlierSupported, earlierReplay, prefixRelated, _prefixRestricted, afterReplay,
    _afterKept, afterRelated, afterRestricted, atoms, _description, chosen,
    choiceAction, past, viewed⟩ := sourceReplay_recorded_foreign_callback setup values
      implementation scale who ⟨some targetCurrent, targetTrace⟩ reference
        ⟨some reference, referenceTrace⟩ ⟨some control, trace⟩
          ⟨some reference, referenceTrace⟩ script (law.choices script) (law.atoms
            script member)
            .refl control trace replayed .refl owner different index.val index.isLt related
              (law.restricted script member)
  obtain ⟨_tag, response, responseEq, _proper, _form⟩ := atoms choice chosen
  have responseAction : response.val = (control.execution.recall owner)[index].action :=
    Option.some.inj (responseEq.symm.trans choiceAction)
  have callbackActing : actualBefore.actor = some owner := prefixRelated.2.1.trans
    beforeActing
  obtain ⟨originalAction, selected⟩ : ∃ action, joint owner = some action := by
    cases selected : joint owner with
    | none => exact ((selected ▸ legal.2 owner) beforeActing).elim
    | some action => exact ⟨action, rfl⟩
  have originalState : after = ⟨before.remaining, none,
      before.execution.respond nativeApplication owner originalAction⟩ := by
    have reached := moved
    change some after ∈ ((nativeApplication).transition nativeInitial
      implementation.horizon implementation.scheduler (some before) joint).support at reached
    simpa only [ReactiveApplication.transition, beforeActing, selected, Option.getD_some,
      PMF.mem_support_pure_iff, Option.some.injEq] using reached
  have appended := afterReplay
  rw [sourceRawReplay, earlierReplay, Option.bind_some] at appended
  dsimp only at appended
  rw [beforeActing] at appended
  dsimp only at appended
  rw [ite_eq_right different, responseEq, Option.bind_some] at appended
  have actualState := (sourceReplayAppend_prior_state setup implementation
    ⟨some actualBefore, actualPrior⟩ actualAfter _ _ appended).2
  have firstMechanical := (RawReplayState.mechanicalProjection setup implementation who
    ⟨some targetCurrent, targetTrace⟩ reference (rawReplayLost setup implementation earlier)
      ⟨some before, prior⟩ ⟨some actualBefore, actualPrior⟩ prefixRelated).symm
  have lastMechanical := (RawReplayState.mechanicalProjection setup implementation who
    ⟨some targetCurrent, targetTrace⟩ reference
      (rawReplayLost setup implementation (choice :: earlier))
        ⟨some after, prior.extend joint legal moved⟩ actualAfter afterRelated).symm
  change mechanicalProjection setup implementation who (some after) = _ at lastMechanical
  rw [actualState, originalState] at lastMechanical
  have packets := mechanicalProjection_response_packet setup implementation who owner
    before actualBefore prior actualPrior originalAction response.val firstMechanical
      lastMechanical
  have sameCall : originalAction.transmission.map (fun material => material.call.packet) =
      (control.execution.recall owner)[index].action.transmission.map
        (fun material => material.call.packet) := by
    have calls := congrArg (Option.map (fun signed :
        CommitAttemptPacket (serviceGraph setup .concurrent) => signed.packet.call)) packets
    simpa only [responseAction, Option.map_map, Function.comp_def,
      PhaseCount.localEnvelope, PhaseCount.maskPacket_call] using calls
  have materialCall : material.call.packet = .commitment named handle := by
    obtain ⟨other, otherEmitted, _sender, packet⟩ := PhaseCount.recalled_submission_emitted
      implementation.runtime implementation.leaks nativeInitial implementation.horizon
        implementation.scheduler rawTrace owner _ recorded material sent
    have same : other = message := Option.some.inj (otherEmitted.symm.trans emitted)
    subst other
    exact packet.symm.trans call
  have tagged := taggedRegistration owner different _ recorded material sent message emitted
    named ty shape handle call materialCall actualBefore originalAction kernel
      (by simpa only [selected, Option.getD_some] using atoms) choice chosen sameCall earlier
        afterRestricted
  have noTag : choice.1 = none := by
    simp only [accepted, not_true_eq_false, and_false, decide_false] at tagged
    cases tag : choice.1 with
    | none => rfl
    | some drawn =>
        simp only [tag, Option.isSome_some] at tagged
        cases tagged
  have packetSlot := sourceReplayLostSlot_eq_of_signed_call setup implementation who
    ⟨some targetCurrent, targetTrace⟩ reference control referenceTrace trace
      finalProjection.symm originalAction (control.execution.recall owner)[index].action
        sameCall
  have tag := (atoms choice chosen).1
  simp only [selected, Option.getD_some] at tag
  rw [packetSlot] at tag
  have meaningful : sourceHandleMeaning setup implementation
      ⟨some targetCurrent, targetTrace⟩ control handle ≠ none := by
    intro missing
    simp only [noTag, Option.map_none, sourceReplayLostSlot, sent, Option.bind_some,
      materialCall, missing, ite_true] at tag
    cases tag
  have handleOwner : handle.1 = owner := congrArg Prod.fst handleEq
  have meaningRead := sourceHandleMeaning_of_emission setup implementation
    ⟨some targetCurrent, targetTrace⟩ control trace handle _
      (by simpa only [handleOwner] using recorded) message emitted named call owner ty shape
        (sourceBindingAt setup message.payload.attempt named owner ty shape targetTrace) rfl
  obtain ⟨drawn, targetRead⟩ : ∃ drawn, sourceBindingAt setup message.payload.attempt
      named owner ty shape targetTrace = some drawn := by
    cases read : sourceBindingAt setup message.payload.attempt named owner ty shape
      targetTrace with
    | none =>
      rw [read, Option.map_none] at meaningRead
      exact (meaningful meaningRead).elim
    | some drawn => exact ⟨drawn, rfl⟩
  have canonicalRead := positive_original_annotated_historical_readback setup values
    implementation operational fullValues sourceProfile nativeProfile who control trace
      actualActing tape q g ⟨some targetCurrent, targetTrace⟩ word canonicalPositive event
        payload actualClean value annotation message.payload.attempt historical owner named
          ty shape drawn targetRead
  obtain ⟨current, sourcePrior, sourceJoint, sourceLegal, sourceNext, sourceMoved, sourceKept,
    generation, saved, rank, data⟩ := sourceBindingAt_origin setup message.payload.attempt
      named owner ty shape canonical.trace drawn canonicalRead
  obtain ⟨next, _rawMoved, rfl⟩ := (PMF.mem_support_map_iff ..).mp sourceMoved
  have active : owner ∉ current.excluded := by
    cases selected : sourceJoint owner with
    | none => simp [selected, phaseRecoveryBindingData] at data
    | some move => exact ((selected ▸ sourceLegal.2 owner).1).2
  have finalValue := (positive_original_annotated_historical_result setup values
    implementation operational fullValues sourceProfile nativeProfile who control trace
      actualActing tape q g ⟨some targetCurrent, targetTrace⟩ word canonicalPositive event
        payload actualClean value annotation owner _ recorded material sent message emitted
          named ty shape handle call historical drawn targetRead).1
  have decoded : opening.bind (fun raw => raw.as? ty) = some drawn := by
    rw [finalValue] at meaning
    cases read : opening.bind (fun raw => raw.as? ty) with
    | none => simp only [read, Option.elim_none] at meaning; cases meaning
    | some old =>
      have same : old = drawn := PublicationResult.success.inj
        (by simpa only [read, Option.elim_some] using meaning.symm)
      exact congrArg some same
  have signedNamespace : actualBefore.execution.application.attempt =
    message.payload.attempt := by
    simp only [Fin.getElem_fin] at signedNamespace
    rw [viewed] at signedNamespace
    exact signedNamespace
  let material' : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.commitment named (owner, .prepared serial), opening⟩, evidence⟩
  have offered : (⟨some material'⟩ : (nativeApplication).Action) ∈
      PhaseCount.onePacketActions implementation.runtime implementation.leaks
        implementation.bounds owner (actualBefore.execution.recall owner)
          (actualBefore.execution.observe nativeApplication owner) := by
    rw [← action, ← responseAction]
    exact response.property
  have activeTrace : (nativeProtocol).Trace
      (some ⟨actualBefore.remaining, some owner, actualBefore.execution⟩) := by
    have state : actualBefore =
        ⟨actualBefore.remaining, some owner, actualBefore.execution⟩ := by
      cases actualBefore
      cases callbackActing
      rfl
    exact state ▸ actualPrior
  have initialEq : nativeInitial = (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  have counted := initialEq ▸ activeTrace
  obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
        actualBefore.remaining owner actualBefore.execution counted material' offered
  have eventEq := PhaseCount.onePacket_event_of_request implementation.runtime
    implementation.leaks implementation.bounds implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent) (setup.initialLaw.map
        encodeInputs)
        implementation.horizon implementation.scheduler actualBefore.remaining owner
          actualBefore.execution counted coordinate request material' offered
  have coordinateEvent : coordinate.event = named := by
    simpa only [material', PhaseCount.event?, Payload.event?, Option.some.injEq] using
      eventEq.symm
  have actualRequest : actualBefore.execution.application.SeedRequest owner
      ⟨actualBefore.execution.application.attempt, named⟩ := by
    have coordinateEq : coordinate =
        ⟨actualBefore.execution.application.attempt, named⟩ := by
      exact congrArg₂ CommitAttemptEvent.mk request.1 coordinateEvent
    exact coordinateEq ▸ request
  exact ⟨actualBefore, actualPrior, current, next, sourcePrior, sourceJoint, sourceLegal,
    sourceMoved, serial, opening, evidence, drawn, actualKept, callbackActing, past, viewed,
      signedNamespace, actualRequest, sourceKept, generation, saved, rank, active,
        data, action,
        decoded⟩

private theorem sourceReplay_matching_binding_atom
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (operational : implementation.Operational)
    (who : Player)
    (scale : Set.Icc (0 : ℝ) 1)
    (sourceBad : Set.Icc (0 : ℝ) 1)
    (actualGood : ∀ owner, owner ≠ who →
          ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
            implementation.leaks
            implementation.bounds nativeInitial implementation.horizon implementation.scheduler
              owner (⟨some control, trace⟩ : (nativeProtocol).History))
    (owner : Player) (different : owner ≠ who)
    (before : (nativeApplication).Control)
    (nativePrior : (nativeProtocol).Trace (some before))
    (nativeKept : TracePrefix nativePrior trace)
    (acting : before.actor = some owner)
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner ty)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, named⟩)
    (old : before.execution.application.attempt ≠ control.execution.application.attempt)
    (current next : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (moved : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (kept : TracePrefix (prior.extend joint legal moved)
      (canonicalSource setup implementation operational ⟨some control, trace⟩).trace)
    (generation : current.generation = before.execution.application.generation)
    (saved : instructionCount setup.program - ProtocolState.remaining setup.program
      current.saved =
      before.execution.application.attempt.phase)
    (rank : named.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point)
    (active : owner ∉ current.excluded)
    (serial : Nat) (opening : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup .concurrent)) (drawn : L.Val ty)
    (decoded : opening.bind (fun raw => raw.as? ty) = some drawn)
    (data : phaseRecoveryBindingData setup .concurrent named owner ty shape
      ((joint owner).map (·.semantic)) = (.success drawn, false)) :
    sourceReplayBindingDrawAtom setup values implementation owner
        (before.execution.recall owner) (before.execution.observe nativeApplication owner)
        ⟨some ⟨⟨.commitment named (owner, .prepared serial), opening⟩, evidence⟩⟩ =
      (setup.proposalRecoveryForeignRowFactors values scale sourceBad scale who
        ⟨some current, prior⟩ joint legal moved).2.1 := by
  classical
  let canonical := canonicalSource setup implementation operational ⟨some control, trace⟩
  have currentKept : TracePrefix prior canonical.trace :=
    (TracePrefix.extend .refl joint legal moved).trans kept
  have query := sourceReplay_historical_query_binding setup implementation operational who
    control before trace nativePrior nativeKept actualGood owner different named ty shape
      acting request old current prior currentKept generation saved rank active
  let information := setup.proposalRecoveryModel.infoOf owner prior
  let key := setup.proposalRecoveryQuery owner information
  rw [sourceReplay_prepared_binding_draw setup values implementation owner
    (before.execution.recall owner) (before.execution.observe nativeApplication owner)
      named ty shape serial opening evidence drawn decoded key query]
  obtain ⟨committing, sourceActing, _decode⟩ := source_binding_at_rank setup.program
    current.point
    named owner ty shape rank
  obtain ⟨move, selected⟩ : ∃ move, joint owner = some move := by
    cases selected : joint owner with
    | none => exact ((selected ▸ legal.2 owner) ⟨sourceActing, active⟩).elim
    | some move => exact ⟨move, rfl⟩
  have notMissing : move.semantic.missing = false := by
    cases missing : move.semantic.missing with
    | false => rfl
    | true =>
        simp only [selected, Option.map_some, phaseRecoveryBindingData, Option.elim_some,
          missing, ite_true] at data
        exact (Bool.false_ne_true (congrArg Prod.snd data).symm).elim
  have nonfailure : ¬ move.semantic.action.IsFailure := by
    intro failed
    have good := canonicalSource_foreignGood setup implementation operational who
      ⟨some control, trace⟩ actualGood
    have prefixGood := source_good_prefix setup who (prior.extend joint legal moved)
      canonical.trace kept good
    apply prefixGood owner different
    refine ⟨(information, move), ?_, ?_⟩
    · simp only [InfoSignals.ownPlay_extend, selected, List.mem_cons]
      exact Or.inl rfl
    · change move.semantic.missing = false ∧ _
      refine ⟨notMissing, ?_⟩
      cases action : move.semantic.action with
      | commit actor name payload publication =>
          rw [action] at failed
          change publication = .failure at failed
          simp only [failed]
      | reveal author name bit =>
          have notCommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal owner
            setup.program current.point move.semantic
              ((selected ▸ legal.2 owner).2.1) ⟨author, name, bit, action⟩
          rw [committing] at notCommit
          cases notCommit
  let actualChoice : setup.proposalRecoveryModel.Choice owner information :=
    ⟨joint owner, (setup.proposalRecoveryModel.menu_adequate owner prior _).mpr
      (setup.proposalRecoveryProtocol.legalOption_of_legal legal owner)⟩
  let semantic := setup.proposalRecoveryComponentSemanticChoice owner key
    (setup.proposalRecoveryComponentChoice owner information actualChoice)
  let domain : setup.CommitRecoveryValueChoice owner key.1 := ⟨semantic, by
    intro candidate chosen
    have same : candidate = move.semantic := by
      apply Option.some.inj
      exact chosen.symm.trans (by
        change (joint owner).map (·.semantic) = _
        rw [selected]
        rfl)
    subst candidate
    exact ⟨notMissing, nonfailure⟩⟩
  have ordinary : domain.val.val.map ProposalRecoveryMove.ordinary = joint owner :=
    setup.proposalRecovery_option_ordinary_of_atCommit current committing owner (joint owner)
      (by cases chosen : joint owner <;> simpa only [LegalOption, chosen] using legal.2 owner)
  have normalizedCurrent (raw : setup.commitRecoveryModel.InfoState owner) :
      (setup.commitRecoveryErasedInformation owner
        (setup.commitRecoveryNoMissInformation owner raw)).1.1.1 =
          raw.1.1.1.map (ProtocolView.eraseHistory owner setup.program) := by
    have kept : (setup.commitRecoveryNoMissInformation owner raw).1.1.1 = raw.1.1.1 := by
      unfold Setup.commitRecoveryNoMissInformation
      split
      · exact (setup.commitRecoveryWithAttemptExclusions_controls owner
          (setup.commitRecoveryAttemptStart owner raw)
            (setup.commitRecoverySavedExclusions owner raw) raw).1
      · rfl
    change ((setup.commitRecoveryNoMissInformation owner raw).1.1.1.map _) = _
    rw [kept]
  have queried := query
  unfold phaseProposalQuery? at queried
  obtain ⟨source, sourcePresent, keyEq⟩ := Option.map_eq_some_iff.mp queried
  have typedQuery := sourcePresent
  unfold phaseVirtualSourceQuery? at typedQuery
  obtain ⟨typed, typedPresent, sourceEq⟩ := Option.map_eq_some_iff.mp typedQuery
  have decodedQuery := typedPresent
  dsimp only [phaseVirtualSourceView?, ReactiveApplication.Execution.observe,
    phaseApplication,
    PhaseRuntimeState.playerView, State.playerView] at decodedQuery
  change (if same : owner = owner then _ else none) = some typed at decodedQuery
  rw [dite_eq_left rfl] at decodedQuery
  obtain ⟨view, nativeDecoded, viewEq⟩ := Option.map_eq_some_iff.mp decodedQuery
  have typedCurrent : key.1.1.1.1 =
      some (ProtocolView.virtualBindings owner (setup.context.map Prod.fst).toFinset
        setup.program (ProtocolView.eraseHistory owner setup.program view)) := by
    have first := congrArg Prod.fst keyEq
    rw [← first, ← sourceEq, normalizedCurrent]
    simp only [Setup.commitRecoveryErasedRead, Option.map_some, ← viewEq,
      ProtocolView.virtualBindings_eraseHistory, ProtocolView.eraseHistory_virtualBindings]
  change decodeEventView? setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref owner named
    ((serviceGraph setup .concurrent).playerStore owner
      before.execution.application.current.native.config.store) [] = some view
        at nativeDecoded
  have erasedDecoded : decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref owner named
      ((serviceGraph setup .concurrent).playerStore owner
        before.execution.application.current.native.config.store) [] =
        some (ProtocolView.eraseHistory owner setup.program view) := by
    rw [decodeEventView?_eraseHistory (past := []), nativeDecoded, Option.map_some]
  have componentActive : setup.commitRecoveryActive owner key.1.1.1 := by
    have legal := domain.val.property
    change setup.commitRecoveryModel.menu owner key.1 domain.val.val at legal
    rw [show domain.val.val = some move.semantic by
      change (joint owner).map (·.semantic) = _; rw [selected]; rfl] at legal
    exact legal.1
  have atom := sourceReplay_source_value_atom setup values
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref owner information named ty shape _ [] _
      erasedDecoded typedCurrent componentActive domain
  have domainValue : phaseRecoveryDomainValue setup .concurrent named owner ty shape
      domain.val.val = drawn := by
    unfold phaseRecoveryDomainValue
    rw [show domain.val.val = (joint owner).map (·.semantic) from rfl, data]
  rw [ordinary, domainValue] at atom
  rw [← atom]
  unfold Setup.proposalRecoveryForeignRowFactors
  simp only [sourceActing, different, ite_false, selected]
  cases action : move.semantic.action with
  | commit actor name payload publication =>
      cases publication with
      | failure => exact (nonfailure (by simp only [action, OwnAction.IsFailure])).elim
      | success value =>
          simp only [notMissing, Bool.false_eq_true, ite_false]
          rfl
  | reveal author name bit =>
      have notCommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal owner
        setup.program current.point move.semantic (by
          exact ((selected ▸ legal.2 owner).2.1)) ⟨author, name, bit, action⟩
      rw [committing] at notCommit
      cases notCommit

private theorem sourceReplay_historical_draw_product
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (who : Player)
    (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (acting : reference.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who
          (reference.execution.recall who)
          (reference.execution.observe nativeApplication who) event payload)
    (g : setup.proposalRecoveryProtocol.History)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (scale : Set.Icc (0 : ℝ) 1)
    (sourceBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val)
    (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val)
    (sourceBadBelow : sourceBad.val < 1)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
          ¬ setup.proposalRecoveryProtocol.terminal history.state →
          sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
            setup.proposalRecoveryNormalizedTrembledProfile
              scale.val scale.property.1 scale.property.2
              sourceBad.val sourceBad.property.1 sourceBad.property.2
              scale.val scale.property.1 scale.property.2 values owner
                (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (value : L.Val payload)
    (law : SourceRawReplayLaw (setup := setup) (values := values)
          (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩ reference
            ⟨some reference, referenceTrace⟩)
    (script : List (RawReplayChoice setup implementation))
    (member : script ∈ law.choices.support)
    (replayed : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
          reference ⟨some reference, referenceTrace⟩ script =
            some (⟨some control, trace⟩ : (nativeProtocol).History))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (actualGood : ∀ owner, owner ≠ who →
          ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
            implementation.leaks
            implementation.bounds nativeInitial implementation.horizon implementation.scheduler
              owner (⟨some control, trace⟩ : (nativeProtocol).History))
    (q : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (annotation : annotatedPrefixWeight setup values implementation operational sourceProfile
          nativeProfile who ⟨some control, trace⟩ tape q word *
            (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
              then 1 else 0) *
            sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
              event payload q word value (g, ⟨some targetCurrent, targetTrace⟩) ≠ 0)
    (related : RawReplayState setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
          (rawReplayLost setup implementation script) ⟨some reference, referenceTrace⟩
            ⟨some control, trace⟩) :
    (sourceReplayHistoricalDrawProducts setup values implementation who
      ⟨some control, trace⟩).1 =
    (setup.proposalRecoveryForeignProducts values scale sourceBad scale who
      (canonicalSource setup implementation operational
        ⟨some control, trace⟩).trace).2.1 := by
  classical
  have actualActing : control.actor = some who := related.2.1.trans acting
  have rawTrace := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have finalInputs := (nativeApplication).history_inputRecall nativeInitial
    implementation.horizon implementation.scheduler rawTrace
  have cleanHistory := (PhaseCount.onePacketMenu_countClean implementation.runtime
    implementation.leaks implementation.bounds implementation.scheduler).history nativeInitial
      implementation.horizon (fun state _ => PhaseCount.countClean_initial
        implementation.runtime implementation.leaks state) trace
  let canonical := canonicalSource setup implementation operational ⟨some control, trace⟩
  have canonicalRegistration := sourceReplay_canonical_registration (setup := setup)
    (implementation := implementation) (control := control) (trace := trace)
    (operational := operational)
  have registrationSourceRow := sourceReplay_registration_source_row (setup := setup)
    (values := values) (implementation := implementation) (control := control) (trace := trace)
    (operational := operational) (fullValues := fullValues) (who := who) (reference := reference)
    (referenceTrace := referenceTrace) (acting := acting) (event := event) (payload := payload)
    (clean := clean) (g := g) (targetCurrent := targetCurrent) (targetTrace := targetTrace)
    (scale := scale) (sourceBad := sourceBad) (scalePositive := scalePositive)
    (scaleBelow := scaleBelow) (sourceBadPositive := sourceBadPositive)
    (sourceBadBelow := sourceBadBelow) (sourceProfile := sourceProfile)
    (sourcePrescribed := sourcePrescribed) (nativeProfile := nativeProfile) (value := value)
    (law := law) (script := script) (member := member) (replayed := replayed) (tape := tape)
    (q := q) (word := word) (annotation := annotation) (related := related)
  have matchingBindingAtom := sourceReplay_matching_binding_atom (setup := setup) (values := values)
    (implementation := implementation) (control := control) (trace := trace)
    (operational := operational) (who := who) (scale := scale) (sourceBad := sourceBad)
    (actualGood := actualGood)
  let sourceWeights : ∀ {state}, setup.proposalRecoveryProtocol.Trace state → List ℝ≥0∞ :=
    fun {_} path => Trace.rec (motive := fun _ _ => List ℝ≥0∞) []
      (fun {before _after} prior joint legal moved earlier =>
        earlier ++ [(setup.proposalRecoveryForeignRowFactors values scale
          sourceBad scale who ⟨before, prior⟩ joint legal moved).2.1]) path
  have weightsStep {before after : setup.proposalRecoveryProtocol.State}
      (prior : setup.proposalRecoveryProtocol.Trace before)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal before joint)
      (moved : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support) :
      sourceWeights (prior.extend joint legal moved) = sourceWeights prior ++
        [(setup.proposalRecoveryForeignRowFactors values scale sourceBad scale who
          ⟨before, prior⟩ joint legal moved).2.1] := rfl
  have sourceLength {state} (path : setup.proposalRecoveryProtocol.Trace state) :
      (sourceWeights path).length = path.length := by
    induction path with
    | start => rfl
    | extend prior joint legal moved ih =>
        simp only [sourceWeights, List.length_append, List.length_singleton, Trace.length, ih]
  have sourceProduct {state} (path : setup.proposalRecoveryProtocol.Trace state) :
      (sourceWeights path).prod =
        (setup.proposalRecoveryForeignProducts values scale sourceBad scale who
          path).2.1 := by
    induction path with
    | start => rfl
    | extend prior joint legal moved ih =>
        simp only [sourceWeights, List.prod_append, List.prod_singleton, ih,
          Setup.proposalRecoveryForeignProducts]
  have sourceAt {state} (path : setup.proposalRecoveryProtocol.Trace state)
      (index : Fin path.length) :
      ∃ (before after : setup.proposalRecoveryProtocol.State)
        (prior : setup.proposalRecoveryProtocol.Trace before)
        (joint : Player → Option (ProposalRecoveryMove Player L))
        (legal : setup.proposalRecoveryProtocol.Legal before joint)
        (moved : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support),
        TracePrefix (prior.extend joint legal moved) path ∧ prior.length = index.val ∧
        (sourceWeights path)[index.val]'(by rw [sourceLength]; exact index.isLt) =
          (setup.proposalRecoveryForeignRowFactors values scale sourceBad scale who
            ⟨before, prior⟩ joint legal moved).2.1 := by
    induction path with
    | start => exact Fin.elim0 index
    | @extend before after prior joint legal moved ih =>
        by_cases old : index.val < prior.length
        · obtain ⟨first, last, earlier, choices, permitted, reached, kept, length, weight⟩ :=
            ih ⟨index.val, old⟩
          exact ⟨first, last, earlier, choices, permitted, reached,
            .extend kept joint legal moved, length, by
              simpa only [sourceWeights, List.getElem_append_left
                (by rw [sourceLength]; exact old)] using weight⟩
        · have last : index.val = prior.length := by
            have bound := index.isLt
            simp only [Trace.length] at bound
            omega
          exact ⟨before, after, prior, joint, legal, moved, .refl, last.symm, by
            simp only [sourceWeights, List.getElem_append_right
              (by rw [sourceLength]; omega), sourceLength, last, Nat.sub_self,
              List.getElem_cons_zero]⟩
  have bindingShape : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program),
      ProtocolState.atCommit program point = true →
      ∃ (event : Fin (eventCount program)) (owner : Player) (ty : L.Ty),
        outputLayout program event = .binding owner ty ∧
          event.val = instructionCount program - ProtocolState.remaining program point := by
    intro Γ O program
    induction program with
    | ret => intro point impossible; cases impossible
    | sample name fresh law next ih =>
        intro point committing
        cases point with
        | inl => cases committing
        | inr point =>
            obtain ⟨event, owner, ty, shape, rank⟩ := ih point committing
            refine ⟨event.succ, owner, ty, shape, ?_⟩
            have bound := ProtocolState.remaining_le_instructionCount next point
            simp only [Fin.val_succ, instructionCount, ProtocolState.remaining, Sum.elim_inr]
            omega
    | commit name owner fresh guard next ih =>
        intro point committing
        cases point with
        | inl =>
            exact ⟨⟨0, by simp only [eventCount]; omega⟩, owner, _, rfl, by
              simp only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
                Nat.sub_self]⟩
        | inr point =>
            obtain ⟨event, actor, ty, shape, rank⟩ := ih point committing
            refine ⟨event.succ, actor, ty, shape, ?_⟩
            have bound := ProtocolState.remaining_le_instructionCount next point
            simp only [Fin.val_succ, instructionCount, ProtocolState.remaining, Sum.elim_inr]
            omega
    | reveal published owner name fresh source unresolved next ih =>
        intro point committing
        cases point with
        | inl => cases committing
        | inr point =>
            obtain ⟨event, actor, ty, shape, rank⟩ := ih point committing
            refine ⟨event.succ, actor, ty, shape, ?_⟩
            have bound := ProtocolState.remaining_le_instructionCount next point
            simp only [Fin.val_succ, instructionCount, ProtocolState.remaining, Sum.elim_inr]
            omega
  let NativeIndex := Σ owner, Fin (control.execution.recall owner).length
  let nativeWeight : NativeIndex → ℝ≥0∞ := fun position =>
    if position.1 = who then 1 else
      match (control.execution.recall position.1)[position.2].emitted with
      | none => 1
      | some message =>
        if message.payload.attempt = control.execution.application.attempt then 1 else
          match message.payload.packet.call with
          | .commitment named _ =>
              if PhaseService.BindingAccepted implementation.runtime implementation.leaks
                ⟨message.payload.attempt, named⟩ position.1 control.execution then
                sourceReplayBindingDrawAtom setup values implementation position.1
                  ((control.execution.recall position.1).take position.2.val)
                  (control.execution.recall position.1)[position.2].beforeView
                  (control.execution.recall position.1)[position.2].action
              else 1
          | .opening .. | .malformed .. => 1
  let sourceWeight : Fin canonical.trace.length → ℝ≥0∞ := fun index =>
    (sourceWeights canonical.trace)[index.val]'(by rw [sourceLength]; exact index.isLt)
  have nativeProduct :
      (sourceReplayHistoricalDrawProducts setup values implementation who
        ⟨some control, trace⟩).1 = ∏ position, nativeWeight position := by
    rw [Fintype.prod_sigma]
    simp only [sourceReplayHistoricalDrawProducts, Prod.fst_prod]
    apply Finset.prod_congr rfl
    intro owner _
    by_cases focal : owner = who
    · simp only [focal, ite_true, nativeWeight, Finset.prod_const_one]
    · simp only [focal, ite_false]
      rw [← Fin.prod_univ_fun_getElem]
      rw [Prod.fst_prod]
      conv_lhs =>
        rw [← Fin.prod_congr' _ (show (control.execution.recall owner).length =
          ((control.execution.recall owner).zipIdx).length from List.length_zipIdx.symm)]
      simp only [List.getElem_zipIdx, Nat.zero_add, nativeWeight, focal, ite_false,
        Fin.val_cast, Fin.getElem_fin]
      apply Finset.prod_congr rfl
      intro index _
      cases emitted : (control.execution.recall owner)[index.val].emitted with
      | none => rfl
      | some message =>
          by_cases old : message.payload.attempt = control.execution.application.attempt
          · simp only [old, ite_true]
          · simp only [old, ite_false]
            cases call : message.payload.packet.call with
            | opening named handle raw => rfl
            | malformed raw => rfl
            | commitment named handle =>
                dsimp only
                split_ifs <;> rfl
  have sourceProduct' :
      (setup.proposalRecoveryForeignProducts values scale sourceBad scale who
        canonical.trace).2.1 =
        ∏ index, sourceWeight index := by
    rw [← sourceProduct]
    rw [← Fin.prod_univ_getElem (sourceWeights canonical.trace)]
    conv_rhs => rw [← Fin.prod_congr' _ (sourceLength canonical.trace)]
    apply Finset.prod_congr rfl
    intro index _
    rfl
  have nativeRow (position : NativeIndex) (nontrivial : nativeWeight position ≠ 1) :
      ∃ (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
        (named : (serviceGraph setup .concurrent).EventId)
        (current next : CommitRecoveryState setup.program)
        (prior : setup.proposalRecoveryProtocol.Trace (some current))
        (joint : Player → Option (ProposalRecoveryMove Player L))
        (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
        (moved : some next ∈
          (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support),
        TracePrefix (prior.extend joint legal moved) canonical.trace ∧
        ProtocolState.actor setup.program current.point = some position.1 ∧
        current.generation = message.payload.attempt.generation ∧
        instructionCount setup.program - ProtocolState.remaining setup.program current.saved =
          message.payload.attempt.phase ∧
        instructionCount setup.program - ProtocolState.remaining setup.program current.point =
          named.val ∧
        (control.execution.recall position.1)[position.2].emitted = some message ∧
        message.sender = position.1 ∧
        PhaseCount.event? message.payload = some ⟨message.payload.attempt, named⟩ ∧
        nativeWeight position = (setup.proposalRecoveryForeignRowFactors values scale
          sourceBad scale who ⟨some current, prior⟩ joint legal moved).2.1 := by
    rcases position with ⟨owner, index⟩
    have different : owner ≠ who := by
      intro same
      simp only [nativeWeight, same, ite_true, ne_eq, not_true_eq_false] at nontrivial
    cases emitted : (control.execution.recall owner)[index].emitted with
    | none =>
        simp only [nativeWeight, different, ite_false, emitted] at nontrivial
        exact (nontrivial rfl).elim
    | some message =>
      by_cases old : message.payload.attempt = control.execution.application.attempt
      · simp only [nativeWeight, different, ite_false, emitted, old, ite_true] at nontrivial
        exact (nontrivial rfl).elim
      · cases call : message.payload.packet.call with
        | opening =>
            simp only [nativeWeight, different, ite_false, emitted, old, call] at nontrivial
            exact (nontrivial rfl).elim
        | malformed =>
            simp only [nativeWeight, different, ite_false, emitted, old, call] at nontrivial
            exact (nontrivial rfl).elim
        | commitment named handle =>
          by_cases accepted : PhaseService.BindingAccepted implementation.runtime
              implementation.leaks ⟨message.payload.attempt, named⟩ owner control.execution
          · have recorded : (control.execution.recall owner)[index] ∈
                control.execution.recall owner := List.getElem_mem index.isLt
            have output : message ∈ (nativeApplication).outputs
                (control.execution.recall owner) :=
              List.mem_filterMap.mpr ⟨_, recorded, emitted⟩
            have input : message ∈ control.execution.network.inputs := by
              rw [← finalInputs owner] at output
              exact (List.mem_filter.mp output).1
            have sender : message.sender = owner := by
              rw [← finalInputs owner] at output
              simpa only [decide_eq_true_eq] using (List.mem_filter.mp output).2
            have correct := ((PhaseCount.permits_eq_true_iff _ _).mp
              (cleanHistory.2 message input)).2.1
            change CountCallCorrect _ (PhaseCount.nativeMessage message) at correct
            simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
            obtain ⟨ty, shape⟩ : ∃ ty,
                (serviceGraph setup .concurrent).outputLayout named = .binding owner ty := by
              cases layout : (serviceGraph setup .concurrent).outputLayout named with
              | binding actor ty =>
                  have same : actor = owner := by
                    have owned := correct.1
                    simp only [bindingOwnedBy, layout, decide_eq_true_eq] at owned
                    change actor = message.sender at owned
                    exact owned.trans sender
                  subst actor
                  exact ⟨ty, rfl⟩
              | publicData ty =>
                  simp only [bindingOwnedBy] at correct
                  rw [layout] at correct
                  cases correct.1
              | privateInput actor ty =>
                  simp only [bindingOwnedBy] at correct
                  rw [layout] at correct
                  cases correct.1
              | publication ty =>
                  simp only [bindingOwnedBy] at correct
                  rw [layout] at correct
                  cases correct.1
            obtain ⟨serial, opening, evidence, _handle, _sender, action, _fresh,
              _namespace, _meaning⟩ := sourceReplay_recorded_binding_registration setup
                implementation control trace owner _ recorded message emitted named ty
                  shape handle call
            let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
              ⟨⟨.commitment named (owner, .prepared serial), opening⟩, evidence⟩
            have sent : (control.execution.recall owner)[index].action.transmission =
                some material := congrArg ReactiveApplication.Action.transmission action
            obtain ⟨actualBefore, actualPrior, current, next, sourcePrior, sourceJoint,
              sourceLegal, sourceMoved, serial, opening, evidence, drawn, actualKept,
              actualActing, past, viewed, signedNamespace, request, sourceKept,
                generation, saved,
              rank, active, data, action, decoded⟩ := registrationSourceRow owner different
                index material sent message emitted named ty shape handle call old accepted
            have atom := matchingBindingAtom owner different actualBefore
              actualPrior actualKept
              actualActing named ty shape request (by rw [signedNamespace]; exact old)
              current next sourcePrior sourceJoint sourceLegal sourceMoved sourceKept
                (generation.trans (congrArg CommitAttemptId.generation signedNamespace.symm))
                (saved.trans (congrArg CommitAttemptId.phase signedNamespace.symm))
                  rank.symm active
                serial opening evidence drawn decoded data
            refine ⟨message, named, current, next, sourcePrior, sourceJoint, sourceLegal,
              sourceMoved, sourceKept, (source_binding_at_rank setup.program current.point
                named owner ty shape rank.symm).2.1, generation, saved, rank, rfl,
              sender, ?_, ?_⟩
            · simp only [PhaseCount.event?, call, Payload.event?, Option.map_some]
            · simp only [nativeWeight, different, ite_false, emitted, old, call, accepted,
                ite_true]
              rw [action, ← past, viewed]
              exact atom
          · simp only [nativeWeight, different, ite_false, emitted, old, call, accepted]
              at nontrivial
            exact (nontrivial rfl).elim
  have readRow {before after : setup.proposalRecoveryProtocol.State}
      (prior : setup.proposalRecoveryProtocol.Trace before)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal before joint)
      (moved : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support)
      {last : setup.proposalRecoveryProtocol.State}
      (final : setup.proposalRecoveryProtocol.Trace last)
      (kept : TracePrefix (prior.extend joint legal moved) final) :
      (sourceWeights final)[prior.length]'(by
        rw [sourceLength]
        have bound := kept.length_le
        simp only [Trace.length] at bound
        omega) =
        (setup.proposalRecoveryForeignRowFactors values scale sourceBad scale who
          ⟨before, prior⟩ joint legal moved).2.1 := by
    have lookup : (sourceWeights final)[prior.length]? = some
        (setup.proposalRecoveryForeignRowFactors values scale sourceBad scale who
          ⟨before, prior⟩ joint legal moved).2.1 := by
      induction kept with
      | refl =>
          rw [weightsStep, List.getElem?_append_right (by rw [sourceLength])]
          simp only [sourceLength, Nat.sub_self, List.getElem?_cons_zero]
      | @extend earlierState laterState earlier kept choices permitted reached ih =>
          rw [weightsStep, List.getElem?_append_left (by
            rw [sourceLength]
            have bound := kept.length_le
            simp only [Trace.length] at bound
            omega)]
          exact ih
    exact Option.some.inj ((List.getElem?_eq_getElem (by
      rw [sourceLength]
      have bound := kept.length_le
      simp only [Trace.length] at bound
      omega)).symm.trans lookup)
  have sourcePrefixLength
      (left right : CommitRecoveryState setup.program)
      (first : setup.proposalRecoveryProtocol.Trace (some left))
      (second : setup.proposalRecoveryProtocol.Trace (some right))
      (firstKept : TracePrefix first canonical.trace)
      (secondKept : TracePrefix second canonical.trace)
      (generation : left.generation = right.generation)
      (rank : instructionCount setup.program - ProtocolState.remaining setup.program
        left.point =
        instructionCount setup.program - ProtocolState.remaining setup.program right.point) :
      first.length = second.length := by
    have same := setup.commitRecovery_ancestor_eq_of_control_eq
      (setup.proposalRecoveryEraseTrace_prefix firstKept).reachesWithin
      (setup.proposalRecoveryEraseTrace_prefix secondKept).reachesWithin (by
        change left.generation * (instructionCount setup.program + 1) +
            (instructionCount setup.program - ProtocolState.remaining setup.program
              left.point) +
              1 =
          right.generation * (instructionCount setup.program + 1) +
            (instructionCount setup.program - ProtocolState.remaining setup.program
              right.point) +
              1
        rw [generation, rank])
    have length := congrArg
      (fun history : setup.commitRecoveryProtocol.History => history.trace.length) same
    simpa only [setup.proposalRecoveryEraseTrace_length] using length
  have emissionOrder := (nativeApplication).emissionOrder_history implementation.scheduler
    nativeInitial implementation.horizon rawTrace
  have outputDistinct (owner : Player) :
      ((nativeApplication).outputs (control.execution.recall owner)).Nodup := by
    apply List.Nodup.of_map Message.id
    rw [emissionOrder owner]
    exact List.nodup_range.map (fun _ _ equal => (Prod.mk.inj equal).2)
  have uniqueIndices (past : List (nativeApplication).PlayerEntry)
      (distinct : ((nativeApplication).outputs past).Nodup)
      (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))) :
      ∀ (first : Nat) (firstBound : first < past.length)
        (second : Nat) (secondBound : second < past.length),
        past[first].emitted = some message → past[second].emitted = some message →
          first = second := by
    induction past with
    | nil => intro first bound; simp only [List.length_nil] at bound; omega
    | cons head rest ih =>
        intro first firstBound second secondBound firstSent secondSent
        cases first with
        | zero =>
            cases second with
            | zero => rfl
            | succ second =>
                have missing : message ∉ (nativeApplication).outputs rest := by
                  have headSent : head.emitted = some message := firstSent
                  exact (List.nodup_cons.mp (show
                      (message :: (nativeApplication).outputs rest).Nodup by
                    simpa only [ReactiveApplication.outputs, List.filterMap_cons,
                      headSent] using distinct)).1
                have inside : second < rest.length := by
                  simp only [List.length_cons] at secondBound
                  omega
                exact (missing (List.mem_filterMap.mpr ⟨rest[second]'inside,
                  List.getElem_mem inside,
                    by simpa only [List.getElem_cons_succ] using secondSent⟩)).elim
        | succ first =>
            cases second with
            | zero =>
                have missing : message ∉ (nativeApplication).outputs rest := by
                  have headSent : head.emitted = some message := secondSent
                  exact (List.nodup_cons.mp (show
                      (message :: (nativeApplication).outputs rest).Nodup by
                    simpa only [ReactiveApplication.outputs, List.filterMap_cons,
                      headSent] using distinct)).1
                have inside : first < rest.length := by
                  simp only [List.length_cons] at firstBound
                  omega
                exact (missing (List.mem_filterMap.mpr ⟨rest[first]'inside,
                  List.getElem_mem inside,
                    by simpa only [List.getElem_cons_succ] using firstSent⟩)).elim
            | succ second =>
                have tailDistinct : ((nativeApplication).outputs rest).Nodup := by
                  cases sent : head.emitted with
                  | none =>
                      simpa only [ReactiveApplication.outputs, List.filterMap_cons,
                        sent] using distinct
                  | some output =>
                      exact (List.nodup_cons.mp (show
                          (output :: (nativeApplication).outputs rest).Nodup by
                        simpa only [ReactiveApplication.outputs, List.filterMap_cons,
                          sent] using distinct)).2
                exact congrArg Nat.succ (ih tailDistinct first
                  (by simp only [List.length_cons] at firstBound; omega) second
                    (by simp only [List.length_cons] at secondBound; omega)
                    (by simpa only [List.getElem_cons_succ] using firstSent)
                    (by simpa only [List.getElem_cons_succ] using secondSent))
  choose mappedMessage mappedEvent mappedCurrent mappedNext mappedPrior mappedJoint
    mappedLegal mappedMoved mappedSpec using nativeRow
  let forward := fun (position : NativeIndex) (nontrivial : nativeWeight position ≠ 1) =>
    (⟨(mappedPrior position nontrivial).length, by
      have bound := (mappedSpec position nontrivial).1.length_le
      simp only [Trace.length] at bound
      omega⟩ : Fin canonical.trace.length)
  have forwardWeight (position : NativeIndex) (nontrivial : nativeWeight position ≠ 1) :
      nativeWeight position = sourceWeight (forward position nontrivial) := by
    rw [(mappedSpec position nontrivial).2.2.2.2.2.2.2.2]
    exact (readRow (mappedPrior position nontrivial) (mappedJoint position nontrivial)
      (mappedLegal position nontrivial) (mappedMoved position nontrivial) canonical.trace
        (mappedSpec position nontrivial).1).symm
  have forwardInjective (left : NativeIndex) (leftNontrivial : nativeWeight left ≠ 1)
      (right : NativeIndex) (rightNontrivial : nativeWeight right ≠ 1)
      (same : forward left leftNontrivial = forward right rightNontrivial) : left =
        right := by
    obtain ⟨leftKept, leftActor, leftGeneration, leftSaved, leftRank, leftEmitted,
      leftSender, leftEvent, _leftWeight⟩ := mappedSpec left leftNontrivial
    obtain ⟨rightKept, rightActor, rightGeneration, rightSaved, rightRank, rightEmitted,
      rightSender, rightEvent, _rightWeight⟩ := mappedSpec right rightNontrivial
    have leftPriorKept : TracePrefix (mappedPrior left leftNontrivial) canonical.trace :=
      (TracePrefix.extend .refl (mappedJoint left leftNontrivial)
        (mappedLegal left leftNontrivial) (mappedMoved left leftNontrivial)).trans leftKept
    have rightPriorKept : TracePrefix (mappedPrior right rightNontrivial) canonical.trace :=
      (TracePrefix.extend .refl (mappedJoint right rightNontrivial)
        (mappedLegal right rightNontrivial) (mappedMoved right
          rightNontrivial)).trans rightKept
    have histories := leftPriorKept.eq_of_same_length rightPriorKept
      (congrArg Fin.val same)
    have states : mappedCurrent left leftNontrivial = mappedCurrent right rightNontrivial :=
      Option.some.inj (congrArg History.state histories)
    have ownerEq : left.1 = right.1 := Option.some.inj
      (leftActor.symm.trans ((congrArg (ProtocolState.actor setup.program)
        (congrArg CommitRecoveryState.point states)).trans rightActor))
    rcases left with ⟨owner, first⟩
    rcases right with ⟨other, second⟩
    cases ownerEq
    have namespaceEq : (mappedMessage ⟨owner, first⟩ leftNontrivial).payload.attempt =
        (mappedMessage ⟨owner, second⟩ rightNontrivial).payload.attempt :=
      congrArg₂ CommitAttemptId.mk
        (leftSaved.symm.trans ((congrArg (fun state : CommitRecoveryState setup.program =>
          instructionCount setup.program - ProtocolState.remaining setup.program state.saved)
            states).trans rightSaved))
        (leftGeneration.symm.trans ((congrArg CommitRecoveryState.generation states).trans
          rightGeneration))
    have eventEq : mappedEvent ⟨owner, first⟩ leftNontrivial =
        mappedEvent ⟨owner, second⟩ rightNontrivial := Fin.ext
      (leftRank.symm.trans ((congrArg (fun state : CommitRecoveryState setup.program =>
        instructionCount setup.program - ProtocolState.remaining setup.program state.point)
          states).trans rightRank))
    have leftInput : mappedMessage ⟨owner, first⟩ leftNontrivial ∈
        control.execution.network.inputs := by
      have output := List.mem_filterMap.mpr
        ⟨_, List.getElem_mem first.isLt, leftEmitted⟩
      change _ ∈ (nativeApplication).outputs (control.execution.recall owner) at output
      rw [← finalInputs owner] at output
      exact (List.mem_filter.mp output).1
    have rightInput : mappedMessage ⟨owner, second⟩ rightNontrivial ∈
        control.execution.network.inputs := by
      have output := List.mem_filterMap.mpr
        ⟨_, List.getElem_mem second.isLt, rightEmitted⟩
      change _ ∈ (nativeApplication).outputs (control.execution.recall owner) at output
      rw [← finalInputs owner] at output
      exact (List.mem_filter.mp output).1
    have messageEq := PhaseCount.Permits.eq_of_same_event
      ((PhaseCount.permits_eq_true_iff _ _).mp (cleanHistory.2 _ leftInput))
      ((PhaseCount.permits_eq_true_iff _ _).mp (cleanHistory.2 _ rightInput))
      leftInput rightInput
      (fun left leftInput right rightInput same =>
        (nativeApplication).input_identifier_injective_history nativeInitial
          implementation.horizon implementation.scheduler control rawTrace left right
            leftInput rightInput same)
      (leftSender.trans rightSender.symm)
      (by rw [leftEvent, rightEvent, namespaceEq, eventEq])
    have indices : first = second := Fin.ext (uniqueIndices
      (control.execution.recall owner) (outputDistinct owner)
      (mappedMessage ⟨owner, first⟩ leftNontrivial) first.val first.isLt second.val
        second.isLt
        leftEmitted (rightEmitted.trans (congrArg some messageEq.symm)))
    exact congrArg (fun index => (⟨owner, index⟩ : NativeIndex)) indices
  have forwardSurjective (index : Fin canonical.trace.length)
      (nontrivial : sourceWeight index ≠ 1) :
      ∃ (position : NativeIndex) (nativeNontrivial : nativeWeight position ≠ 1),
        forward position nativeNontrivial = index := by
    obtain ⟨before, after, prior, joint, legal, moved, kept, depth, weight⟩ :=
      sourceAt canonical.trace index
    have rowNontrivial :
        (setup.proposalRecoveryForeignRowFactors values scale sourceBad scale who
          ⟨before, prior⟩ joint legal moved).2.1 ≠ 1 := by
      rw [← weight]
      exact nontrivial
    cases before with
    | none =>
        simp only [Setup.proposalRecoveryForeignRowFactors] at rowNontrivial
        exact (rowNontrivial rfl).elim
    | some current =>
      cases actor : ProtocolState.actor setup.program current.point with
      | none =>
          simp only [Setup.proposalRecoveryForeignRowFactors, actor] at rowNontrivial
          exact (rowNontrivial rfl).elim
      | some owner =>
        have different : owner ≠ who := by
          intro same
          simp only [Setup.proposalRecoveryForeignRowFactors, actor, same, ite_true]
            at rowNontrivial
          exact rowNontrivial rfl
        cases selected : joint owner with
        | none =>
            simp only [Setup.proposalRecoveryForeignRowFactors, actor, different,
              ite_false, selected] at rowNontrivial
            exact (rowNontrivial rfl).elim
        | some move =>
          have offered := legal.2 owner
          rw [selected] at offered
          have active : owner ∉ current.excluded := offered.1.2
          cases action : move.semantic.action with
          | reveal author name bit =>
              simp only [Setup.proposalRecoveryForeignRowFactors, actor, different,
                ite_false, selected, action] at rowNontrivial
              exact (rowNontrivial rfl).elim
          | commit author name payload publication =>
            have committing : ProtocolState.atCommit setup.program current.point = true := by
              cases isCommit : ProtocolState.atCommit setup.program current.point with
              | true => rfl
              | false =>
                  obtain ⟨other, bit, reveal⟩ :=
                    ProtocolState.recoveryAvailable_reveal_of_not_commit owner setup.program
                      current.point actor isCommit move.semantic offered.2.1
                  have impossible := congrArg CommitRecoveryMove.action reveal
                  rw [action] at impossible
                  cases impossible
            have notMissing : move.semantic.missing = false := by
              cases missing : move.semantic.missing with
              | false => rfl
              | true =>
                  simp only [Setup.proposalRecoveryForeignRowFactors, actor, different,
                    ite_false, selected, action, missing, ite_true] at rowNontrivial
                  exact (rowNontrivial rfl).elim
            obtain ⟨next, _nativeMoved, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
            obtain ⟨named, typedOwner, ty, shape, rank⟩ :=
              bindingShape setup.program current.point committing
            have ownerEq : typedOwner = owner := Option.some.inj
              ((source_binding_at_rank setup.program current.point named typedOwner ty
                shape rank).2.1.symm.trans actor)
            subst typedOwner
            have missingFalse : (phaseRecoveryBindingData setup .concurrent named owner
                ty shape ((joint owner).map (·.semantic))).2 = false := by
              simp only [phaseRecoveryBindingData, selected, Option.map_some,
                Option.elim_some, notMissing, Bool.false_eq_true, ite_false]
            have survives : owner ∉ next.excluded := by
              intro excluded
              have missing := (source_binding_missing_iff setup current next joint legal
                moved owner named ty shape rank active).mpr excluded
              rw [missingFalse] at missing
              cases missing
            have sourceGood := canonicalSource_foreignGood setup implementation operational
              who ⟨some control, trace⟩ actualGood
            have prefixGood := source_good_prefix setup who (prior.extend joint legal moved)
              canonical.trace kept sourceGood
            obtain ⟨drawn, data⟩ := source_foreign_binding_success setup who owner different
              named ty shape current prior joint legal next moved rank active
                survives prefixGood
            obtain ⟨handle, record, material, message, recorded, transmitted, emitted,
              sender, call, generation, saved, old, accepted, _value⟩ :=
                canonicalRegistration current next prior joint legal moved kept owner
                  named ty shape rank active drawn data
            obtain ⟨offset, bounded, recordEq⟩ := List.mem_iff_getElem.mp recorded
            let position : NativeIndex := ⟨owner, ⟨offset, bounded⟩⟩
            have emittedAt : (control.execution.recall owner)[offset].emitted =
                some message := by rw [recordEq]; exact emitted
            have sentAt : (control.execution.recall owner)[offset].action.transmission =
                some material := by rw [recordEq]; exact transmitted
            obtain ⟨actualBefore, actualPrior, first, last, firstPrior, firstJoint,
              firstLegal, firstMoved, serial, opening, evidence, decoded,
              actualKept, callbackActing, past, viewed, signedAttempt, request,
              firstKept, firstGeneration, firstSaved, firstRank, firstActive,
              firstData, firstAction, decodedOpening⟩ :=
                registrationSourceRow owner different ⟨offset, bounded⟩ material sentAt
                  message emittedAt named ty shape handle call old accepted
            have atom := matchingBindingAtom owner different actualBefore actualPrior
              actualKept callbackActing named ty shape request
              (by rw [signedAttempt]; exact old) first last firstPrior firstJoint
              firstLegal firstMoved firstKept
              (firstGeneration.trans
                (congrArg CommitAttemptId.generation signedAttempt.symm))
              (firstSaved.trans (congrArg CommitAttemptId.phase signedAttempt.symm))
              firstRank.symm firstActive serial opening evidence decoded
                decodedOpening firstData
            have firstBeforeKept : TracePrefix firstPrior canonical.trace :=
              (TracePrefix.extend .refl firstJoint firstLegal firstMoved).trans firstKept
            have beforeKept : TracePrefix prior canonical.trace :=
              (TracePrefix.extend .refl joint legal moved).trans kept
            have sameDepth := sourcePrefixLength first current firstPrior prior
              firstBeforeKept beforeKept (firstGeneration.trans generation.symm)
                (firstRank.trans rank)
            have rowAt : sourceWeight index =
                (setup.proposalRecoveryForeignRowFactors values scale sourceBad scale who
                  ⟨some first, firstPrior⟩ firstJoint firstLegal firstMoved).2.1 := by
              let firstIndex : Fin canonical.trace.length := ⟨firstPrior.length, by
                have bound := firstKept.length_le
                simp only [Trace.length] at bound
                omega⟩
              have sameIndex : firstIndex = index :=
                Fin.ext (sameDepth.trans depth)
              rw [← sameIndex]
              exact readRow firstPrior firstJoint firstLegal firstMoved
                canonical.trace firstKept
            have nativeAt : nativeWeight position = sourceWeight index := by
              rw [rowAt]
              simp only [nativeWeight, position, Fin.getElem_fin, different, ite_false,
                emittedAt, old, call, accepted, ite_true]
              simp only [Fin.getElem_fin] at firstAction viewed
              rw [firstAction, ← past, viewed]
              exact atom
            have nativeNontrivial : nativeWeight position ≠ 1 := by
              rw [nativeAt]
              exact nontrivial
            refine ⟨position, nativeNontrivial, ?_⟩
            obtain ⟨mappedKept, _mappedActor, mappedGeneration, _mappedSaved, mappedRank,
              mappedEmitted, _mappedSender, mappedEventEq, _mappedWeight⟩ :=
                mappedSpec position nativeNontrivial
            have messageEq : mappedMessage position nativeNontrivial = message :=
              Option.some.inj (mappedEmitted.symm.trans emittedAt)
            have eventPresent : PhaseCount.event? message.payload =
                some ⟨message.payload.attempt, named⟩ := by
              simp only [PhaseCount.event?, call, Payload.event?, Option.map_some]
            rw [messageEq, eventPresent] at mappedEventEq
            have eventEq : mappedEvent position nativeNontrivial = named :=
              (congrArg CommitAttemptEvent.event (Option.some.inj mappedEventEq)).symm
            have mappedBeforeKept :
                TracePrefix (mappedPrior position nativeNontrivial) canonical.trace :=
              (TracePrefix.extend .refl (mappedJoint position nativeNontrivial)
                (mappedLegal position nativeNontrivial)
                  (mappedMoved position nativeNontrivial)).trans mappedKept
            have sameMappedDepth := sourcePrefixLength
              (mappedCurrent position nativeNontrivial) current
              (mappedPrior position nativeNontrivial) prior mappedBeforeKept beforeKept
              (by
                rw [messageEq] at mappedGeneration
                exact mappedGeneration.trans generation.symm)
              (mappedRank.trans ((congrArg Fin.val eventEq).trans rank))
            apply Fin.ext
            exact sameMappedDepth.trans depth
  rw [nativeProduct, sourceProduct']
  exact Finset.prod_bij_ne_one
    (fun position _ nontrivial => forward position nontrivial)
    (fun _ _ _ => Finset.mem_univ _)
    (fun left _ leftNontrivial right _ rightNontrivial same =>
      forwardInjective left leftNontrivial right rightNontrivial same)
    (fun index _ nontrivial => by
      obtain ⟨position, nativeNontrivial, same⟩ := forwardSurjective index nontrivial
      exact ⟨position, Finset.mem_univ _, nativeNontrivial, same⟩)
    (fun position _ nontrivial => forwardWeight position nontrivial)

private theorem sourceReplay_lost_draw_product
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (who : Player)
    (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (acting : reference.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who
          (reference.execution.recall who)
          (reference.execution.observe nativeApplication who) event payload)
    (g : setup.proposalRecoveryProtocol.History)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (scale : Set.Icc (0 : ℝ) 1)
    (sourceBad : Set.Icc (0 : ℝ) 1)
    (nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val)
    (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val)
    (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val)
    (nativeBadBelow : nativeBad.val < 1)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
          ¬ setup.proposalRecoveryProtocol.terminal history.state →
          sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
            setup.proposalRecoveryNormalizedTrembledProfile
              scale.val scale.property.1 scale.property.2
              sourceBad.val sourceBad.property.1 sourceBad.property.2
              scale.val scale.property.1 scale.property.2 values owner
                (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (value : L.Val payload)
    (law : SourceRawReplayLaw (setup := setup) (values := values)
          (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩ reference
            ⟨some reference, referenceTrace⟩)
    (script : List (RawReplayChoice setup implementation))
    (member : script ∈ law.choices.support)
    (replayed : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
          reference ⟨some reference, referenceTrace⟩ script =
            some (⟨some control, trace⟩ : (nativeProtocol).History))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (q : setup.proposalRecoveryProtocol.History)
    (word : SourceProgram.History Player L)
    (annotation : annotatedPrefixWeight setup values implementation operational sourceProfile
          nativeProfile who ⟨some control, trace⟩ tape q word *
            (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
              then 1 else 0) *
            sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
              event payload q word value (g, ⟨some targetCurrent, targetTrace⟩) ≠ 0)
    (related : RawReplayState setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
          (rawReplayLost setup implementation script) ⟨some reference, referenceTrace⟩
            ⟨some control, trace⟩) :
    (sourceReplayHistoricalDrawProducts setup values implementation who
      ⟨some control, trace⟩).2 =
    (sourceReplayScriptProducts setup values implementation scale who
      ⟨some reference, referenceTrace⟩ ⟨some control, trace⟩ script).1 := by
  classical
  let model := (nativeMenu).information nativeInitial implementation.horizon
    implementation.scheduler
  have actualActing : control.actor = some who := related.2.1.trans acting
  have rawTrace := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have ownProductExtend := sourceReplay_foreign_own_play_extend (setup := setup)
    (implementation := implementation) (who := who)
  have recallWord := sourceReplay_recall_own_play_product (setup := setup)
    (implementation := implementation)
  have taggedRegistration := sourceReplay_tagged_registration (setup := setup) (values := values)
    (implementation := implementation) (control := control) (trace := trace)
    (operational := operational) (fullValues := fullValues) (who := who) (reference := reference)
    (referenceTrace := referenceTrace) (acting := acting) (event := event) (payload := payload)
    (clean := clean) (g := g) (targetCurrent := targetCurrent) (targetTrace := targetTrace)
    (scale := scale) (sourceBad := sourceBad) (scalePositive := scalePositive)
    (scaleBelow := scaleBelow) (sourceBadPositive := sourceBadPositive)
    (sourceBadBelow := sourceBadBelow) (sourceProfile := sourceProfile)
    (sourcePrescribed := sourcePrescribed) (nativeProfile := nativeProfile) (value := value)
    (script := script) (tape := tape) (q := q) (word := word) (annotation := annotation)
    (related := related)
  let lostAt := fun (owner : Player)
      (record : model.InfoState owner × (nativeApplication).Action) =>
    match record.1, record.2.transmission with
    | some observed, some material => match material.call.packet with
      | .commitment named _ =>
          if observed.2.application.2.attempt ≠ control.execution.application.attempt ∧
              ¬ PhaseService.BindingAccepted implementation.runtime implementation.leaks
                ⟨observed.2.application.2.attempt, named⟩ owner control.execution then
            sourceReplayBindingDrawAtom setup values implementation owner observed.1
              observed.2 record.2
          else 1
      | .opening .. | .malformed .. => 1
    | _, _ => 1
  let folded := fun history : (nativeProtocol).History =>
    ∏ owner, if owner = who then (1 : ℝ≥0∞) else
      ((model.ownPlay owner history.trace).map (lostAt owner)).prod
  have appendFold (previous actual : (nativeProtocol).History)
      (next : (nativeProtocol).State) (joint : Player → Option (nativeApplication).Action)
      (appended : sourceReplayAppend setup implementation previous next joint = some actual) :
      folded actual = folded previous * ∏ owner, if owner = who then 1 else
        match joint owner with
        | none => 1
        | some action => lostAt owner (model.infoOf owner previous.trace, action) := by
    unfold sourceReplayAppend at appended
    split at appended
    · split at appended
      · cases Option.some.inj appended
        exact ownProductExtend lostAt previous.trace joint _ _
      · cases appended
    · cases appended
  have foldScript {original : (nativeProtocol).History}
      {choices : List (RawReplayChoice setup implementation)} {mass : ℝ≥0∞}
      (supportedScript : SourceReplayScriptMass (setup := setup) (values := values)
        (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩
          reference original choices mass) :
      ∀ (actualPrefix : (nativeProtocol).History),
        sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
            original choices = some actualPrefix →
        RawReplayState setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
          (rawReplayLost setup implementation choices) original actualPrefix →
        SourceReplayLostRestricted setup implementation ⟨some targetCurrent, targetTrace⟩
          reference who (rawReplayLost setup implementation choices) →
        TracePrefix original.trace referenceTrace → TracePrefix actualPrefix.trace trace →
        (sourceReplayScriptProducts setup values implementation scale who original
          actualPrefix choices).1 = folded actualPrefix := by
    induction supportedScript with
    | start =>
      intro actualPrefix produced _related _restricted _kept _actualKept
      simp only [sourceRawReplay] at produced
      cases Option.some.inj produced
      change (1 : ℝ≥0∞) = ∏ owner : Player, if owner = who then 1 else 1
      simp only [ite_self, Finset.prod_const_one]
    | @deterministic before after prior joint legal moved earlierChoices earlierMass
        quiet previous previousReplay previousRelated previousRestricted earlier ih =>
      intro actualPrefix produced _nextRelated _nextRestricted kept actualKept
      obtain ⟨previous', previousReplay', priorEq⟩ := sourceRawReplay_step_prior setup
        implementation who ⟨some targetCurrent, targetTrace⟩ reference prior joint legal
          moved (none, none) earlierChoices actualPrefix produced
      have samePrevious : previous' = previous :=
        Option.some.inj (previousReplay'.symm.trans previousReplay)
      rw [samePrevious] at priorEq
      have previousKept : TracePrefix previous.trace trace := by
        have priorKept : TracePrefix actualPrefix.prior.trace actualPrefix.trace := by
          rcases actualPrefix with ⟨state, prefixTrace⟩
          cases prefixTrace with
          | start => exact .refl
          | extend prefixTrace joint legal moved => exact .extend .refl joint legal moved
        rw [priorEq] at priorKept
        exact priorKept.trans actualKept
      have previousOriginal : TracePrefix prior referenceTrace :=
        (TracePrefix.extend (TracePrefix.refl (prefixTrace := prior)) joint legal moved).trans
          kept
      have earlierProduct := ih previous previousReplay previousRelated previousRestricted
        previousOriginal previousKept
      change (sourceReplayScriptProducts setup values implementation scale who
        ⟨after, prior.extend joint legal moved⟩ actualPrefix
          ((none, none) :: earlierChoices)).1
          = _
      rw [sourceReplayScriptProducts_extend, priorEq]
      dsimp only
      rw [sourceRawReplay, previousReplay, Option.bind_some] at produced
      dsimp only at produced
      cases before with
      | none =>
        dsimp only at produced
        have update := appendFold previous actualPrefix _ _ produced
        simp only [ite_self, Finset.prod_const_one, mul_one] at update
        simpa only [ReactiveApplication.actor, Option.bind_none] using
          earlierProduct.trans update.symm
      | some before =>
        cases acting : before.actor with
        | none =>
          simp only [acting] at produced
          cases previousState : previous.state with
          | none => simp only [previousState] at produced; cases produced
          | some actualBefore =>
            simp only [previousState] at produced
            cases after with
            | none => dsimp only at produced; cases produced
            | some ending =>
              dsimp only at produced
              have update := appendFold previous actualPrefix _ _ produced
              simp only [ite_self, Finset.prod_const_one, mul_one] at update
              simpa only [ReactiveApplication.actor, Option.bind_some, acting, mul_one] using
                earlierProduct.trans update.symm
        | some responder =>
          have focal : responder = who := by
            rcases quiet with impossible | same
            · simp only [ReactiveApplication.actor, Option.bind_some, acting] at impossible
              cases impossible
            · simpa only [ReactiveApplication.actor, Option.bind_some, acting,
                Option.some.injEq] using same
          subst responder
          simp only [acting, ite_true] at produced
          cases previousState : previous.state with
          | none => simp only [previousState] at produced; cases produced
          | some actualBefore =>
            simp only [previousState] at produced
            obtain ⟨action, _selected, appended⟩ := Option.bind_eq_some_iff.mp produced
            have update := appendFold previous actualPrefix _ _ appended
            have quietUpdate : folded actualPrefix = folded previous := by
              calc
                _ = folded previous * _ := update
                _ = folded previous * 1 := by
                  apply congrArg (folded previous * ·)
                  apply Finset.prod_eq_one
                  intro owner _
                  by_cases same : owner = who <;>
                    simp only [same, ite_true, ite_false]
                _ = folded previous := mul_one _
            simpa only [ReactiveApplication.actor, Option.bind_some, acting, ite_true] using
              earlierProduct.trans quietUpdate.symm
    | @foreign before after prior joint legal moved earlierChoices earlierMass owner
        different acting actualBefore actualPrior actualReplay prefixRelated
        prefixRestricted kernel atoms _description choice chosen earlier ih =>
      intro actualPrefix produced nextRelated nextRestricted kept actualKept
      obtain ⟨_tag, response, responseEq, proper, _form⟩ := atoms choice chosen
      have previousOriginal : TracePrefix prior referenceTrace :=
        (TracePrefix.extend (TracePrefix.refl (prefixTrace := prior)) joint legal moved).trans
          kept
      obtain ⟨previous, previousReplay, priorEq⟩ := sourceRawReplay_step_prior setup
        implementation who ⟨some targetCurrent, targetTrace⟩ reference prior joint legal moved
          choice earlierChoices actualPrefix produced
      have samePrevious : previous = (⟨some actualBefore, actualPrior⟩ :
          (nativeProtocol).History) :=
        Option.some.inj (previousReplay.symm.trans actualReplay)
      rw [samePrevious] at priorEq
      have actualPriorKept : TracePrefix actualPrior actualPrefix.trace := by
        have priorKept : TracePrefix actualPrefix.prior.trace actualPrefix.trace := by
          rcases actualPrefix with ⟨state, prefixTrace⟩
          cases prefixTrace with
          | start => exact .refl
          | extend prefixTrace joint legal moved => exact .extend .refl joint legal moved
        rw [priorEq] at priorKept
        exact priorKept
      have earlierProduct := ih ⟨some actualBefore, actualPrior⟩ actualReplay prefixRelated
        prefixRestricted previousOriginal (actualPriorKept.trans actualKept)
      rw [sourceRawReplay, actualReplay, Option.bind_some] at produced
      dsimp only at produced
      rw [acting] at produced
      dsimp only at produced
      rw [ite_eq_right different, responseEq, Option.bind_some] at produced
      have actualState := (sourceReplayAppend_prior_state setup implementation
        ⟨some actualBefore, actualPrior⟩ actualPrefix _ _ produced).2
      have update := appendFold ⟨some actualBefore, actualPrior⟩ actualPrefix _ _ produced
      have single : (∏ other, if other = who then (1 : ℝ≥0∞) else
          match (if other = owner then some response.val else none) with
          | none => 1
          | some action => lostAt other (model.infoOf other actualPrior, action)) =
            lostAt owner (model.infoOf owner actualPrior, response.val) := by
        have oneRow : (∏ other, if other = who then (1 : ℝ≥0∞) else
            match (if other = owner then some response.val else none) with
            | none => 1
            | some action => lostAt other (model.infoOf other actualPrior, action)) =
              (if owner = who then 1 else
                lostAt owner (model.infoOf owner actualPrior, response.val)) := by
          trans (if owner = who then 1 else
            match (if owner = owner then some response.val else none) with
            | none => 1
            | some action => lostAt owner (model.infoOf owner actualPrior, action))
          · apply Finset.prod_eq_single owner
            · intro other _ differentOwner
              by_cases focal : other = who <;>
                simp only [focal, differentOwner, ite_true, ite_false]
            · intro impossible
              exact (impossible (Finset.mem_univ owner)).elim
          · simp only [ite_true]
        exact oneRow.trans (ite_eq_right different)
      have singleUpdate := update.trans
        (congrArg (folded ⟨some actualBefore, actualPrior⟩ * ·) single)
      change (sourceReplayScriptProducts setup values implementation scale who
        ⟨some after, prior.extend joint legal moved⟩ actualPrefix
          (choice :: earlierChoices)).1
          = _
      rw [sourceReplayScriptProducts_extend, priorEq]
      simp only [ReactiveApplication.actor, Option.bind_some, acting, ite_eq_right different]
      rw [earlierProduct, singleUpdate]
      apply congrArg (folded ⟨some actualBefore, actualPrior⟩ * ·)
      have actualActing : actualBefore.actor = some owner := prefixRelated.2.1.trans acting
      obtain ⟨originalAction, originalSelected⟩ : ∃ action, joint owner = some action := by
        cases selected : joint owner with
        | none =>
          have impossible := selected ▸ legal.2 owner
          exact (impossible acting).elim
        | some action => exact ⟨action, rfl⟩
      simp only [originalSelected, Option.getD_some] at atoms
      have originalState : after = ⟨before.remaining, none,
          before.execution.respond nativeApplication owner originalAction⟩ := by
        have reached := moved
        change some after ∈ ((nativeApplication).transition nativeInitial
          implementation.horizon implementation.scheduler
            (some before) joint).support at reached
        simpa only [ReactiveApplication.transition, acting, originalSelected,
          Option.getD_some, PMF.mem_support_pure_iff, Option.some.injEq] using reached
      have sameBefore := (RawReplayState.mechanicalProjection setup implementation who
        ⟨some targetCurrent, targetTrace⟩ reference
          (rawReplayLost setup implementation earlierChoices) ⟨some before, prior⟩
            ⟨some actualBefore, actualPrior⟩ prefixRelated).symm
      have sameAfter := (RawReplayState.mechanicalProjection setup implementation who
        ⟨some targetCurrent, targetTrace⟩ reference
          (rawReplayLost setup implementation (choice :: earlierChoices))
            ⟨some after, prior.extend joint legal moved⟩ actualPrefix nextRelated).symm
      change mechanicalProjection setup implementation who (some after) = _ at sameAfter
      rw [actualState, originalState] at sameAfter
      have packets := mechanicalProjection_response_packet setup implementation who owner
        before actualBefore prior actualPrior originalAction response.val sameBefore sameAfter
      have sameCall : originalAction.transmission.map (fun material => material.call.packet) =
          response.val.transmission.map (fun material => material.call.packet) := by
        have calls := congrArg (Option.map (fun signed :
            CommitAttemptPacket (serviceGraph setup .concurrent) =>
              signed.packet.call)) packets
        have localCall (execution : (nativeApplication).Execution)
            (material : WitnessedSubmission (serviceGraph setup .concurrent)) :
            (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
              (execution.recall owner) (execution.observe nativeApplication owner)
                material).payload.packet.call = material.call.packet :=
          PhaseCount.maskPacket_call _ _
        simpa only [Option.map_map, Function.comp_def, localCall] using calls
      rw [originalSelected, Option.getD_some]
      rw [sourceReplay_lost_draw_at_actual_callback setup values implementation scale owner
        actualBefore.execution ⟨some targetCurrent, targetTrace⟩ reference originalAction
          response.val kernel atoms choice chosen responseEq sameCall]
      have nativeInformation : model.infoOf owner actualPrior =
          some (actualBefore.execution.recall owner,
            actualBefore.execution.observe nativeApplication owner) := by
        change ((nativeMenu).signals nativeInitial implementation.horizon
          implementation.scheduler).infoOf owner actualPrior = _
        simpa only [ReactiveApplication.observe, actualActing, ite_true] using
          (nativeMenu).info nativeInitial implementation.horizon
            implementation.scheduler owner actualPrior
      rw [nativeInformation]
      cases sent : response.val.transmission with
      | none => simp only [sourceReplayBindingDrawAtom, sent, lostAt, ite_self]
      | some material =>
        cases packet : material.call.packet with
        | opening => simp only [sourceReplayBindingDrawAtom, sent, packet, lostAt, ite_self]
        | malformed => simp only [sourceReplayBindingDrawAtom, sent, packet, lostAt, ite_self]
        | commitment named handle =>
          have activeTrace : (nativeProtocol).Trace
              (some ⟨actualBefore.remaining, some owner, actualBefore.execution⟩) := by
            have state : actualBefore =
                ⟨actualBefore.remaining, some owner, actualBefore.execution⟩ := by
              cases actualBefore
              cases actualActing
              rfl
            exact state ▸ actualPrior
          obtain ⟨ty, shape, _key, _serial, _drawn, _handle, _request, _query,
            _prepared, _base, _response⟩ := sourceReplay_proper_callback_atom setup values
              implementation operational fullValues ⟨nativeBad, scale, scale, scale⟩
                scalePositive scaleBelow scalePositive nativeBadPositive nativeBadBelow
                  actualBefore.remaining owner actualBefore.execution activeTrace response
                    proper material sent named handle packet choice.1
          obtain ⟨emitted, recallEq⟩ := (nativeApplication).respond_recall_entry
            actualBefore.execution owner response.val
          let record : (nativeApplication).PlayerEntry :=
            ⟨actualBefore.execution.observe nativeApplication owner, response.val, emitted⟩
          have recordMember : record ∈ control.execution.recall owner := by
            have growth := (nativeApplication).reaches_recall_prefix nativeInitial
              implementation.horizon implementation.scheduler
                ((nativeMenu).reaches_raw nativeInitial implementation.horizon
                  implementation.scheduler actualKept.reachesWithin)
                    _ control actualState rfl owner
            apply growth.subset
            rw [recallEq]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          obtain ⟨message, actualEmitted, _sender, actualPacket⟩ :=
            PhaseCount.recalled_submission_emitted implementation.runtime implementation.leaks
              nativeInitial implementation.horizon implementation.scheduler rawTrace owner
                record recordMember material sent
          have call : message.payload.packet.call = .commitment named handle :=
            actualPacket.trans packet
          have tagged := taggedRegistration owner different record recordMember material sent
            message actualEmitted named ty shape handle call packet actualBefore
              originalAction
              kernel atoms choice chosen sameCall earlierChoices nextRestricted
          obtain ⟨_serial, _opening, _evidence, _handle, _sender, _action, _fresh,
            namespaceEq, _meaning⟩ := sourceReplay_recorded_binding_registration setup
              implementation control trace owner record recordMember message actualEmitted
                named
                ty shape handle call
          change actualBefore.execution.application.attempt = message.payload.attempt
            at namespaceEq
          rw [← namespaceEq] at tagged
          simp only [lostAt, sent, packet]
          rw [tagged]
          let historical : Prop :=
            actualBefore.execution.application.attempt ≠
                control.execution.application.attempt ∧
              ¬ PhaseService.BindingAccepted implementation.runtime implementation.leaks
                ⟨actualBefore.execution.application.attempt, named⟩ owner control.execution
          let draw := sourceReplayBindingDrawAtom setup values implementation owner
            (actualBefore.execution.recall owner)
              (actualBefore.execution.observe nativeApplication owner) response.val
          change (if decide historical = true then draw else 1) =
            (if historical then draw else 1)
          simp only [decide_eq_true_eq]
  have scriptFold := foldScript (law.atoms script member) ⟨some control, trace⟩ replayed
    related (law.restricted script member) .refl .refl
  rw [scriptFold]
  unfold sourceReplayHistoricalDrawProducts folded
  simp only [Prod.snd_prod]
  apply Finset.prod_congr rfl
  intro owner _
  by_cases focal : owner = who
  · simp only [focal, ite_true]
  · rw [ite_eq_right focal, ite_eq_right focal,
      HiddenSwap.phase_trace_ownPlay implementation.bounds nativeInitial
        implementation.horizon implementation.scheduler control trace owner,
          recallWord owner (lostAt owner)]
    have secondProduct (entries : List (ℝ≥0∞ × ℝ≥0∞)) :
        entries.prod.2 = (entries.map Prod.snd).prod := by
      induction entries with
      | nil => rfl
      | cons entry rest ih =>
        simp only [List.prod_cons, Prod.snd_mul, List.map_cons, ih]
    rw [secondProduct, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro indexed member
    have recordMember : indexed.1 ∈ control.execution.recall owner :=
      List.fst_mem_of_mem_zipIdx member
    dsimp only [Function.comp_def]
    cases sent : indexed.1.action.transmission with
    | none =>
      cases emitted : indexed.1.emitted with
      | none => simp only [lostAt, sent]
      | some message =>
        cases call : message.payload.packet.call <;>
          simp [lostAt, sent, call, sourceReplayBindingDrawAtom]
    | some material =>
      obtain ⟨message, emitted, _sender, packet⟩ := PhaseCount.recalled_submission_emitted
        implementation.runtime implementation.leaks nativeInitial implementation.horizon
          implementation.scheduler rawTrace owner indexed.1 recordMember material sent
      have namespaceEq := phase_recalled_emission_attempt implementation.runtime
        implementation.leaks nativeInitial implementation.horizon implementation.scheduler
          rawTrace owner indexed.1 recordMember message emitted
      rw [emitted]
      dsimp only
      rw [packet]
      cases call : material.call.packet with
      | opening => simp [lostAt, sent, call, sourceReplayBindingDrawAtom]
      | malformed => simp [lostAt, sent, call, sourceReplayBindingDrawAtom]
      | commitment named handle =>
        simp only [lostAt, sent, call, sourceReplayBindingDrawAtom]
        rw [namespaceEq]
        by_cases current : indexed.1.beforeView.application.2.attempt =
            control.execution.application.attempt
        · simp [current]
        · by_cases accepted : PhaseService.BindingAccepted implementation.runtime
              implementation.leaks ⟨indexed.1.beforeView.application.2.attempt, named⟩
                owner control.execution
          · simp [current, accepted]
          · simp [current, accepted]

private theorem sourceReplay_callback_alias_product
    (who : Player)
    (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (scale : Set.Icc (0 : ℝ) 1)
    (nativeBad : Set.Icc (0 : ℝ) 1)
    (law : SourceRawReplayLaw (setup := setup) (values := values)
          (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩ reference
            ⟨some reference, referenceTrace⟩)
    (script : List (RawReplayChoice setup implementation))
    (member : script ∈ law.choices.support)
    (actual : ((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).InformationHistory who
            (((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).infoOf who referenceTrace))
    (replayed : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
          reference ⟨some reference, referenceTrace⟩ script = some actual.val) :
    ENNReal.ofReal
        (sourceReplayResponseProducts setup values implementation ⟨nativeBad, scale, scale, scale⟩
          who actual.val.trace).2.2 =
      (sourceReplayScriptProducts setup values implementation scale who
        ⟨some reference, referenceTrace⟩ actual.val script).2 := by
  classical
  have aliasFinite (owner : Player) (execution : (nativeApplication).Execution)
      (choice : RawReplayChoice setup implementation) :
      sourceReplayAliasAtom setup implementation scale owner execution choice ≠ ⊤ := by
    unfold sourceReplayAliasAtom
    split
    · exact ENNReal.zero_ne_top
    · split_ifs
      · exact PMF.apply_ne_top _ _
      · exact ENNReal.zero_ne_top
  have appendAlias (previous actual : (nativeProtocol).History)
      (next : (nativeProtocol).State) (joint : Player → Option (nativeApplication).Action)
      (appended : sourceReplayAppend setup implementation previous next joint = some actual) :
      ENNReal.ofReal
        (sourceReplayResponseProducts setup values implementation ⟨nativeBad, scale, scale, scale⟩
          who actual.trace).2.2 =
        ENNReal.ofReal
          (sourceReplayResponseProducts setup values implementation
            ⟨nativeBad, scale, scale, scale⟩ who previous.trace).2.2 *
        match previous.state with
        | none => 1
        | some before => match before.actor with
          | none => 1
          | some owner => if owner = who then 1 else match joint owner with
            | none => 0
            | some action => sourceReplayAliasAtom setup implementation scale owner
                before.execution (none, some action) := by
    rcases previous with ⟨previousState, prior⟩
    unfold sourceReplayAppend at appended
    split at appended
    · split at appended
      · cases Option.some.inj appended
        have nonnegative := (sourceReplay_response_products_nonnegative setup values
          implementation ⟨nativeBad, scale, scale, scale⟩ who prior).2
        change ENNReal.ofReal
          ((sourceReplayResponseProducts setup values implementation
            ⟨nativeBad, scale, scale, scale⟩ who prior).2.2 * _) = _
        rw [ENNReal.ofReal_mul nonnegative]
        apply congrArg (ENNReal.ofReal _ * ·)
        cases previousState with
        | none => simp only [ENNReal.ofReal_one]
        | some before =>
          cases actor : before.actor with
          | none => simp only [actor, ENNReal.ofReal_one]
          | some owner =>
            by_cases focal : owner = who
            · simp only [actor, focal, ite_true, ENNReal.ofReal_one]
            · cases selected : joint owner with
              | none => simp only [actor, focal, ite_false, selected,
                  ENNReal.ofReal_zero]
              | some action =>
                simp only [actor, focal, ite_false, selected]
                exact ENNReal.ofReal_toReal (aliasFinite owner before.execution
                  (none, some action))
      · cases appended
    · cases appended
  have foldAliases {original : (nativeProtocol).History}
      {choices : List (RawReplayChoice setup implementation)} {mass : ℝ≥0∞}
      (supportedScript : SourceReplayScriptMass (setup := setup) (values := values)
        (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩ reference
          original choices mass) :
      ∀ actualPrefix : (nativeProtocol).History,
        sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
            original choices = some actualPrefix →
        ENNReal.ofReal
          (sourceReplayResponseProducts setup values implementation
            ⟨nativeBad, scale, scale, scale⟩ who actualPrefix.trace).2.2 =
          (sourceReplayScriptProducts setup values implementation scale who original
            actualPrefix choices).2 := by
    induction supportedScript with
    | start =>
      intro actualPrefix produced
      simp only [sourceRawReplay] at produced
      cases Option.some.inj produced
      change ENNReal.ofReal (1 : ℝ) = 1
      exact ENNReal.ofReal_one
    | @deterministic before after prior joint legal moved earlierChoices earlierMass quiet
        previous previousReplay previousRelated _previousRestricted earlier ih =>
      intro actualPrefix produced
      obtain ⟨previous', previousReplay', priorEq⟩ := sourceRawReplay_step_prior setup
        implementation who ⟨some targetCurrent, targetTrace⟩ reference prior joint legal moved
          (none, none) earlierChoices actualPrefix produced
      have samePrevious : previous' = previous :=
        Option.some.inj (previousReplay'.symm.trans previousReplay)
      rw [samePrevious] at priorEq
      have earlierProduct := ih previous previousReplay
      change _ = (sourceReplayScriptProducts setup values implementation scale who
        ⟨after, prior.extend joint legal moved⟩ actualPrefix ((none, none) :: earlierChoices)).2
      rw [sourceReplayScriptProducts_extend, priorEq]
      dsimp only
      rw [sourceRawReplay, previousReplay, Option.bind_some] at produced
      cases before with
      | none =>
        have previousState : previous.state = none := by
          cases state : previous.state with
          | none => rfl
          | some before =>
            simp only [RawReplayState, state] at previousRelated
        dsimp only at produced
        have update := appendAlias previous actualPrefix _ _ produced
        simp only [previousState, mul_one] at update
        simpa only [ReactiveApplication.actor, Option.bind_none] using
          update.trans earlierProduct
      | some before =>
        cases previousState : previous.state with
        | none => simp only [RawReplayState, previousState] at previousRelated
        | some actualBefore =>
          simp only [RawReplayState, previousState] at previousRelated
          have actualActor : actualBefore.actor = before.actor := previousRelated.2.1
          cases acting : before.actor with
          | none =>
            simp only [acting, previousState] at produced
            cases after with
            | none => cases produced
            | some ending =>
              have update := appendAlias previous actualPrefix _ _ produced
              simp only [previousState, actualActor, acting, mul_one] at update
              simpa only [ReactiveApplication.actor, Option.bind_some, acting] using
                update.trans earlierProduct
          | some owner =>
            have focal : owner = who := by
              rcases quiet with impossible | same
              · simp only [ReactiveApplication.actor, Option.bind_some, acting] at impossible
                cases impossible
              · simpa only [ReactiveApplication.actor, Option.bind_some, acting,
                  Option.some.injEq] using same
            subst owner
            simp only [acting, previousState, ite_true] at produced
            obtain ⟨action, _selected, appended⟩ := Option.bind_eq_some_iff.mp produced
            have update := appendAlias previous actualPrefix _ _ appended
            simp only [previousState, actualActor, acting, ite_true, mul_one] at update
            simpa only [ReactiveApplication.actor, Option.bind_some, acting, ite_true] using
              update.trans earlierProduct
    | @foreign before after prior joint legal moved earlierChoices earlierMass owner different
        acting previous previousTrace previousReplay prefixRelated _prefixRestricted kernel atoms
        _description choice chosen earlier ih =>
      intro actualPrefix produced
      obtain ⟨_tag, response, responseEq, _proper, _form⟩ := atoms choice chosen
      have earlierProduct := ih ⟨some previous, previousTrace⟩ previousReplay
      obtain ⟨previous', previousReplay', priorEq⟩ := sourceRawReplay_step_prior setup
        implementation who ⟨some targetCurrent, targetTrace⟩ reference prior joint legal moved
          choice earlierChoices actualPrefix produced
      have samePrevious : previous' = (⟨some previous, previousTrace⟩ :
          (nativeProtocol).History) :=
        Option.some.inj (previousReplay'.symm.trans previousReplay)
      rw [samePrevious] at priorEq
      rw [sourceRawReplay, previousReplay, Option.bind_some] at produced
      dsimp only at produced
      rw [acting] at produced
      dsimp only at produced
      rw [ite_eq_right different, responseEq, Option.bind_some] at produced
      have update := appendAlias ⟨some previous, previousTrace⟩ actualPrefix _ _ produced
      have actualActor : previous.actor = some owner := prefixRelated.2.1.trans acting
      simp only [actualActor, different, ite_false, ite_true] at update
      change _ = (sourceReplayScriptProducts setup values implementation scale who
        ⟨some after, prior.extend joint legal moved⟩ actualPrefix (choice :: earlierChoices)).2
      rw [sourceReplayScriptProducts_extend, priorEq]
      simp only [ReactiveApplication.actor, Option.bind_some, acting, ite_eq_right different]
      rw [update, earlierProduct]
      apply congrArg (_ * ·)
      have pair : choice = (choice.1, some response.val) := Prod.ext rfl responseEq
      rw [pair]
      exact (sourceReplay_alias_atom_tag setup implementation scale owner previous.execution
        choice.1 response.val response.property).symm
  exact foldAliases (law.atoms script member) actual.val replayed

/-- The literal foreign queried draws split into the actual canonical historical
rows, the current issued cylinder, and this same script's lost coordinates.
Aliases retain every callback occurrence, including WAIT. -/
theorem sourceRawReplay_foreign_draw_products
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (who : Player) (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (acting : reference.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who
      (reference.execution.recall who)
      (reference.execution.observe nativeApplication who) event payload)
    (good : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner ⟨some reference, referenceTrace⟩)
    (entry : NativeBindingEntry setup implementation operational reference referenceTrace
      who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who
        (entry.canonicalCut setup values implementation operational fullValues reference
          referenceTrace who acting event payload clean good).trace)
    (sourceGood : setup.proposalRecoveryForeignGood who g)
    (sourceChoice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, sourceChoice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (supported : (⟨some targetCurrent, targetTrace⟩ :
      setup.proposalRecoveryProtocol.History) ∈
        (sourceForcedBlock setup values who g sourceChoice).support)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        nativeInitial implementation.horizon implementation.scheduler values
          ⟨nativeBad, scale, scale, scale⟩)
    (site : (nativeModel).InformationSite who)
    (referenceInformation : (nativeModel).infoOf who referenceTrace = site.1)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site
      (reference.execution.recall who) (reference.execution.observe nativeApplication who)
        event payload clean.binding)
    (gInfo : setup.proposalRecoveryModel.infoOf who g.trace = source.site.1)
    (value : L.Val payload)
    (encoded : sourceChoice = gInfo.symm ▸ source.encode value)
    (law : SourceRawReplayLaw (setup := setup) (values := values)
      (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩ reference
        ⟨some reference, referenceTrace⟩)
    (script : List (RawReplayChoice setup implementation))
    (member : script ∈ law.choices.support)
    (actual : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationHistory who
        (((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).infoOf who referenceTrace))
    (replayed : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
      reference ⟨some reference, referenceTrace⟩ script = some actual.val)
    (nativePositive : (nativeModel).historyReachWeight nativeProfile actual.val ≠ 0)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (tapePositive : prefixTapeLaw setup implementation actual.val tape ≠ 0)
    (actualGood : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner actual.val)
    (actualAlive : actual.val.state.elim True (fun control =>
      who ∉ control.execution.application.current.excluded))
    (admitted : bindingAdmissionBit setup implementation who event actual.val tape = true)
    (q : setup.proposalRecoveryProtocol.History)
    (qKept : TracePrefix q.trace g.trace)
    (qDepth : q.trace.length =
      (canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩).trace.length)
    (sameKey : setup.proposalRecoveryClosedKey who
        (canonicalSource setup implementation operational actual.val) =
      setup.proposalRecoveryClosedKey who q) :
    ENNReal.ofReal
        (sourceReplayResponseProducts setup values implementation ⟨nativeBad, scale, scale, scale⟩
          who actual.val.trace).2.1 =
      (setup.proposalRecoveryForeignProducts values scale sourceBad scale who
          (canonicalSource setup implementation operational actual.val).trace).2.1 *
        sourceReplayCurrentIssuedProduct setup values implementation who actual.val *
          (sourceReplayScriptProducts setup values implementation scale who
            ⟨some reference, referenceTrace⟩ actual.val script).1 ∧
    ENNReal.ofReal
        (sourceReplayResponseProducts setup values implementation ⟨nativeBad, scale, scale, scale⟩
          who actual.val.trace).2.2 =
      (sourceReplayScriptProducts setup values implementation scale who
        ⟨some reference, referenceTrace⟩ actual.val script).2 := by
  classical
  obtain ⟨word, annotation⟩ := sourceRawReplay_forward_annotation setup values implementation
    operational fullValues who reference referenceTrace acting
      event payload clean good entry g sameInfo sourceGood sourceChoice properChoice targetCurrent
        targetTrace supported scale sourceBad nativeBad scalePositive scaleBelow sourceBadPositive
          sourceBadBelow nativeBadPositive nativeBadBelow sourceProfile sourcePrescribed
            nativeProfile
            nativePrescribed site referenceInformation source gInfo value encoded law script member
              actual replayed nativePositive tape tapePositive actualGood actualAlive admitted q
                  qKept
                qDepth sameKey
  obtain ⟨image, imageReplay, related, mechanical, imageGood⟩ := law.replayed script member
  have sameActual : image = actual.val := Option.some.inj (imageReplay.symm.trans replayed)
  cases sameActual
  constructor
  -- BEGIN HISTORICAL AND LOST DRAW PRODUCTS
  · rcases actual with ⟨⟨state, trace⟩, information⟩
    cases state with
    | none => simp only [bindingAdmissionBit, Bool.false_eq_true] at admitted
    | some control =>
      have registered := sourceReplay_registered_draw_product (setup := setup) (values := values)
        (implementation := implementation) (control := control) (trace := trace) (who := who)
        (scale := scale) (nativeBad := nativeBad)
      have historical := sourceReplay_historical_draw_product (setup := setup) (values := values)
        (implementation := implementation) (control := control) (trace := trace)
        (operational := operational) (fullValues := fullValues) (who := who)
        (reference := reference) (referenceTrace := referenceTrace) (acting := acting)
        (event := event) (payload := payload) (clean := clean) (g := g)
        (targetCurrent := targetCurrent) (targetTrace := targetTrace) (scale := scale)
        (sourceBad := sourceBad) (scalePositive := scalePositive) (scaleBelow := scaleBelow)
        (sourceBadPositive := sourceBadPositive) (sourceBadBelow := sourceBadBelow)
        (sourceProfile := sourceProfile) (sourcePrescribed := sourcePrescribed)
        (nativeProfile := nativeProfile) (value := value) (law := law) (script := script)
        (member := member) (replayed := replayed) (tape := tape) (actualGood := actualGood) (q := q)
        (word := word) (annotation := annotation) (related := related)
      have lost := sourceReplay_lost_draw_product (setup := setup) (values := values)
        (implementation := implementation) (control := control) (trace := trace)
        (operational := operational) (fullValues := fullValues) (who := who)
        (reference := reference) (referenceTrace := referenceTrace) (acting := acting)
        (event := event) (payload := payload) (clean := clean) (g := g)
        (targetCurrent := targetCurrent) (targetTrace := targetTrace) (scale := scale)
        (sourceBad := sourceBad) (nativeBad := nativeBad) (scalePositive := scalePositive)
        (scaleBelow := scaleBelow) (sourceBadPositive := sourceBadPositive)
        (sourceBadBelow := sourceBadBelow) (nativeBadPositive := nativeBadPositive)
        (nativeBadBelow := nativeBadBelow) (sourceProfile := sourceProfile)
        (sourcePrescribed := sourcePrescribed) (nativeProfile := nativeProfile) (value := value)
        (law := law) (script := script) (member := member) (replayed := replayed) (tape := tape)
        (q := q) (word := word) (annotation := annotation)
        (related := related)
      rw [registered, sourceReplay_registered_draw_partition, historical, lost]
  -- END HISTORICAL AND LOST DRAW PRODUCTS
  -- BEGIN CALLBACK ALIAS PRODUCT
  · exact sourceReplay_callback_alias_product (setup := setup) (values := values)
      (implementation := implementation) (who := who) (reference := reference)
      (referenceTrace := referenceTrace) (targetCurrent := targetCurrent)
      (targetTrace := targetTrace) (scale := scale) (nativeBad := nativeBad) (law := law)
      (script := script) (member := member) (actual := actual) (replayed := replayed)
  -- END CALLBACK ALIAS PRODUCT

/-- The finite mechanical path has no infinite probability atom. -/
private theorem sourceReplay_mechanical_path_finite
    (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    mechanicalPathAtom setup implementation rates who tape trace ≠ ⊤ := by
  have packetFinite (execution : (nativeApplication).Execution) (owner : Player)
      (action : (nativeApplication).Action) :
      foreignMechanicalAtom setup implementation rates execution owner action ≠ ⊤ := by
    unfold foreignMechanicalAtom
    apply ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    split
    · exact ENNReal.one_ne_top
    · split <;> first | exact ENNReal.ofReal_ne_top | exact ENNReal.one_ne_top
  have stepFinite (before after : (nativeProtocol).State)
      (joint : Player → Option (nativeApplication).Action) :
      mechanicalStepAtom setup implementation rates who tape before after joint ≠ ⊤ := by
    cases before with
    | none => exact ENNReal.one_ne_top
    | some control =>
      cases acting : control.actor with
      | some owner =>
        by_cases focal : owner = who
        · simpa only [mechanicalStepAtom, acting, focal, ↓reduceIte] using ENNReal.one_ne_top
        · cases selected : joint owner with
          | none => simpa only [mechanicalStepAtom, acting, focal, ↓reduceIte, selected] using
              ENNReal.zero_ne_top
          | some action =>
            simpa only [mechanicalStepAtom, acting, focal, ↓reduceIte, selected] using
              packetFinite control.execution owner action
      | none =>
        by_cases stopped : control.remaining = 0
        · simpa only [mechanicalStepAtom, acting, stopped, ↓reduceIte] using ENNReal.one_ne_top
        · cases after with
          | none => simpa only [mechanicalStepAtom, acting, stopped, ↓reduceIte] using
              ENNReal.zero_ne_top
          | some later =>
            cases recorded : later.execution.environmentRecall.getLast? with
            | none => simpa only [mechanicalStepAtom, acting, stopped, ↓reduceIte, recorded] using
                ENNReal.zero_ne_top
            | some command =>
              simpa only [mechanicalStepAtom, acting, stopped, ↓reduceIte, recorded] using
                (PMF.apply_ne_top (ReservedEpoch.family implementation.runtime
                  implementation.leaks (ReservedEpoch.packetCapacity implementation.runtime) tape
                    control.execution.environmentRecall
                      (control.execution.observeEnvironment nativeApplication)) command.command)
  induction trace with
  | start => exact ENNReal.one_ne_top
  | extend prior joint legal moved ih =>
    exact ENNReal.mul_ne_top ih (stepFinite _ _ joint)

/-- The native and tape atom uses the selected canonical history's own Nature
and historical draw factors. The normalized script mass is retained once. -/
theorem sourceRawReplay_native_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (who : Player) (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (acting : reference.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who
      (reference.execution.recall who)
      (reference.execution.observe nativeApplication who) event payload)
    (good : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner ⟨some reference, referenceTrace⟩)
    (entry : NativeBindingEntry setup implementation operational reference referenceTrace
      who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who
        (entry.canonicalCut setup values implementation operational fullValues reference
          referenceTrace who acting event payload clean good).trace)
    (sourceGood : setup.proposalRecoveryForeignGood who g)
    (sourceChoice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, sourceChoice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (supported : (⟨some targetCurrent, targetTrace⟩ :
      setup.proposalRecoveryProtocol.History) ∈
        (sourceForcedBlock setup values who g sourceChoice).support)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        nativeInitial implementation.horizon implementation.scheduler values
          ⟨nativeBad, scale, scale, scale⟩)
    (site : (nativeModel).InformationSite who)
    (referenceInformation : (nativeModel).infoOf who referenceTrace = site.1)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site
      (reference.execution.recall who) (reference.execution.observe nativeApplication who)
        event payload clean.binding)
    (gInfo : setup.proposalRecoveryModel.infoOf who g.trace = source.site.1)
    (value : L.Val payload)
    (encoded : sourceChoice = gInfo.symm ▸ source.encode value)
    (law : SourceRawReplayLaw (setup := setup) (values := values)
      (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩ reference
        ⟨some reference, referenceTrace⟩)
    (script : List (RawReplayChoice setup implementation))
    (member : script ∈ law.choices.support)
    (actual : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationHistory who
        (((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).infoOf who referenceTrace))
    (replayed : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
      reference ⟨some reference, referenceTrace⟩ script = some actual.val)
    (nativePositive : (nativeModel).historyReachWeight nativeProfile actual.val ≠ 0)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (tapePositive : prefixTapeLaw setup implementation actual.val tape ≠ 0)
    (actualGood : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner actual.val)
    (actualAlive : actual.val.state.elim True (fun control =>
      who ∉ control.execution.application.current.excluded))
    (admitted : bindingAdmissionBit setup implementation who event actual.val tape = true)
    (q : setup.proposalRecoveryProtocol.History)
    (qKept : TracePrefix q.trace g.trace)
    (qDepth : q.trace.length =
      (canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩).trace.length)
    (sameKey : setup.proposalRecoveryClosedKey who
        (canonicalSource setup implementation operational actual.val) =
      setup.proposalRecoveryClosedKey who q) :
    ((nativeModel).historyReachWeight nativeProfile actual.val).toReal *
        (prefixTapeLaw setup implementation actual.val tape).toReal =
      (implementation.prior tape).toReal *
        (canonicalSource setup implementation operational actual.val).trace.transitionMass *
        (mechanicalPathAtom setup implementation ⟨nativeBad, scale, scale, scale⟩ who
          tape actual.val.trace).toReal *
        (nativeModel).ownPlayReachProbability (nativeProfile who)
          ((nativeModel).ownPlay who actual.val.trace) *
        ((setup.proposalRecoveryForeignProducts values scale sourceBad scale who
              (canonicalSource setup implementation operational actual.val).trace).2.1 *
          sourceReplayCurrentIssuedProduct setup values implementation who actual.val *
            law.choices script).toReal := by
  classical
  obtain ⟨draws, aliases⟩ := sourceRawReplay_foreign_draw_products setup values implementation
    operational fullValues who reference referenceTrace acting
      event payload clean good entry g sameInfo sourceGood sourceChoice properChoice targetCurrent
        targetTrace supported scale sourceBad nativeBad scalePositive scaleBelow sourceBadPositive
          sourceBadBelow nativeBadPositive nativeBadBelow sourceProfile sourcePrescribed
            nativeProfile
            nativePrescribed site referenceInformation source gInfo value encoded law script member
              actual replayed nativePositive tape tapePositive actualGood actualAlive admitted q
                  qKept
                qDepth sameKey
  have scriptAtom := sourceReplayScriptMass_factor setup values implementation scale who
    ⟨some targetCurrent, targetTrace⟩ reference ⟨some reference, referenceTrace⟩ script
      (law.choices script) (law.atoms script member) actual.val replayed
  rcases actual with ⟨⟨state, trace⟩, information⟩
  cases state with
  | none => simp only [bindingAdmissionBit, Bool.false_eq_true] at admitted
  | some control =>
    have atom := sourceReplay_prescribed_response_atom setup values implementation operational
      fullValues ⟨nativeBad, scale, scale, scale⟩ scalePositive scaleBelow scalePositive
        nativeBadPositive nativeBadBelow who tape control trace actualGood
    rw [← nativePrescribed] at atom
    rw [atom]
    have nonnegative := sourceReplay_response_products_nonnegative setup values implementation
      ⟨nativeBad, scale, scale, scale⟩ who trace
    have drawReal := congrArg ENNReal.toReal draws
    have aliasReal := congrArg ENNReal.toReal aliases
    rw [ENNReal.toReal_ofReal nonnegative.1] at drawReal
    rw [ENNReal.toReal_ofReal nonnegative.2] at aliasReal
    have product :
        (sourceReplayResponseProducts setup values implementation
              ⟨nativeBad, scale, scale, scale⟩ who trace).2.1 *
            (sourceReplayResponseProducts setup values implementation
              ⟨nativeBad, scale, scale, scale⟩ who trace).2.2 =
          ((setup.proposalRecoveryForeignProducts values scale sourceBad scale who
                (canonicalSource setup implementation operational
                  ⟨some control, trace⟩).trace).2.1 *
            sourceReplayCurrentIssuedProduct setup values implementation who
              ⟨some control, trace⟩ * law.choices script).toReal := by
      rw [scriptAtom, drawReal, aliasReal]
      simp only [ENNReal.toReal_mul]
      ring
    rw [← product]
    ring


/-- On a proper commitment row the foreign prescribed atom is its original
ordinary atom times the same literal class factor. Inactive rows contribute one. -/
private theorem sourceReplay_commit_opponents_calibration
    (scale sourceBad : Set.Icc (0 : ℝ) 1) (who : Player)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (after : setup.proposalRecoveryProtocol.State)
    (moved : after ∈ (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (proper : ∀ owner move, owner ≠ who → joint owner = some move →
      move.semantic.missing = false ∧ ¬ move.semantic.action.IsFailure) :
    let profile := setup.proposalRecoveryNormalizedTrembledProfile
      scale.val scale.property.1 scale.property.2
      sourceBad.val sourceBad.property.1 sourceBad.property.2
      scale.val scale.property.1 scale.property.2 values
    let row := setup.proposalRecoveryForeignRowFactors values scale sourceBad scale who
      ⟨some current, prior⟩ joint legal moved
    setup.proposalRecoveryModel.opponentsStepProb profile who prior ⟨joint, legal⟩ =
      row.1.toReal * setup.proposalRecoveryModel.opponentsStepProb
        (sourceUnflaggedStrategy setup values) who prior ⟨joint, legal⟩ := by
  classical
  intro profile row
  let zero : Set.Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
  let ordinaryRow := setup.proposalRecoveryForeignRowFactors values zero zero zero who
    ⟨some current, prior⟩ joint legal moved
  have prescribed := setup.proposalRecovery_foreign_row_opponents values scale sourceBad scale
    who ⟨some current, prior⟩ joint legal moved
  have ordinary := setup.proposalRecovery_foreign_row_opponents values zero zero zero
    who ⟨some current, prior⟩ joint legal moved
  change setup.proposalRecoveryModel.opponentsStepProb profile who prior ⟨joint, legal⟩ =
    row.1.toReal * row.2.1.toReal * row.2.2.toReal at prescribed
  change setup.proposalRecoveryModel.opponentsStepProb (sourceUnflaggedStrategy setup values)
      who prior ⟨joint, legal⟩ =
    ordinaryRow.1.toReal * ordinaryRow.2.1.toReal * ordinaryRow.2.2.toReal at ordinary
  have rows : row.2.1 = ordinaryRow.2.1 ∧ row.2.2 = 1 ∧
      ordinaryRow.1 = 1 ∧ ordinaryRow.2.2 = 1 := by
    cases acting : ProtocolState.actor setup.program current.point with
    | none => simp [row, ordinaryRow, Setup.proposalRecoveryForeignRowFactors, acting]
    | some owner =>
      by_cases focal : owner = who
      · simp [row, ordinaryRow, Setup.proposalRecoveryForeignRowFactors, acting, focal]
      · cases selected : joint owner with
        | none =>
          simp [row, ordinaryRow, Setup.proposalRecoveryForeignRowFactors, acting, focal, selected]
        | some move =>
          have sound := proper owner move focal selected
          cases action : move.semantic.action with
          | commit author name payload binding =>
            cases binding with
            | failure => exact (sound.2 (by rw [action]; rfl)).elim
            | success value =>
              simp [row, ordinaryRow, Setup.proposalRecoveryForeignRowFactors, acting,
                focal, selected, action, sound.1, zero]
          | reveal author name disclosed =>
            have allowed := setup.proposalRecoveryProtocol.legalOption_of_legal legal owner
            rw [selected] at allowed
            have notCommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal owner
              setup.program current.point move.semantic allowed.2.1
                ⟨author, name, disclosed, action⟩
            rw [committing] at notCommit
            cases notCommit
  rw [prescribed, ordinary, rows.1, rows.2.1, rows.2.2.1, rows.2.2.2,
    ENNReal.toReal_one, one_mul, mul_one, mul_one]

/-- Along an actual proper commitment prefix, changing from the prescribed
law to the ordinary law changes only the foreign class factors and the
focal player's new own records. Earlier records remain literal, even if
their ordinary mass is zero. -/
private theorem sourceReplay_commit_prefix_calibration
    (scale sourceBad : Set.Icc (0 : ℝ) 1) (who : Player)
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (prescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      profile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (first last : setup.proposalRecoveryProtocol.History)
    (kept : TracePrefix first.trace last.trace)
    (rows : ∀ (before : setup.proposalRecoveryProtocol.History)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
      (after : setup.proposalRecoveryProtocol.State)
      (moved : after ∈ (setup.proposalRecoveryProtocol.step before.state ⟨joint, legal⟩).support),
      TracePrefix first.trace before.trace →
      TracePrefix (before.trace.extend joint legal moved) last.trace →
      ∃ current, before.state = some current ∧
        ProtocolState.atCommit setup.program current.point = true ∧
        ∀ owner move, owner ≠ who → joint owner = some move →
          move.semantic.missing = false ∧ ¬ move.semantic.action.IsFailure) :
    ∃ records : List (setup.proposalRecoveryModel.InfoState who ×
        setup.proposalRecoveryProtocol.Action who),
      setup.proposalRecoveryModel.ownPlay who last.trace =
        records ++ setup.proposalRecoveryModel.ownPlay who first.trace ∧
      setup.proposalRecoveryModel.playerReachProbability profile who last.trace *
          (setup.proposalRecoveryForeignProducts values scale sourceBad scale who
            last.trace).1.toReal *
          (setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup values)
            (last.trace.length - first.trace.length) first last).toReal =
        setup.proposalRecoveryModel.playerReachProbability profile who first.trace *
          (setup.proposalRecoveryForeignProducts values scale sourceBad scale who
            first.trace).1.toReal *
          (setup.proposalRecoveryModel.runBehavioralFrom profile
            (last.trace.length - first.trace.length) first last).toReal *
          setup.proposalRecoveryModel.ownPlayReachProbability
            (sourceUnflaggedStrategy setup values who) records := by
  classical
  rcases first with ⟨firstState, firstTrace⟩
  rcases last with ⟨lastState, lastTrace⟩
  dsimp only at kept ⊢
  revert rows
  induction kept with
  | refl =>
    intro _rows
    refine ⟨[], by simp only [List.nil_append], ?_⟩
    simp only [Nat.sub_self, InformationModel.runBehavioralFrom,
      ExecutionProtocol.runRandomizedFor_zero, PMF.pure_apply_self, ENNReal.toReal_one,
      InformationModel.ownPlayReachProbability, mul_one]
  | @extend source target prior retained joint legal moved ih =>
    intro rows
    obtain ⟨records, recorded, calibrated⟩ := ih (by
      intro before earlier earlierLegal next reached firstKept lastKept
      exact rows before earlier earlierLegal next reached firstKept
        (.extend lastKept joint legal moved))
    obtain ⟨current, sourceEq, committing, proper⟩ :=
      rows ⟨source, prior⟩ joint legal target moved retained .refl
    cases sourceEq
    let ordinary := sourceUnflaggedStrategy setup values
    let newer := match joint who with
      | none => records
      | some action => (setup.proposalRecoveryModel.infoOf who prior, action) :: records
    have newOwn : setup.proposalRecoveryModel.ownPlayReachProbability (ordinary who) newer =
        setup.proposalRecoveryModel.ownPlayReachProbability (ordinary who) records *
          setup.proposalRecoveryModel.playerStepProb ordinary who prior ⟨joint, legal⟩ := by
      cases chosen : joint who with
      | none =>
        have inactive : ¬ setup.proposalRecoveryProtocol.active (some current) who := by
          have offered := setup.proposalRecoveryProtocol.legalOption_of_legal legal who
          simpa only [chosen, LegalOption] using offered
        let _ := setup.proposalRecoveryModel.subsingleton_choice_of_not_active prior inactive
        simp only [newer, chosen]
        unfold InformationModel.playerStepProb
        rw [eq_pure_of_subsingleton (ordinary who
          (setup.proposalRecoveryModel.infoOf who prior))
            (setup.proposalRecoveryModel.choicesOfLegal prior ⟨joint, legal⟩ who)]
        simp only [PMF.pure_apply_self, ENNReal.toReal_one, mul_one]
      | some action =>
        simp only [newer, chosen, InformationModel.ownPlayReachProbability]
        have atom := pmf_map_apply_of_injective
          (ordinary who (setup.proposalRecoveryModel.infoOf who prior)) Subtype.val_injective
            (setup.proposalRecoveryModel.choicesOfLegal prior ⟨joint, legal⟩ who)
        change ((ordinary who (setup.proposalRecoveryModel.infoOf who prior)).map Subtype.val)
          (joint who) = _ at atom
        rw [chosen] at atom
        rw [atom]
        exact mul_comm _ _
    have extendAtom (policies : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner) :
        (setup.proposalRecoveryModel.runBehavioralFrom policies
          ((prior.extend joint legal moved).length - firstTrace.length)
          ⟨firstState, firstTrace⟩ ⟨target, prior.extend joint legal moved⟩).toReal =
        (setup.proposalRecoveryModel.runBehavioralFrom policies
          (prior.length - firstTrace.length) ⟨firstState, firstTrace⟩
            ⟨some current, prior⟩).toReal *
          (setup.proposalRecoveryModel.playerStepProb policies who prior ⟨joint, legal⟩ *
            setup.proposalRecoveryModel.opponentsStepProb policies who prior ⟨joint, legal⟩ *
            (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩ target).toReal) := by
      have lengthEq : (prior.extend joint legal moved).length - firstTrace.length =
          (prior.length - firstTrace.length) + 1 := by
        have bounded := retained.length_le
        simp only [Trace.length]
        omega
      have lastAtom := setup.proposalRecoveryProtocol.runRandomizedFor_apply_of_trace_succ
        (setup.proposalRecoveryModel.randomizedChooser policies)
          (prior.length - firstTrace.length) ⟨firstState, firstTrace⟩
            ⟨target, prior.extend joint legal moved⟩ (by
              have bounded := retained.length_le
              simp only [Trace.length]
              omega)
      have one := setup.proposalRecoveryModel.runBehavioralFrom_one_prob_extend policies
        ⟨some current, prior⟩ legal.1 ⟨joint, legal⟩ target moved
      change (setup.proposalRecoveryModel.runBehavioralFrom policies 1 ⟨some current, prior⟩
        ⟨target, prior.extend joint legal moved⟩).toReal = _ at one
      change (setup.proposalRecoveryModel.runBehavioralFrom policies
        (prior.length - firstTrace.length + 1) ⟨firstState, firstTrace⟩)
          ⟨target, prior.extend joint legal moved⟩ = _ at lastAtom
      rw [lengthEq, lastAtom, ENNReal.toReal_mul]
      change (setup.proposalRecoveryModel.runBehavioralFrom policies
          (prior.length - firstTrace.length) ⟨firstState, firstTrace⟩
            ⟨some current, prior⟩).toReal *
        (setup.proposalRecoveryModel.runBehavioralFrom policies 1 ⟨some current, prior⟩
          ⟨target, prior.extend joint legal moved⟩).toReal = _
      rw [one,
        setup.proposalRecoveryModel.stepProb_eq_player_mul_counterfactual policies who,
        InformationModel.counterfactualStepProb]
      ring
    have foreignAtom := sourceReplay_commit_opponents_calibration setup values scale sourceBad
      who current prior committing joint legal target moved proper
    have prescribedOpponents : setup.proposalRecoveryModel.opponentsStepProb profile who prior
        ⟨joint, legal⟩ =
      (setup.proposalRecoveryForeignRowFactors values scale sourceBad scale who
        ⟨some current, prior⟩ joint legal moved).1.toReal *
          setup.proposalRecoveryModel.opponentsStepProb ordinary who prior ⟨joint, legal⟩ := by
      rw [← foreignAtom]
      unfold InformationModel.opponentsStepProb
      apply Finset.prod_congr rfl
      intro owner _member
      rw [prescribed owner ⟨some current, prior⟩ legal.1]
    refine ⟨newer, ?_, ?_⟩
    · rw [InfoSignals.ownPlay_extend, recorded]
      cases chosen : joint who <;> simp only [newer, chosen, List.cons_append]
    · rw [InformationModel.playerReachProbability, Setup.proposalRecoveryForeignProducts,
        ENNReal.toReal_mul, extendAtom ordinary, extendAtom profile, newOwn,
        prescribedOpponents]
      calc
        _ =
            (setup.proposalRecoveryModel.playerReachProbability profile who prior *
              (setup.proposalRecoveryForeignProducts values scale sourceBad scale who
                prior).1.toReal *
              (setup.proposalRecoveryModel.runBehavioralFrom ordinary
                (prior.length - firstTrace.length) ⟨firstState, firstTrace⟩
                  ⟨some current, prior⟩).toReal) *
            (setup.proposalRecoveryModel.playerStepProb profile who prior ⟨joint, legal⟩ *
              (setup.proposalRecoveryForeignRowFactors values scale sourceBad scale who
                ⟨some current, prior⟩ joint legal moved).1.toReal *
              setup.proposalRecoveryModel.playerStepProb ordinary who prior ⟨joint, legal⟩ *
              setup.proposalRecoveryModel.opponentsStepProb ordinary who prior ⟨joint, legal⟩ *
              (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩ target).toReal) :=
          by ring
        _ = _ := by rw [calibrated]; ring

omit [Fintype Player] in
private theorem sourceReplay_ordinary_commitment_action_law (who : Player)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding who ty)
    (rank : named.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point)
    (survives : who ∉ current.excluded) :
    ((sourceUnflaggedStrategy setup values) who (setup.proposalRecoveryModel.infoOf who prior)).map
        (fun choice => choice.val.map (fun move => move.semantic.action)) =
      (values who (setup.proposalRecoveryQuery who
        (setup.proposalRecoveryModel.infoOf who prior))).map (fun sampled =>
          decodeEventAction setup.program named
            (cast (congrArg EventField.Action shape.symm) (.success
              (phaseRecoveryDomainValue setup .concurrent named who ty shape
                sampled.val.val)))) := by
  classical
  let ordinary := sourceUnflaggedStrategy setup values
  let information := setup.proposalRecoveryModel.infoOf who prior
  let key := setup.proposalRecoveryQuery who information
  let lift := fun sampled : setup.CommitRecoveryValueChoice who key.1 =>
    (setup.proposalRecoveryComponentChoice who information).symm
      (setup.proposalRecoveryComponentLabelChoice who key false sampled.val)
  have lifted (sampled : setup.CommitRecoveryValueChoice who key.1) :
      (lift sampled).val = sampled.val.val.map ProposalRecoveryMove.ordinary := by
    change sampled.val.val.map (fun move => ProposalRecoveryMove.label move false) = _
    simp only [ProposalRecoveryMove.label_false]
  have rawLaw : ordinary who information = (values who key).map lift := by
    exact setup.proposalRecovery_ordinary_choice_law values who information
  change (ordinary who information).map
      (fun choice => choice.val.map (fun move => move.semantic.action)) =
    (values who key).map (fun sampled =>
      decodeEventAction setup.program named
        (cast (congrArg EventField.Action shape.symm) (.success
          (phaseRecoveryDomainValue setup .concurrent named who ty shape sampled.val.val))))
  rw [rawLaw, PMF.map_comp]
  apply congrArg (fun transform => (values who key).map transform)
  funext sampled
  dsimp only [Function.comp_def]
  rw [lifted]
  simp only [Option.map_map, Function.comp_def, ProposalRecoveryMove.ordinary_semantic]
  obtain ⟨_committing, acting, decode⟩ := source_binding_at_rank setup.program current.point
    named who ty shape rank
  have legal := (setup.proposalRecoveryModel.menu_adequate who prior (lift sampled).val).mp
    (lift sampled).property
  rw [lifted] at legal
  cases selected : sampled.val.val with
  | none =>
      simp only [selected, Option.map_none] at legal
      exact (legal ⟨acting, survives⟩).elim
  | some move =>
      simp only [selected, Option.map_some] at legal
      have proper := sampled.property move selected
      obtain ⟨encoded, decoded⟩ := decode move.action legal.2.1.1
      have encoding := encodeEventAction?_decodeEventAction_eq_some setup.program named
        encoded move.action decoded
      have notFailure : cast (congrArg EventField.Action shape) encoded ≠ .failure := by
        intro failed
        exact proper.2 ((decodeEventAction_binding_failure_iff setup.program named who ty
          shape encoded move.action decoded).mp failed)
      cases result : cast (congrArg EventField.Action shape) encoded with
      | failure => exact (notFailure result).elim
      | success value =>
          have data : phaseRecoveryBindingData setup .concurrent named who ty shape
              sampled.val.val = (.success value, false) := by
            simp only [selected, phaseRecoveryBindingData, Option.elim_some, proper.1,
              Bool.false_eq_true, ite_false, Option.bind_some, encoding, Option.map_some,
              Option.getD_some, result]
          have domain : phaseRecoveryDomainValue setup .concurrent named who ty shape
              sampled.val.val = value := by
            unfold phaseRecoveryDomainValue
            rw [data]
          have encodedEq : encoded = cast (congrArg EventField.Action shape.symm)
              (.success value) := by
            rw [← result]
            simp only [cast_cast, cast_eq]
          have domainAtSome : phaseRecoveryDomainValue setup .concurrent named who ty shape
              (some move) = value := by
            rw [← selected]
            exact domain
          rw [domainAtSome, ← encodedEq, decoded]
          rfl

omit [Fintype Player] in
private theorem sourceReplay_ordinary_commitment_action_atom (who : Player)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who prior))
    (proper : ∀ move, choice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure) :
    (((sourceUnflaggedStrategy setup values) who (setup.proposalRecoveryModel.infoOf who prior)).map
        (fun choice => choice.val.map (fun move => move.semantic.action)))
          (choice.val.map (fun move => move.semantic.action)) =
      (sourceUnflaggedStrategy setup values) who
        (setup.proposalRecoveryModel.infoOf who prior) choice := by
  classical
  let ordinary := sourceUnflaggedStrategy setup values
  let information := setup.proposalRecoveryModel.infoOf who prior
  let key := setup.proposalRecoveryQuery who information
  let raw := fun sampled : setup.CommitRecoveryValueChoice who key.1 =>
    sampled.val.val.map ProposalRecoveryMove.ordinary
  let action := fun sampled : setup.CommitRecoveryValueChoice who key.1 =>
    sampled.val.val.map (fun move => move.action)
  let selected : setup.CommitRecoveryValueChoice who key.1 :=
    ⟨setup.proposalRecoveryComponentSemanticChoice who key
      (setup.proposalRecoveryComponentChoice who information choice), proper⟩
  have rawSelected : raw selected = choice.val :=
    setup.proposalRecovery_option_ordinary_of_atCommit current committing who choice.val
      ((setup.proposalRecoveryModel.menu_adequate who prior choice.val).mp choice.property)
  have actionSelected : action selected =
      choice.val.map (fun move => move.semantic.action) := by
    change (choice.val.map (·.semantic)).map (·.action) = _
    simp only [Option.map_map, Function.comp_def]
  have rawInjective : Function.Injective raw := by
    intro first second same
    apply Subtype.ext
    apply Subtype.ext
    have semantic := congrArg (Option.map (fun move : ProposalRecoveryMove Player L =>
      move.semantic)) same
    simpa only [raw, Option.map_map, Function.comp_def, ProposalRecoveryMove.ordinary,
      Option.map_id'] using semantic
  have actionInjective : Function.Injective action := by
    intro first second same
    apply Subtype.ext
    apply Subtype.ext
    cases firstValue : first.val.val with
    | none =>
        cases secondValue : second.val.val with
        | none => rfl
        | some secondMove =>
            simp only [action, firstValue, secondValue, Option.map_none,
              Option.map_some] at same
            cases same
    | some firstMove =>
        cases secondValue : second.val.val with
        | none =>
            simp only [action, firstValue, secondValue, Option.map_none,
              Option.map_some] at same
            cases same
        | some secondMove =>
            have sameAction : firstMove.action = secondMove.action :=
              Option.some.inj (by simpa only [action, firstValue, secondValue,
                Option.map_some] using same)
            have firstProper := first.property firstMove firstValue
            have secondProper := second.property secondMove secondValue
            have sameMove : firstMove = secondMove := by
              cases firstMove with
              | mk firstAction firstMissing =>
                  cases secondMove with
                  | mk secondAction secondMissing =>
                      exact congrArg₂ CommitRecoveryMove.mk sameAction
                        (firstProper.1.trans secondProper.1.symm)
            rw [sameMove]
  have rawLaw : (ordinary who information).map Subtype.val =
      (values who key).map raw := by
    unfold ordinary sourceUnflaggedStrategy
    rw [setup.proposalRecovery_ordinary_choice_law, PMF.map_comp]
    apply congrArg (fun transform => (values who key).map transform)
    funext sampled
    change sampled.val.val.map (fun move => ProposalRecoveryMove.label move false) = _
    simp only [raw, ProposalRecoveryMove.label_false]
  have actionLaw : (ordinary who information).map
      (fun choice => choice.val.map (fun move => move.semantic.action)) =
        (values who key).map action := by
    calc
      _ = ((ordinary who information).map Subtype.val).map
          (Option.map (fun move : ProposalRecoveryMove Player L =>
            move.semantic.action)) := by rw [PMF.map_comp]; rfl
      _ = ((values who key).map raw).map
          (Option.map (fun move : ProposalRecoveryMove Player L =>
            move.semantic.action)) := congrArg (fun law => law.map
              (Option.map (fun move : ProposalRecoveryMove Player L =>
                move.semantic.action))) rawLaw
      _ = _ := by
        rw [PMF.map_comp]
        apply congrArg (fun transform => (values who key).map transform)
        funext sampled
        change (sampled.val.val.map ProposalRecoveryMove.ordinary).map
          (fun move => move.semantic.action) = sampled.val.val.map (fun move => move.action)
        simp only [Option.map_map, Function.comp_def,
          ProposalRecoveryMove.ordinary_semantic]
        rfl
  have rawEvaluation : ((values who key).map raw) (raw selected) =
      values who key selected :=
    pmf_map_apply_of_injective (values who key) rawInjective selected
  have rawAtom : ordinary who information choice = values who key selected := by
    calc
      _ = ((ordinary who information).map Subtype.val) choice.val :=
        (pmf_map_apply_of_injective (ordinary who information)
          Subtype.val_injective choice).symm
      _ = ((values who key).map raw) (raw selected) := by
        rw [rawLaw, rawSelected]
        rfl
      _ = _ := rawEvaluation
  have actionEvaluation : ((values who key).map action) (action selected) =
      values who key selected :=
    pmf_map_apply_of_injective (values who key) actionInjective selected
  rw [actionLaw, ← actionSelected, actionEvaluation, rawAtom]

omit [Fintype Player] [IExpr.ResultTypes L] in
private theorem sourceReplay_attempt_owned_actions (who : Player) :
    ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (piece : SourceProgram.CommitPrefix Γ O Δ P)
    (sourceInitial replacement : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (final : SourceProgram.Config Player L Δ)
    (candidate : piece.Attempt sourceInitial excluded final excluded),
    who ∉ excluded →
    (List.range piece.length).map (fun index => piece.wordAction who index
      ((candidate.withoutMisses ∅ replacement).view who)) =
        candidate.joints.map (fun joint => (joint who).map (fun move => move.action)) := by
  classical
  intro Γ Δ O P piece
  induction piece with
  | nil =>
      intro sourceInitial replacement excluded final candidate _survives
      cases candidate
      rfl
  | @commit Γ O Δ P name actor ty fresh guard rest ih =>
      intro sourceInitial replacement excluded final candidate survives
      cases candidate with
      | active active result missed valid tail =>
          have noMiss : missed = false := by
            cases missed with
            | false => rfl
            | true =>
                have inserted : actor ∈ excludeCommit excluded actor true := by
                  simp only [excludeCommit, ite_true, Finset.mem_insert, true_or]
                exact (active (tail.excluded_subset inserted)).elim
          subst missed
          have projected := SourceProgram.CommitPrefix.Attempt.entryView_eq rest
            (commitSuccessor name guard replacement result) _
              (tail.withoutMisses_attempt ∅ (Finset.empty_subset excluded)
                (commitSuccessor name guard replacement result)) who
          have restEq := ih _ (commitSuccessor name guard replacement result) excluded
            final tail survives
          rw [SourceProgram.CommitPrefix.length, List.range_succ_eq_map,
            List.map_cons, List.map_map]
          simp only [Function.comp_def, SourceProgram.CommitPrefix.wordAction,
            SourceProgram.CommitPrefix.Attempt.withoutMisses,
            SourceProgram.CommitPrefix.Attempt.joints, List.map_cons]
          rw [restEq]
          congr 1
          by_cases own : actor = who
          · subst actor
            simp only [ite_true]
            rw [projected]
            simp only [SourceProgram.Config.view, commitSuccessor,
              sourceObserve_commitment, ite_true, Option.getD_some, Option.map_some,
              Env.cons_get_here]
          · have reversed : who ≠ actor := Ne.symm own
            simp only [own, reversed, ite_false, Option.map_none]
      | excluded inactive tail =>
          have different : actor ≠ who := by
            intro same
            exact survives (same ▸ inactive)
          have restEq := ih _ (commitSuccessor name guard replacement .failure) excluded
            final tail survives
          rw [SourceProgram.CommitPrefix.length, List.range_succ_eq_map,
            List.map_cons, List.map_map]
          simp only [Function.comp_def, SourceProgram.CommitPrefix.wordAction,
            SourceProgram.CommitPrefix.Attempt.withoutMisses,
            Finset.notMem_empty, ite_false, SourceProgram.CommitPrefix.Attempt.joints,
            different, List.map_cons, Option.map_none]
          exact congrArg (none :: ·) restEq

omit [Fintype Player] in
private theorem sourceReplay_source_generation_mono
    (first last : CommitRecoveryState setup.program)
    (firstTrace : setup.commitRecoveryProtocol.Trace (some first))
    (lastTrace : setup.commitRecoveryProtocol.Trace (some last))
    (kept : TracePrefix firstTrace lastTrace) : first.generation ≤ last.generation := by
  classical
  have monotone : ∀ {fuel : Nat} {start finish : setup.commitRecoveryProtocol.History},
      setup.commitRecoveryProtocol.ReachesWithin fuel start finish →
      ∀ first last, start.state = some first → finish.state = some last →
        first.generation ≤ last.generation := by
    intro fuel start finish reached
    induction reached with
    | refl =>
        intro first last firstEq lastEq
        cases Option.some.inj (firstEq.symm.trans lastEq)
        exact le_rfl
    | @step fuel start target joint legal next moved rest ih =>
        intro first last firstEq lastEq
        rcases start with ⟨state, trace⟩
        change state = some first at firstEq
        subst state
        obtain ⟨middle, moved, equal⟩ := (PMF.mem_support_map_iff ..).mp moved
        exact (first.step_generation_mono joint middle moved).trans
          (ih middle last equal.symm lastEq)
  exact monotone kept.reachesWithin first last rfl rfl

omit [Fintype Player] in
private theorem sourceReplay_source_exclusions_mono
    {first last : setup.commitRecoveryProtocol.State}
    (firstTrace : setup.commitRecoveryProtocol.Trace first)
    (lastTrace : setup.commitRecoveryProtocol.Trace last)
    (kept : TracePrefix firstTrace lastTrace) :
    (setup.commitRecoveryPublic first).1 ⊆ (setup.commitRecoveryPublic last).1 := by
  classical
  induction kept with
  | refl => exact Finset.Subset.refl _
  | extend earlier joint legal moved ih =>
      exact ih.trans (setup.commitRecovery_step_excluded_subset joint legal moved)

private theorem sourceReplay_selected_source_tail_atom
    (who : Player) (g : setup.proposalRecoveryProtocol.History)
    (sourceChoice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (choiceSome : sourceChoice.val ≠ none)
    (supported : (⟨some targetCurrent, targetTrace⟩ : setup.proposalRecoveryProtocol.History) ∈
      (sourceForcedBlock setup values who g sourceChoice).support)
    (positiveFuel : 0 < sourceCommitFuel setup g) :
    setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup values)
        (sourceCommitFuel setup g) g ⟨some targetCurrent, targetTrace⟩ =
      sourceUnflaggedStrategy setup values who
          (setup.proposalRecoveryModel.infoOf who g.trace) sourceChoice *
        sourceForcedBlock setup values who g sourceChoice ⟨some targetCurrent, targetTrace⟩ := by
  classical
  let ordinary := sourceUnflaggedStrategy setup values
  have active : setup.proposalRecoveryProtocol.active g.state who := by
    have legal := (setup.proposalRecoveryModel.menu_adequate who g.trace sourceChoice.val).mp
      sourceChoice.property
    cases selected : sourceChoice.val with
    | none => exact (choiceSome selected).elim
    | some action =>
        rw [selected] at legal
        exact legal.1
  have nonterminal : ¬ setup.proposalRecoveryProtocol.terminal g.state := by
    intro stopped
    rcases g with ⟨state, gTrace⟩
    cases state with
    | none => cases active
    | some current =>
        change ProtocolState.terminal setup.program current.point at stopped
        change ProtocolState.actor setup.program current.point = some who ∧ _ at active
        have none := ProtocolState.terminal_actor_none who setup.program current.point stopped
        rw [ProtocolState.actor_observe_eq] at none
        rw [active.1] at none
        cases none
  let forced := fun choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace) =>
    Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) ordinary who
      ((ordinary who).commit (setup.proposalRecoveryModel.infoOf who g.trace) choice)
  have currentMixture : setup.proposalRecoveryModel.runBehavioralFrom ordinary 1 g =
      (ordinary who (setup.proposalRecoveryModel.infoOf who g.trace)).bind
        (fun choice => setup.proposalRecoveryModel.runBehavioralFrom (forced choice) 1 g) := by
    have joint := setup.proposalRecoveryModel.behavioralJoint_update_withLaw_eq_bind ordinary
      who (ordinary who) (setup.proposalRecoveryModel.infoOf who g.trace)
        (ordinary who (setup.proposalRecoveryModel.infoOf who g.trace)) g.trace nonterminal rfl
    rw [InformationModel.BehavioralPolicy.withLaw_eq_self] at joint
    have sameUpdate : Profile.update
        (sig := setup.proposalRecoveryModel.behavioralSignature) ordinary who (ordinary who) =
          ordinary := by
      funext owner
      by_cases same : owner = who
      · subst owner; exact Profile.update_same ..
      · exact Profile.update_of_ne _ _ same
    rw [sameUpdate] at joint
    rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal ordinary 0
      nonterminal, joint, PMF.bind_bind]
    apply bind_congr_on_support
    intro choice _chosen
    rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal (forced choice) 0
      nonterminal]
    apply bind_congr_on_support
    intro draw _supported
    apply bindOnSupport_congr
    intro next reached
    rfl
  have forcedFirst
      (choice : setup.proposalRecoveryModel.Choice who
        (setup.proposalRecoveryModel.infoOf who g.trace))
      (positive : sourceForcedBlock setup values who g choice
        ⟨some targetCurrent, targetTrace⟩ ≠ 0) :
      ∃ (joint : Player → Option (ProposalRecoveryMove Player L))
        (legal : setup.proposalRecoveryProtocol.Legal g.state joint)
        (next : setup.proposalRecoveryProtocol.State)
        (moved : next ∈ (setup.proposalRecoveryProtocol.step g.state ⟨joint, legal⟩).support),
        TracePrefix (g.trace.extend joint legal moved) targetTrace ∧ joint who =
          choice.val := by
    have present := (PMF.mem_support_iff ..).mpr positive
    unfold sourceForcedBlock at present
    obtain ⟨middle, first, rest⟩ := (PMF.mem_support_bind_iff ..).mp present
    rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal (forced choice)
      0 nonterminal] at first
    obtain ⟨draw, chosen, continued⟩ := (PMF.mem_support_bind_iff ..).mp first
    rw [PMF.support_bindOnSupport] at continued
    obtain ⟨next, moved, pureSupport⟩ := Set.mem_iUnion₂.mp continued
    have middleEq : middle = g.extend draw.property moved := by
      simpa only [InformationModel.runBehavioralFrom, ExecutionProtocol.runRandomizedFor_zero,
        PMF.mem_support_pure_iff] using pureSupport
    subst middle
    obtain ⟨choices, supportedChoices, jointEq⟩ := (PMF.mem_support_map_iff ..).mp chosen
    have own := (independentProduct_support_iff _ _).mp supportedChoices who
    have sameChoice : choices who = choice := by
      simpa only [forced, Profile.update_same, InformationModel.BehavioralPolicy.commit_self,
        PMF.mem_support_pure_iff] using own
    refine ⟨draw.val, draw.property, next, moved,
      (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin ordinary
        (sourceCommitFuel setup g - 1) _ ⟨some targetCurrent, targetTrace⟩
          rest).tracePrefix, ?_⟩
    have selected := congrArg (fun joint => joint.val who) jointEq
    exact selected.symm.trans (congrArg Subtype.val sameChoice)
  have forcedChoiceUnique
      (choice : setup.proposalRecoveryModel.Choice who
        (setup.proposalRecoveryModel.infoOf who g.trace))
      (positive : sourceForcedBlock setup values who g choice
        ⟨some targetCurrent, targetTrace⟩ ≠ 0) : choice = sourceChoice := by
    obtain ⟨first, firstLegal, firstState, firstMoved, firstKept, firstChoice⟩ :=
      forcedFirst choice positive
    obtain ⟨second, secondLegal, secondState, secondMoved, secondKept, secondChoice⟩ :=
      forcedFirst sourceChoice ((PMF.mem_support_iff ..).mp supported)
    have same := firstKept.eq_of_same_length secondKept rfl
    have jointEq : first = second := Option.some.inj (by
      have selected := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
        (setup.proposalRecoveryJointRecall history.trace).head?) same
      simpa only [Setup.proposalRecoveryJointRecall, List.head?_cons] using selected)
    apply Subtype.ext
    exact firstChoice.symm.trans ((congrFun jointEq who).trans secondChoice)
  have mixture : setup.proposalRecoveryModel.runBehavioralFrom ordinary
      (sourceCommitFuel setup g) g =
        (ordinary who (setup.proposalRecoveryModel.infoOf who g.trace)).bind
          (fun choice => sourceForcedBlock setup values who g choice) := by
    rw [show sourceCommitFuel setup g = 1 + (sourceCommitFuel setup g - 1) by omega,
      setup.proposalRecoveryModel.runBehavioralFrom_add, currentMixture, PMF.bind_bind]
    rfl
  rw [mixture, PMF.bind_apply]
  apply tsum_eq_single sourceChoice
  intro choice different
  have zero : sourceForcedBlock setup values who g choice
      ⟨some targetCurrent, targetTrace⟩ = 0 := by
    by_contra positive
    exact different (forcedChoiceUnique choice positive)
  rw [zero, mul_zero]

/- Literal source prefix cylinders and their chronological products. -/

open scoped Classical in
private theorem sourceReplay_source_prefix_position_law
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    {Δ : SourceCtx Player L} {Q : Finset VarId}
    (suffix : SourceProgram Player L Δ Q)
    (wordBlock : SourceProgram.CommitPrefix
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.context
      (checkpointSelection setup implementation operational
        trace).val.checkpoint.residual.names Δ Q)
    (reconstruct : (checkpointSelection setup implementation operational
      trace).val.checkpoint.residual.tail =
      wordBlock.prepend suffix)
    (boundary : IsCommitBoundary suffix)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan control phase wordBlock suffix)
    (blockPositive : 0 < wordBlock.length)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (wholeSupport : (⟨some targetCurrent, targetTrace⟩ :
      setup.proposalRecoveryProtocol.History) ∈
      (setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup values)
        wordBlock.length ⟨some cursor.current, cursor.trace⟩).support)
    (referenceWord : SourceProgram.Config Player L Δ)
    (referenceWordSupport : referenceWord ∈ (wordBlock.prefixLaw suffix
      (ordinaryBlockProfile setup .concurrent implementation.plan values wordBlock suffix
        cursor.embedding (fun owner view => cursor.views.view owner view)
        (control.execution.application.entry.excluded, control.execution.application.generation,
          control.execution.application.attempt.phase)
        control.execution.application.publicView
        (PhaseProposal.sourceArchive control.execution.network.inputs)) cursor.source).support)
    (issuedLedgers : ∀ owner, issuedLedger setup implementation wordBlock
      control.execution.application.attempt.phase control
        (control.execution.application.attempt.phase + wordBlock.length) owner
          (referenceWord.view owner))
    (finished : SourceProgram.Config Player L Δ)
    (attempt : wordBlock.Attempt cursor.source cursor.current.excluded finished
      targetCurrent.excluded)
    (finishedPoint : targetCurrent.point = cursor.lift
      (wordBlock.liftPoint suffix (ProtocolState.entry suffix finished)))
    (finishedExcluded : targetCurrent.excluded = cursor.current.excluded)
    (structuralWord : referenceWord = attempt.withoutMisses ∅ cursor.source)
    (who : Player)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (actualClean : CleanUnsentBinding setup implementation who
      (control.execution.recall who) (control.execution.observe nativeApplication who)
        event payload)
    (actualEntry : NativeBindingEntry setup implementation operational control trace who event)
    (actualCut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler control
      (sourceCutTrace setup implementation trace) who event)
    (phaseLow : actualEntry.phase.low = control.execution.application.attempt.phase)
    (phaseHigh : actualEntry.phase.high =
      control.execution.application.attempt.phase + wordBlock.length)
    (embeddingRank : ∀ index, (cursor.embedding.event index).val =
      control.execution.application.attempt.phase + index.val)
    (offsetInside : event.val - control.execution.application.attempt.phase < wordBlock.length)
    (position : Nat)
    (earlierPosition : position < event.val - control.execution.application.attempt.phase)
    (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding who ty)
    (positionEq : named.val = control.execution.application.attempt.phase + position)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (retained : TracePrefix prior targetTrace)
    (rank : named.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point)
    (generation : current.generation = control.execution.application.generation)
    (survives : who ∉ current.excluded) :
    (fiberPosterior
      ((wordBlock.prefixLaw suffix
        (ordinaryBlockProfile setup .concurrent implementation.plan values wordBlock suffix
          cursor.embedding (fun owner view => cursor.views.view owner view)
          (control.execution.application.entry.excluded, control.execution.application.generation,
            control.execution.application.attempt.phase)
          control.execution.application.publicView
          (PhaseProposal.sourceArchive control.execution.network.inputs)) cursor.source).map
            (SourceProgram.Config.view who))
      (fun candidate => decide (∀ index < position, wordBlock.wordAction who index candidate =
        wordBlock.wordAction who index (referenceWord.view who))) true).map
          (wordBlock.wordAction who position) =
      ((sourceUnflaggedStrategy setup values) who
        (setup.proposalRecoveryModel.infoOf who prior)).map
          (fun choice => choice.val.map (fun move => move.semantic.action)) := by
  classical
  let low := control.execution.application.attempt.phase
  let offset := event.val - low
  let ordinary := sourceUnflaggedStrategy setup values
  let wordProfile := ordinaryBlockProfile setup .concurrent implementation.plan values wordBlock
    suffix cursor.embedding (fun owner view => cursor.views.view owner view)
      (control.execution.application.entry.excluded, control.execution.application.generation, low)
      control.execution.application.publicView
      (PhaseProposal.sourceArchive control.execution.network.inputs)
  let ownWordLaw := (wordBlock.prefixLaw suffix wordProfile cursor.source).map
    (SourceProgram.Config.view who)
  let sourceObservationAt := fun count candidate => decide (
    ∀ index < count, wordBlock.wordAction who index candidate =
      wordBlock.wordAction who index (referenceWord.view who))
  change (fiberPosterior ownWordLaw (sourceObservationAt position) true).map
      (wordBlock.wordAction who position) =
    (ordinary who (setup.proposalRecoveryModel.infoOf who prior)).map
      (fun choice => choice.val.map (fun move => move.semantic.action))
  change position < offset at earlierPosition
  change named.val = low + position at positionEq
  change actualEntry.phase.low = low at phaseLow
  change actualEntry.phase.high = low + wordBlock.length at phaseHigh
  change offset < wordBlock.length at offsetInside
  have initialEq : nativeInitial = (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  have namedInside : named ∈ actualEntry.phase.events := by
    apply (actualEntry.phase.mem_events named).mpr
    rw [phaseLow, phaseHigh, positionEq]
    omega
  have earlierRank : named.val < event.val := by
    dsimp only [offset] at earlierPosition
    omega
  have actualTrace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map
        (PhaseRuntimeState.initial implementation.plan)) implementation.horizon
      implementation.scheduler).Trace (some control) := initialEq ▸ trace
  obtain ⟨candidate, owned, accepted, _read⟩ := phase_ready_earlier_binding_read
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
        actualTrace (serviceGraph_revealRelaxedOrdered setup .concurrent)
          actualEntry.phase actualEntry.installed who event payload actualClean.binding
            actualCut.request.2.2.1 actualCut.request.2.2.2.2 named ty shape namedInside
              earlierRank
  have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have stamp := phaseLiveBindingStamp_history implementation.runtime implementation.leaks
    implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
      implementation.scheduler (initialEq ▸ raw)
  obtain ⟨message, output, _sender, call, signed⟩ :=
    (stamp named candidate accepted).resolve_left (by rw [positionEq]; omega)
  rw [owned] at output
  obtain ⟨record, member, emitted⟩ := List.mem_filterMap.mp output
  obtain ⟨serial, opening, evidence, _candidateEq, _sender, action, _fresh,
    namespaceEq, _meaning⟩ := sourceReplay_recorded_binding_registration setup implementation
      control trace who record member message emitted named ty shape candidate call
  obtain ⟨earlierRecall, laterRecall, recalled⟩ := List.mem_iff_append.mp member
  obtain ⟨before, beforeTrace, beforeKept, acting, past, viewed, offered⟩ :=
    (nativeMenu).recorded_response_at nativeInitial implementation.horizon
      implementation.scheduler control trace who earlierRecall record laterRecall recalled
  let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.commitment named (who, .prepared serial), opening⟩, evidence⟩
  have available : (⟨some material⟩ : (nativeApplication).Action) ∈
      PhaseCount.onePacketActions implementation.runtime implementation.leaks
        implementation.bounds who (before.execution.recall who)
          (before.execution.observe nativeApplication who) := by
    rw [past]
    simpa only [action, material, PhaseCount.onePacketMenu] using offered
  have activeTrace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map
        (PhaseRuntimeState.initial implementation.plan)) implementation.horizon
      implementation.scheduler).Trace (some ⟨before.remaining, some who,
        before.execution⟩) := by
    have same : before = ⟨before.remaining, some who, before.execution⟩ := by
      cases before
      cases acting
      rfl
    exact same ▸ initialEq ▸ beforeTrace
  obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
        before.remaining who before.execution activeTrace material available
  have eventName := PhaseCount.onePacket_event_of_request implementation.runtime
    implementation.leaks implementation.bounds implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent)
        (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
          before.remaining who before.execution activeTrace coordinate request material
            available
  have coordinateEq : coordinate = ⟨before.execution.application.attempt, named⟩ := by
    have sameEvent : coordinate.event = named := by
      change some named = some coordinate.event at eventName
      exact (Option.some.inj eventName).symm
    cases coordinate with
    | mk attempt event =>
        cases request.1
        cases sameEvent
        rfl
  rw [coordinateEq] at request
  have unsent := PhaseCount.unsent_of_nonsilent implementation.runtime implementation.leaks
    implementation.bounds implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent)
        (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
          before.remaining who before.execution activeTrace
            ⟨before.execution.application.attempt, named⟩ request material available
  have sameAttempt : before.execution.application.attempt =
      control.execution.application.attempt := by
    rw [viewed] at namespaceEq
    exact namespaceEq.trans signed
  have countRecall : before.execution.recall who =
      (control.execution.recall who).take earlierRecall.length := by
    rw [recalled, List.take_left, past]
  have previousLedger := sourceReplay_issued_ledger_prefix setup implementation wordBlock
    low (low + wordBlock.length) control trace before who (by
      rw [past, recalled]
      intro recalledRecord member
      exact List.mem_append_left _ member) sameAttempt
        (referenceWord.view who) (issuedLedgers who)
  have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    intro state present
    rw [initialEq] at present
    obtain ⟨input, _present, rfl⟩ := (PMF.mem_support_map_iff ..).mp present
    exact PhaseRuntimeState.initial_ordered implementation.plan input
  have beforeOrdered := (phaseApplication_seedOrder implementation.runtime
    implementation.leaks).history nativeInitial implementation.horizon
      implementation.scheduler initialized
        ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler beforeTrace)
  have metadata := phase_attempt_metadata_of_prefix implementation.runtime
    implementation.leaks nativeMenu nativeInitial initialized implementation.horizon
      implementation.scheduler before control beforeTrace trace beforeKept beforeOrdered
        sameAttempt
  have beforeInstalled : before.execution.application.phases.head? =
      some actualEntry.phase :=
    (congrArg (fun pair => pair.1.head?) metadata).trans actualEntry.installed
  have observation : (fun word => decide (sourceIssuedOwnObservation setup implementation
      wordBlock low control who (referenceWord.view who) earlierRecall.length word)) =
        sourceObservationAt position := by
    funext word
    apply decide_eq_decide.mpr
    rw [sourceReplay_issued_callback_observation setup implementation wordBlock
      suffix cursor.embedding low embeddingRank cursor.views.actionEq control before
        beforeTrace who earlierRecall.length countRecall sameAttempt
          (referenceWord.view who) word previousLedger,
      issuedLedger_iff_prefix_at_request setup implementation wordBlock suffix
        cursor.embedding low embeddingRank cursor.views.actionEq beforeTrace
          actualEntry.phase beforeInstalled phaseLow phaseHigh who named ty shape request
            (by rw [positionEq]; omega) unsent (referenceWord.view who) word previousLedger]
    have samePosition : named.val - low = position := by omega
    simp only [samePosition]
  obtain ⟨_lower, _upper, law⟩ := sourceReplay_issued_source_callback_atom setup values
    implementation operational control trace suffix wordBlock reconstruct
      boundary phase cursor blockPositive targetCurrent targetTrace
        wholeSupport referenceWord referenceWordSupport
          issuedLedgers finished attempt finishedPoint finishedExcluded structuralWord who
            earlierRecall.length named ty shape before beforeTrace beforeKept countRecall
              sameAttempt unsent request current prior retained rank generation survives
  rw [observation, show named.val - low = position by omega] at law
  exact law.trans (sourceReplay_ordinary_commitment_action_law setup values who current
    prior named ty shape rank survives).symm

/- Source prefix cylinder telescopes along the retained recovery trace. -/

open Classical in
private theorem sourceReplay_source_prefix_cylinder_fold
    (who : Player) (control : (nativeApplication).Control)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (block : SourceProgram.CommitPhase program)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan control phase block.block block.suffix)
    (blockPositive : 0 < block.block.length)
    (q g : setup.proposalRecoveryProtocol.History)
    (qLength : q.trace.length = cursor.trace.length)
    (qInitialized : 0 < q.trace.length)
    (cursorPrefix : ∀ {state : setup.proposalRecoveryProtocol.State}
      (prior : setup.proposalRecoveryProtocol.Trace state),
      TracePrefix q.trace prior → TracePrefix cursor.trace prior)
    (low offset : Nat)
    (gDepth : g.trace.length = q.trace.length + offset)
    (offsetInside : offset < block.block.length)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (gToTarget : TracePrefix g.trace targetTrace)
    (targetGeneration : targetCurrent.generation = cursor.current.generation)
    (finishedExcluded : targetCurrent.excluded = cursor.current.excluded)
    (actualAlive : who ∉ control.execution.application.current.excluded)
    (startRank : instructionCount setup.program -
      ProtocolState.remaining setup.program cursor.current.point = low)
    (embeddingRank : ∀ index, (cursor.embedding.event index).val = low + index.val)
    (wholeFinished : SourceProgram.Config Player L block.context)
    (wholeCurrent : CommitRecoveryState setup.program)
    (wholeAttempt : block.block.Attempt cursor.source cursor.current.excluded wholeFinished
      wholeCurrent.excluded)
    (literalWord : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetTrace) =
      wholeAttempt.joints.reverse ++ setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace cursor.trace))
    (wholeProper : ∀ joint ∈ wholeAttempt.joints, ∀ owner move, joint owner = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (referenceWord : SourceProgram.Config Player L block.context)
    (referenceWholeActions : (List.range block.block.length).map
      (fun index => block.block.wordAction who index (referenceWord.view who)) =
        wholeAttempt.joints.map (fun joint => (joint who).map (fun move => move.action)))
    (ownWordLaw : PMF (DecisionView who block.context))
    (rows : ∀ (before : setup.proposalRecoveryProtocol.History)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
      (after : setup.proposalRecoveryProtocol.State)
      (moved : after ∈ (setup.proposalRecoveryProtocol.step before.state ⟨joint, legal⟩).support),
      TracePrefix q.trace before.trace →
      TracePrefix (before.trace.extend joint legal moved) g.trace →
      ∃ current, before.state = some current ∧
        ProtocolState.atCommit setup.program current.point = true ∧
        ∀ owner move, owner ≠ who → joint owner = some move →
          move.semantic.missing = false ∧ ¬ move.semantic.action.IsFailure)
    (sourcePositionLaw : ∀ (position : Nat), position < offset →
      ∀ (named : (serviceGraph setup .concurrent).EventId) (ty : L.Ty)
        (_shape : (serviceGraph setup .concurrent).outputLayout named = .binding who ty),
      named.val = low + position →
      ∀ (current : CommitRecoveryState setup.program)
        (prior : setup.proposalRecoveryProtocol.Trace (some current)),
      TracePrefix prior targetTrace →
      named.val = instructionCount setup.program -
        ProtocolState.remaining setup.program current.point →
      current.generation = control.execution.application.generation →
      who ∉ current.excluded →
      (fiberPosterior ownWordLaw
        (fun candidate => decide (∀ index < position,
          block.block.wordAction who index candidate =
            block.block.wordAction who index (referenceWord.view who))) true).map
          (block.block.wordAction who position) =
        ((sourceUnflaggedStrategy setup values) who
          (setup.proposalRecoveryModel.infoOf who prior)).map
            (fun choice => choice.val.map (fun move => move.semantic.action)))
    (referencePresent : ∀ position, true ∈
      (ownWordLaw.map (fun candidate => decide (∀ index < position,
          block.block.wordAction who index candidate =
            block.block.wordAction who index (referenceWord.view who)))).support) :
    ∀ (last : setup.proposalRecoveryProtocol.History)
      (_kept : TracePrefix q.trace last.trace), TracePrefix last.trace g.trace →
      ∃ records : List (setup.proposalRecoveryModel.InfoState who ×
          setup.proposalRecoveryProtocol.Action who),
        setup.proposalRecoveryModel.ownPlay who last.trace =
          records ++ setup.proposalRecoveryModel.ownPlay who q.trace ∧
        (ownWordLaw.map (fun candidate => decide (
          ∀ position < last.trace.length - q.trace.length,
            block.block.wordAction who position candidate =
              block.block.wordAction who position (referenceWord.view who)))) true =
          ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
            ((sourceUnflaggedStrategy setup values) who) records) := by
  classical
  let ordinary := sourceUnflaggedStrategy setup values
  let sourceObservationAt := fun count candidate => decide (
    ∀ position < count, block.block.wordAction who position candidate =
      block.block.wordAction who position (referenceWord.view who))
  change ∀ (last : setup.proposalRecoveryProtocol.History)
      (kept : TracePrefix q.trace last.trace), TracePrefix last.trace g.trace →
      ∃ records : List (setup.proposalRecoveryModel.InfoState who ×
          setup.proposalRecoveryProtocol.Action who),
        setup.proposalRecoveryModel.ownPlay who last.trace =
          records ++ setup.proposalRecoveryModel.ownPlay who q.trace ∧
        (ownWordLaw.map (sourceObservationAt (last.trace.length - q.trace.length))) true =
          ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
            (ordinary who) records)
  intro last kept
  rcases last with ⟨lastState, lastTrace⟩
  dsimp only at kept ⊢
  induction kept with
  | refl =>
      intro _retained
      refine ⟨[], by simp only [List.nil_append], ?_⟩
      have empty : sourceObservationAt 0 = fun _ => true := by
        funext candidate
        apply decide_eq_true
        intro position impossible
        omega
      simp only [Nat.sub_self, empty, InformationModel.ownPlayReachProbability,
        ENNReal.ofReal_one]
      change (ownWordLaw.map (Function.const _ true)) true = 1
      rw [PMF.map_const, PMF.pure_apply_self]
  | @extend before after prior earlier joint legal moved ih =>
      intro retained
      have beforeG := (TracePrefix.extend .refl joint legal moved).trans retained
      obtain ⟨records, ownRecords, mass⟩ := ih beforeG
      obtain ⟨current, currentEq, committing, _foreignProper⟩ :=
        rows ⟨before, prior⟩ joint legal after moved earlier retained
      cases currentEq
      let position := prior.length - q.trace.length
      have positionInside : position < offset := by
        have upper := retained.length_le
        have lower := earlier.length_le
        simp only [Trace.length] at upper
        dsimp only [position]
        omega
      have positionBlock : position < block.block.length := by omega
      have erasedEarlier : TracePrefix (setup.proposalRecoveryEraseTrace cursor.trace)
          (setup.proposalRecoveryEraseTrace prior) := by
        apply setup.proposalRecoveryEraseTrace_prefix
        exact cursorPrefix prior earlier
      have erasedRetained := setup.proposalRecoveryEraseTrace_prefix
        (beforeG.trans gToTarget)
      have beforeGeneration : current.generation = cursor.current.generation := by
        have lower := sourceReplay_source_generation_mono setup cursor.current current
          (setup.proposalRecoveryEraseTrace cursor.trace)
            (setup.proposalRecoveryEraseTrace prior) erasedEarlier
        have upper := sourceReplay_source_generation_mono setup current targetCurrent
          (setup.proposalRecoveryEraseTrace prior)
            (setup.proposalRecoveryEraseTrace targetTrace) erasedRetained
        omega
      have beforeSurvives : who ∉ current.excluded := by
        intro excluded
        have afterExcluded := sourceReplay_source_exclusions_mono setup
          (setup.proposalRecoveryEraseTrace prior)
          (setup.proposalRecoveryEraseTrace targetTrace) erasedRetained excluded
        change who ∈ targetCurrent.excluded at afterExcluded
        rw [finishedExcluded, cursor.excluded] at afterExcluded
        exact actualAlive afterExcluded
      have balance := setup.commitRecovery_same_generation_length erasedEarlier.reachesWithin
        cursor.current current rfl rfl beforeGeneration.symm
      simp only [setup.proposalRecoveryEraseTrace_length] at balance
      have currentRank : instructionCount setup.program -
          ProtocolState.remaining setup.program current.point = low + position := by
        have firstBound := ProtocolState.remaining_le_instructionCount setup.program
          cursor.current.point
        have lower := earlier.length_le
        dsimp only [position]
        omega
      let index : Fin (eventCount (block.block.prepend block.suffix)) :=
        ⟨position, by have count := block.block.eventCount_prepend block.suffix; omega⟩
      obtain ⟨actor, ty, _member, layout⟩ := block.block.binding_before_length
        block.suffix index positionBlock
      let named := cursor.embedding.event index
      have shape : (serviceGraph setup .concurrent).outputLayout named = .binding actor ty :=
        (cursor.embedding.layout_eq index).trans layout
      have namedRank : named.val = low + position := embeddingRank index
      have atRank : named.val = instructionCount setup.program -
          ProtocolState.remaining setup.program current.point := namedRank.trans
            currentRank.symm
      have currentActor := (source_binding_at_rank setup.program current.point named actor
        ty shape atRank).2.1
      have sourceIndex : position < wholeAttempt.joints.length := by
        rw [wholeAttempt.joints_length]
        exact positionBlock
      obtain ⟨firstState, lastState, firstPrior, choices, permitted, reached,
        firstKept, firstDepth, semantic, _firstAddress, _lastAddress⟩ :=
          source_instruction_chunk_row setup cursor.trace targetTrace (by
            simpa only [qLength] using qInitialized) wholeAttempt.joints
              literalWord position sourceIndex
      have sameRow := firstKept.eq_of_same_length
        (retained.trans gToTarget) (by
          have lower := earlier.length_le
          simp only [Trace.length]
          dsimp only [position] at firstDepth
          omega)
      have choicesEq : choices = joint := Option.some.inj (by
        have same := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
          (setup.proposalRecoveryJointRecall history.trace).head?) sameRow
        simpa only [Setup.proposalRecoveryJointRecall, List.head?_cons] using same)
      have referenceAction : block.block.wordAction who position (referenceWord.view who) =
          (joint who).map (fun move => move.semantic.action) := by
        have selected := congrArg (fun word => word[position]?) referenceWholeActions
        have rangeInside : position < (List.range block.block.length).length := by
          simpa only [List.length_range] using positionBlock
        simp only [List.getElem?_map, List.getElem?_eq_getElem rangeInside,
          List.getElem?_eq_getElem sourceIndex, List.getElem_range] at selected
        have actionEq := Option.some.inj selected
        rw [← semantic, choicesEq] at actionEq
        calc
          _ = (Setup.proposalRecoveryJoint joint who).map (fun move => move.action) :=
            actionEq
          _ = _ := by
            change ((joint who).map (·.semantic)).map (·.action) = _
            rw [Option.map_map]
            rfl
      have nextPosition : (prior.extend joint legal moved).length - q.trace.length =
          position + 1 := by
        have lower := earlier.length_le
        simp only [Trace.length]
        dsimp only [position]
        omega
      have observationStep : ∀ candidate,
          sourceObservationAt (position + 1) candidate = true ↔
            sourceObservationAt position candidate = true ∧
              block.block.wordAction who position candidate =
                block.block.wordAction who position (referenceWord.view who) := by
        intro candidate
        simp only [sourceObservationAt, decide_eq_true_eq]
        constructor
        · intro next
          exact ⟨fun index bounded => next index (by omega), next position (by omega)⟩
        · rintro ⟨previous, same⟩ index bounded
          by_cases earlier : index < position
          · exact previous index earlier
          · have equal : index = position := by omega
            simpa only [equal] using same
      let newer := match joint who with
        | none => records
        | some action => (setup.proposalRecoveryModel.infoOf who prior, action) :: records
      refine ⟨newer, ?_, ?_⟩
      · rw [InfoSignals.ownPlay_extend, ownRecords]
        cases selected : joint who <;> simp only [newer, selected, List.cons_append]
      · rw [nextPosition]
        cases selected : joint who with
        | none =>
            have notOwn : actor ≠ who := by
              intro same
              have active : setup.proposalRecoveryProtocol.active (some current) who :=
                ⟨same ▸ currentActor, beforeSurvives⟩
              have permitted := setup.proposalRecoveryProtocol.legalOption_of_legal legal who
              rw [selected] at permitted
              exact permitted active
            have unowned : eventOwner? (block.block.prepend block.suffix) index ≠
                some who := by
              rw [eventOwner?_eq_actor, EventGraph.actor?_of_outputLayout_binding
                (toEventGraph (block.block.prepend block.suffix)) layout]
              exact fun same => notOwn (Option.some.inj same)
            have silent : ∀ candidate, block.block.wordAction who position candidate =
                none := fun candidate => compiledCommitPrefix_wordAction_none_of_unowned
                  block.block block.suffix who index unowned candidate
            have sameObservation : sourceObservationAt (position + 1) =
                sourceObservationAt position := by
              funext candidate
              apply Bool.eq_iff_iff.mpr
              rw [observationStep, silent candidate, silent (referenceWord.view who)]
              exact ⟨And.left, fun previous => ⟨previous, rfl⟩⟩
            rw [sameObservation, mass]
            simp only [newer, selected]
        | some move =>
            have permitted := setup.proposalRecoveryProtocol.legalOption_of_legal legal who
            rw [selected] at permitted
            have sameOwner : actor = who := Option.some.inj
              (currentActor.symm.trans permitted.1.1)
            subst actor
            have properMove := wholeProper _ (List.getElem_mem sourceIndex) who
              move.semantic (by
                rw [← semantic, choicesEq]
                change (joint who).map (·.semantic) = some move.semantic
                rw [selected]
                rfl)
            have law := sourcePositionLaw position positionInside named ty shape namedRank
              current prior (beforeG.trans gToTarget) atRank
                (beforeGeneration.trans (congrArg (fun controls => controls.2.1)
                  (cursor.controls blockPositive))) beforeSurvives
            have increment := observation_fiber_mass ownWordLaw
              (sourceObservationAt position) (sourceObservationAt (position + 1))
                (block.block.wordAction who position)
                  (block.block.wordAction who position (referenceWord.view who))
                    (referencePresent position) (fun candidate _present =>
                      observationStep candidate)
            rw [increment, mass, law, referenceAction]
            have atom := sourceReplay_ordinary_commitment_action_atom setup values who
              current prior committing
              (setup.proposalRecoveryModel.choicesOfLegal prior ⟨joint, legal⟩ who) (by
                intro candidate chosen
                change (joint who).map (·.semantic) = some candidate at chosen
                rw [selected, Option.map_some, Option.some.injEq] at chosen
                exact chosen ▸ properMove)
            change ((ordinary who (setup.proposalRecoveryModel.infoOf who prior)).map
                (fun choice => choice.val.map (fun move => move.semantic.action)))
                  ((joint who).map (fun move => move.semantic.action)) = _ at atom
            rw [atom]
            have rawAtom := pmf_map_apply_of_injective
              (ordinary who (setup.proposalRecoveryModel.infoOf who prior))
                Subtype.val_injective
                  (setup.proposalRecoveryModel.choicesOfLegal prior ⟨joint, legal⟩ who)
            change ((ordinary who (setup.proposalRecoveryModel.infoOf who prior)).map
              Subtype.val) (joint who) = _ at rawAtom
            rw [selected] at rawAtom
            simp only [newer, selected, InformationModel.ownPlayReachProbability]
            rw [rawAtom, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
            exact mul_comm _ _

/-- The original posterior mixture at one supported replay has the literal
source cut/completion weight. Only its focal and foreign issued masses are
canceled; the canonical historical closed mass is disintegrated without division. -/
theorem sourceRawReplay_annotation_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (who : Player) (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (acting : reference.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who
      (reference.execution.recall who)
      (reference.execution.observe nativeApplication who) event payload)
    (good : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner ⟨some reference, referenceTrace⟩)
    (entry : NativeBindingEntry setup implementation operational reference referenceTrace
      who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who
        (entry.canonicalCut setup values implementation operational fullValues reference
          referenceTrace who acting event payload clean good).trace)
    (sourceGood : setup.proposalRecoveryForeignGood who g)
    (sourceChoice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, sourceChoice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (supported : (⟨some targetCurrent, targetTrace⟩ :
      setup.proposalRecoveryProtocol.History) ∈
        (sourceForcedBlock setup values who g sourceChoice).support)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        nativeInitial implementation.horizon implementation.scheduler values
          ⟨nativeBad, scale, scale, scale⟩)
    (site : (nativeModel).InformationSite who)
    (referenceInformation : (nativeModel).infoOf who referenceTrace = site.1)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site
      (reference.execution.recall who) (reference.execution.observe nativeApplication who)
        event payload clean.binding)
    (gInfo : setup.proposalRecoveryModel.infoOf who g.trace = source.site.1)
    (value : L.Val payload)
    (encoded : sourceChoice = gInfo.symm ▸ source.encode value)
    (law : SourceRawReplayLaw (setup := setup) (values := values)
      (implementation := implementation) scale who ⟨some targetCurrent, targetTrace⟩ reference
        ⟨some reference, referenceTrace⟩)
    (script : List (RawReplayChoice setup implementation))
    (member : script ∈ law.choices.support)
    (actual : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationHistory who
        (((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).infoOf who referenceTrace))
    (replayed : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
      reference ⟨some reference, referenceTrace⟩ script = some actual.val)
    (nativePositive : (nativeModel).historyReachWeight nativeProfile actual.val ≠ 0)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (tapePositive : prefixTapeLaw setup implementation actual.val tape ≠ 0)
    (actualGood : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner actual.val)
    (actualAlive : actual.val.state.elim True (fun control =>
      who ∉ control.execution.application.current.excluded))
    (admitted : bindingAdmissionBit setup implementation who event actual.val tape = true)
    (q : setup.proposalRecoveryProtocol.History)
    (qKept : TracePrefix q.trace g.trace)
    (qDepth : q.trace.length =
      (canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩).trace.length)
    (sameKey : setup.proposalRecoveryClosedKey who
        (canonicalSource setup implementation operational actual.val) =
      setup.proposalRecoveryClosedKey who q)
    (pairLaw : ForeignPosteriorCutPair setup values implementation) :
    ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
        (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who source.anchor.trace)) *
      (setup.proposalRecoveryForeignProducts values scale sourceBad scale who
        source.anchor.trace).1 *
      (∑' candidate : setup.proposalRecoveryProtocol.History,
        ∑' word : SourceProgram.History Player L,
          annotatedPrefixWeight setup values implementation operational sourceProfile nativeProfile
              who actual.val tape candidate word *
            (if bindingAdmissionBit setup implementation who event actual.val tape then 1 else 0) *
            sourceForcedBlockJoint setup values implementation who actual.val event payload
              candidate word value (g, ⟨some targetCurrent, targetTrace⟩)) =
      (implementation.prior tape *
          ENNReal.ofReal ((nativeModel).ownPlayReachProbability (nativeProfile who)
            ((nativeModel).ownPlay who actual.val.trace)) *
          mechanicalPathAtom setup implementation ⟨nativeBad, scale, scale, scale⟩ who tape
            actual.val.trace) *
        (setup.proposalRecoveryModel.historyReachWeight sourceProfile g *
          sourceForcedBlock setup values who g sourceChoice ⟨some targetCurrent, targetTrace⟩) *
        law.choices script := by
  classical
  have nativeAtom := sourceRawReplay_native_atom setup values implementation operational
    fullValues who reference
      referenceTrace acting event payload clean good entry g sameInfo sourceGood sourceChoice
        properChoice targetCurrent targetTrace supported scale sourceBad nativeBad scalePositive
          scaleBelow sourceBadPositive sourceBadBelow nativeBadPositive nativeBadBelow sourceProfile
            sourcePrescribed nativeProfile nativePrescribed site referenceInformation source gInfo
              value encoded law script member actual replayed nativePositive tape tapePositive
                actualGood actualAlive admitted q qKept qDepth sameKey
  have issuedMass := sourceRawReplay_current_issued_mass setup values implementation operational
    fullValues who reference referenceTrace acting event payload clean good entry g sameInfo
      sourceGood sourceChoice properChoice targetCurrent targetTrace supported scale sourceBad
        nativeBad scalePositive scaleBelow sourceBadPositive sourceBadBelow nativeBadPositive
          nativeBadBelow sourceProfile sourcePrescribed nativeProfile nativePrescribed site
            referenceInformation source gInfo value encoded law script member actual replayed
              nativePositive actualGood actualAlive q qKept qDepth sameKey
  obtain ⟨entryInformation, _entryKey⟩ := sourceRawReplay_closed_key setup values implementation
    operational fullValues who reference referenceTrace acting event payload clean good entry g
      sameInfo sourceGood sourceChoice properChoice targetCurrent targetTrace supported scale law
        script member actual replayed q qKept qDepth
  let canonical := canonicalSource setup implementation operational actual.val
  have canonicalGood : setup.proposalRecoveryForeignGood who canonical :=
    canonicalSource_foreignGood setup implementation operational who actual.val actualGood
  have canonicalPositive : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      canonical ≠ 0 :=
    (prescribed_source_history_positive setup values scale sourceBad scalePositive scaleBelow
      sourceBadPositive sourceBadBelow fullValues sourceProfile sourcePrescribed canonical).ne'
  have closedFactors := (prescribed_source_closed_products setup values scale
    sourceBad operational.wellFormed sourceProfile sourcePrescribed who canonical canonicalGood).1
  have disintegration : setup.proposalRecoveryClosedMass sourceProfile who canonical *
      setup.proposalRecoveryClosedLaw sourceProfile who canonical q =
        setup.proposalRecoveryModel.historyReachWeight sourceProfile q := by
    rw [setup.proposalRecoveryClosedMass_mul_law, ite_eq_left sameKey.symm]
  obtain ⟨word, annotation⟩ := sourceRawReplay_forward_annotation setup values implementation
    operational fullValues who reference
      referenceTrace acting event payload clean good entry g sameInfo sourceGood sourceChoice
        properChoice targetCurrent targetTrace supported scale sourceBad nativeBad scalePositive
          scaleBelow sourceBadPositive sourceBadBelow nativeBadPositive nativeBadBelow sourceProfile
            sourcePrescribed nativeProfile nativePrescribed site referenceInformation source gInfo
              value encoded law script member actual replayed nativePositive tape tapePositive
                actualGood actualAlive admitted q qKept qDepth sameKey
  have prefixPositive := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp annotation).1).1
  obtain ⟨image, imageReplay, related, _mechanical, _good⟩ := law.replayed script member
  have sameActual : image = actual.val := Option.some.inj (imageReplay.symm.trans replayed)
  rw [sameActual] at related
  rcases actual with ⟨⟨state, trace⟩, information⟩
  cases state with
  | none => simp only [bindingAdmissionBit, Bool.false_eq_true] at admitted
  | some control =>
    obtain ⟨_remaining, actor, _execution, recalled, observed⟩ := related
    have actualActing : control.actor = some who := actor.trans acting
    have actualClean : CleanUnsentBinding setup implementation who
        (control.execution.recall who) (control.execution.observe nativeApplication who)
          event payload := by
      rw [recalled, observed]
      exact clean
    have nativeInformation : (nativeModel).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
      change ((nativeMenu).signals nativeInitial implementation.horizon
        implementation.scheduler).infoOf who trace = _
      simpa only [ReactiveApplication.observe, actualActing, ↓reduceIte] using
        (nativeMenu).info nativeInitial implementation.horizon implementation.scheduler who trace
    obtain ⟨completionControl, completionTrace, completionEq, completion⟩ :=
      sourceRawReplay_ordinary_completion setup values implementation operational fullValues who
        reference referenceTrace acting event payload clean good entry g sameInfo sourceGood
          sourceChoice properChoice targetCurrent targetTrace supported scale sourceBad nativeBad
            scalePositive scaleBelow sourceBadPositive sourceBadBelow nativeBadPositive
              nativeBadBelow sourceProfile sourcePrescribed nativeProfile nativePrescribed site
                referenceInformation source gInfo value encoded law script member
                  ⟨⟨some control, trace⟩, information⟩ replayed nativePositive actualGood
                    actualAlive q qKept qDepth sameKey
    have completionControlEq : control = completionControl :=
      Option.some.inj (congrArg History.state completionEq)
    subst completionControl
    have completionTraceEq : trace = completionTrace := eq_of_heq (History.mk.inj completionEq).2
    subst completionTrace
    obtain ⟨phase, cursor, qAtCursor, blockPositive, cursorEmbedding, cursorLift, cursorViews,
      ordinarySupport, referenceWord, referenceWordSupport, issuedLedgers, finished, attempt,
      finishedPoint, finishedExcluded, finishedWord, finishedLabels, structuralWord⟩ := completion
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let block := SourceProgram.commitPhase checkpoint.residual.tail
    let low := control.execution.application.attempt.phase
    let high := low + block.block.length
    let offset := event.val - low
    let ordinary := sourceUnflaggedStrategy setup values
    let ordinaryPair := (setup.proposalRecoveryModel.runBehavioralFrom ordinary offset q).bind
      fun before => (setup.proposalRecoveryModel.runBehavioralFrom ordinary
        (block.block.length - offset) before).map (Prod.mk before)
    let completedAt := fun history : setup.proposalRecoveryProtocol.History =>
      history.state.bind fun current => residualEntry? block.suffix
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) current.point
    let observed := fun point : setup.proposalRecoveryProtocol.History ×
        setup.proposalRecoveryProtocol.History =>
      match completedAt point.2 with
      | none => false
      | some finished => decide (
          issuedLedger setup implementation block.block low control high who (finished.view who) ∧
          block.block.wordAction who offset (finished.view who) =
            decodeEventAction setup.program event
              (cast (congrArg EventField.Action actualClean.binding.symm) (.success value)) ∧
          ∀ owner, owner ≠ who → issuedLedger setup implementation block.block low control high
            owner (finished.view owner))
    let ownObserved := fun point : setup.proposalRecoveryProtocol.History ×
        setup.proposalRecoveryProtocol.History =>
      match completedAt point.2 with
      | none => false
      | some finished => decide (
          issuedLedger setup implementation block.block low control high who (finished.view who) ∧
          block.block.wordAction who offset (finished.view who) =
            decodeEventAction setup.program event
              (cast (congrArg EventField.Action actualClean.binding.symm) (.success value)))
    let foreign := ordinaryForeignJoint setup values implementation operational who
      ⟨some control, trace⟩ q
    let ownMass := (ordinaryPair.map ownObserved) true
    let beta := ordinaryPair (g, ⟨some targetCurrent, targetTrace⟩)
    have mixture := pairLaw operational fullValues sourceProfile nativeProfile who control trace
      tape q word canonicalPositive prefixPositive (control.execution.recall who)
        (control.execution.observe nativeApplication who) nativeInformation event payload
          actualClean admitted value
    have mixtureAtoms := foreign_posterior_cut_pair_atoms setup values implementation operational
      fullValues sourceProfile nativeProfile who control trace tape q word canonicalPositive
        prefixPositive (control.execution.recall who)
          (control.execution.observe nativeApplication who) nativeInformation event payload
            actualClean admitted value
    have foreignPresent : true ∈ (foreign.map Prod.snd).support := mixture.2.1
    have foreignPositive : (foreign.map Prod.snd) true ≠ 0 :=
      (PMF.mem_support_iff ..).mp foreignPresent
    have observedPresent : true ∈ (ordinaryPair.map observed).support := mixture.1
    have ownPositive : ownMass ≠ 0 :=
      (PMF.mem_support_iff ..).mp mixture.2.2.2.1
    have ownFinite : ownMass ≠ ⊤ := PMF.apply_ne_top _ _
    have posteriorMixture : fiberPosterior ordinaryPair observed true =
        (fiberPosterior foreign Prod.snd true).bind (fun drawn =>
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
            event payload q drawn.1 value) := mixture.2.2.1
    have observedMass : (ordinaryPair.map observed) true =
        ownMass * (foreign.map Prod.snd) true := mixtureAtoms.2.2.2.2.2.1
    let coefficient := implementation.prior tape *
      ENNReal.ofReal ((nativeModel).ownPlayReachProbability (nativeProfile who)
        ((nativeModel).ownPlay who trace)) *
      mechanicalPathAtom setup implementation ⟨nativeBad, scale, scale, scale⟩ who tape trace
    let historical := (setup.proposalRecoveryForeignProducts values scale sourceBad scale who
      canonical.trace).2.1
    let issued := sourceReplayCurrentIssuedProduct setup values implementation who
      ⟨some control, trace⟩
    have issuedValue : issued = (foreign.map Prod.snd) true := issuedMass.symm
    have issuedFinite : issued ≠ ⊤ := by
      rw [issuedValue]
      exact PMF.apply_ne_top _ _
    have historicalFinite : historical ≠ ⊤ :=
      (setup.proposalRecoveryForeignProducts_finite values scale sourceBad scale who
        canonical.trace).2.1
    have pathFinite := sourceReplay_mechanical_path_finite setup implementation
      ⟨nativeBad, scale, scale, scale⟩ who tape trace
    have coefficientFinite : coefficient ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
        ENNReal.ofReal_ne_top) pathFinite
    have rightFinite : coefficient * ENNReal.ofReal canonical.trace.transitionMass * historical *
        issued * law.choices script ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top coefficientFinite ENNReal.ofReal_ne_top) historicalFinite)
          issuedFinite) (PMF.apply_ne_top _ _)
    have nativeScalar : (nativeModel).historyReachWeight nativeProfile ⟨some control, trace⟩ *
        prefixTapeLaw setup implementation ⟨some control, trace⟩ tape =
      coefficient * ENNReal.ofReal canonical.trace.transitionMass * historical * issued *
        law.choices script := by
      apply (ENNReal.toReal_eq_toReal_iff'
        (ENNReal.mul_ne_top ((nativeModel).historyReachWeight_ne_top nativeProfile _)
          (PMF.apply_ne_top _ _)) rightFinite).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal canonical.trace.transitionMass_pos.le]
      rw [nativeAtom]
      simp only [coefficient, historical, issued, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal ((nativeModel).ownPlayReachProbability_nonneg _ _)]
      ring
    let actualHistory : (nativeModel).InformationHistory who site.1 :=
      ⟨⟨some control, trace⟩, information.trans referenceInformation⟩
    have siteEq : site.1 = some (control.execution.recall who,
        control.execution.observe nativeApplication who) :=
      (information.trans referenceInformation).symm.trans nativeInformation
    have uniqueEntry (candidate : setup.proposalRecoveryProtocol.History)
        (otherWord : SourceProgram.History Player L)
        (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
            nativeProfile who ⟨some control, trace⟩ tape candidate otherWord *
          (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
            then 1 else 0) *
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩ event
            payload candidate otherWord value (g, ⟨some targetCurrent, targetTrace⟩) ≠ 0) :
        candidate = q := by
      have equal := positive_original_annotated_entry_eq setup values implementation operational
        fullValues sourceProfile nativeProfile who site (control.execution.recall who)
          (control.execution.observe nativeApplication who) siteEq event payload actualClean value
            (fun _ => actualHistory) (fun _ => tape)
            (fun side => if side then q else candidate)
            (fun side => if side then word else otherWord) g ⟨some targetCurrent, targetTrace⟩
            (fun _ => canonicalPositive) (by
              intro side
              cases side with
              | false => exact positive
              | true => exact annotation)
      exact equal
    have entryReduction :
        (∑' candidate : setup.proposalRecoveryProtocol.History,
          ∑' otherWord : SourceProgram.History Player L,
            annotatedPrefixWeight setup values implementation operational sourceProfile
                nativeProfile who ⟨some control, trace⟩ tape candidate otherWord *
              (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
                then 1 else 0) *
              sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩ event
                payload candidate otherWord value (g, ⟨some targetCurrent, targetTrace⟩)) =
          ∑' otherWord : SourceProgram.History Player L,
            annotatedPrefixWeight setup values implementation operational sourceProfile
                nativeProfile who ⟨some control, trace⟩ tape q otherWord *
              (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
                then 1 else 0) *
              sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩ event
                payload q otherWord value (g, ⟨some targetCurrent, targetTrace⟩) := by
      apply tsum_eq_single q
      intro candidate different
      apply ENNReal.tsum_eq_zero.mpr
      intro otherWord
      by_contra positive
      exact different (uniqueEntry candidate otherWord positive)
    rw [entryReduction]
    let forced := fun drawn : SourceProgram.History Player L =>
      sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩ event payload
        q drawn value
    have wordMixture :
        (∑' drawn : SourceProgram.History Player L,
          ((fiberPosterior foreign Prod.snd true).map Prod.fst) drawn *
            forced drawn (g, ⟨some targetCurrent, targetTrace⟩)) =
          fiberPosterior ordinaryPair observed true (g, ⟨some targetCurrent, targetTrace⟩) := by
      calc
        _ = (((fiberPosterior foreign Prod.snd true).map Prod.fst).bind forced)
            (g, ⟨some targetCurrent, targetTrace⟩) := (PMF.bind_apply ..).symm
        _ = ((fiberPosterior foreign Prod.snd true).bind (fun drawn => forced drawn.1))
            (g, ⟨some targetCurrent, targetTrace⟩) :=
          congrArg (fun distribution : PMF (setup.proposalRecoveryProtocol.History ×
              setup.proposalRecoveryProtocol.History) =>
                distribution (g, ⟨some targetCurrent, targetTrace⟩))
            (PMF.bind_map (fiberPosterior foreign Prod.snd true) Prod.fst forced)
        _ = _ := congrArg
          (fun distribution => distribution (g, ⟨some targetCurrent, targetTrace⟩))
          posteriorMixture.symm
    have actualPair := positive_original_annotated_pair setup values implementation operational
      fullValues sourceProfile nativeProfile who control trace tape q g
        ⟨some targetCurrent, targetTrace⟩ word canonicalPositive (control.execution.recall who)
          (control.execution.observe nativeApplication who) nativeInformation event payload
            actualClean value annotation
    have observedTrue : observed (g, ⟨some targetCurrent, targetTrace⟩) = true :=
      actualPair.2.2.2.1
    have posteriorAtom : fiberPosterior ordinaryPair observed true
        (g, ⟨some targetCurrent, targetTrace⟩) =
      beta * (ownMass * issued)⁻¹ := by
      rw [fiberPosterior_apply ordinaryPair observed true observedPresent,
        Set.indicator_of_mem (show (g, ⟨some targetCurrent, targetTrace⟩) ∈
          {point | observed point = true} from observedTrue)]
      rw [observedMass, issuedMass]
    have eachWord (drawn : SourceProgram.History Player L) :
        annotatedPrefixWeight setup values implementation operational sourceProfile nativeProfile
            who ⟨some control, trace⟩ tape q drawn *
          (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
            then 1 else 0) * forced drawn (g, ⟨some targetCurrent, targetTrace⟩) =
        ((nativeModel).historyReachWeight nativeProfile ⟨some control, trace⟩ *
          prefixTapeLaw setup implementation ⟨some control, trace⟩ tape *
          setup.proposalRecoveryClosedLaw sourceProfile who canonical q) *
          (((fiberPosterior foreign Prod.snd true).map Prod.fst) drawn *
            forced drawn (g, ⟨some targetCurrent, targetTrace⟩)) := by
      dsimp only [annotatedPrefixWeight]
      rw [ite_eq_left ⟨actualGood, actualAlive⟩, ite_eq_right foreignPositive, admitted]
      simp only [↓reduceIte, mul_one]
      ring
    have wordSum :
        (∑' drawn : SourceProgram.History Player L,
          annotatedPrefixWeight setup values implementation operational sourceProfile nativeProfile
              who ⟨some control, trace⟩ tape q drawn *
            (if bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape
              then 1 else 0) * forced drawn (g, ⟨some targetCurrent, targetTrace⟩)) =
        ((nativeModel).historyReachWeight nativeProfile ⟨some control, trace⟩ *
          prefixTapeLaw setup implementation ⟨some control, trace⟩ tape *
          setup.proposalRecoveryClosedLaw sourceProfile who canonical q) *
          (beta * (ownMass * issued)⁻¹) := by
      simp_rw [eachWord]
      rw [ENNReal.tsum_mul_left, wordMixture, posteriorAtom]
    rw [wordSum]
    let anchorOwn := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
      (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who source.anchor.trace))
    let anchorClasses := (setup.proposalRecoveryForeignProducts values scale sourceBad scale who
      source.anchor.trace).1
    let canonicalOwn := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
      (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who canonical.trace))
    let canonicalClasses := (setup.proposalRecoveryForeignProducts values scale sourceBad scale who
      canonical.trace).1
    let sourcePrefix := setup.proposalRecoveryModel.runBehavioralFrom sourceProfile
      (g.trace.length - q.trace.length) q g
    let sourceTail := sourceForcedBlock setup values who g sourceChoice
      ⟨some targetCurrent, targetTrace⟩
    have pairAtom : beta =
        setup.proposalRecoveryModel.runBehavioralFrom ordinary offset q g *
          setup.proposalRecoveryModel.runBehavioralFrom ordinary
            (block.block.length - offset) g ⟨some targetCurrent, targetTrace⟩ := by
      change bindPairLaw
        (setup.proposalRecoveryModel.runBehavioralFrom ordinary offset q)
        (setup.proposalRecoveryModel.runBehavioralFrom ordinary (block.block.length - offset))
          (g, ⟨some targetCurrent, targetTrace⟩) = _
      rw [bindPairLaw_apply]
    have sourcePrefixReach : setup.proposalRecoveryModel.historyReachWeight sourceProfile g =
        setup.proposalRecoveryModel.historyReachWeight sourceProfile q * sourcePrefix := by
      have depth := qKept.length_le
      change setup.proposalRecoveryModel.runBehavioralFrom sourceProfile g.trace.length
          setup.proposalRecoveryProtocol.initHistory g = _
      rw [show g.trace.length = q.trace.length + (g.trace.length - q.trace.length) by omega,
        setup.proposalRecoveryModel.runBehavioralFrom_add, PMF.bind_apply]
      apply tsum_eq_single q
      intro middle different
      by_cases initial : middle ∈ (setup.proposalRecoveryModel.runBehavioral sourceProfile
          q.trace.length).support
      · by_cases onward : g ∈ (setup.proposalRecoveryModel.runBehavioralFrom sourceProfile
            (g.trace.length - q.trace.length) middle).support
        · exact (different (setup.proposalRecoveryModel.eq_of_runBehavioral_support_and_cone
            sourceProfile q middle g initial onward ⟨_, qKept.reachesWithin⟩)).elim
        · rw [(PMF.apply_eq_zero_iff _ _).mpr onward, mul_zero]
      · have initialZero : (setup.proposalRecoveryModel.runBehavioralFrom sourceProfile
            q.trace.length setup.proposalRecoveryProtocol.initHistory) middle = 0 :=
          (PMF.apply_eq_zero_iff _ _).mpr initial
        rw [initialZero, zero_mul]
    have ordinaryRows : anchorOwn * anchorClasses * beta =
        canonicalOwn * canonicalClasses * sourcePrefix * ownMass * sourceTail := by
      have qGood : setup.proposalRecoveryForeignGood who q := by
        have bit := congrArg (fun key => key.2.2.2) sameKey.symm
        change decide (setup.proposalRecoveryForeignGood who q) =
          decide (setup.proposalRecoveryForeignGood who canonical) at bit
        apply of_decide_eq_true
        rw [bit]
        exact decide_eq_true canonicalGood
      change (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) = q
        at qAtCursor
      change (⟨some targetCurrent, targetTrace⟩ : setup.proposalRecoveryProtocol.History) ∈
        (setup.proposalRecoveryModel.runBehavioralFrom ordinary block.block.length q).support
          at ordinarySupport
      have qLength : q.trace.length = cursor.trace.length :=
        congrArg (fun history : setup.proposalRecoveryProtocol.History => history.trace.length)
          qAtCursor.symm
      have cursorPrefix {state : setup.proposalRecoveryProtocol.State}
          (prior : setup.proposalRecoveryProtocol.Trace state)
          (kept : TracePrefix q.trace prior) : TracePrefix cursor.trace prior := by
        change TracePrefix (⟨some cursor.current, cursor.trace⟩ :
          setup.proposalRecoveryProtocol.History).trace prior
        rw [qAtCursor]
        exact kept
      have wholeSupport : (⟨some targetCurrent, targetTrace⟩ :
          setup.proposalRecoveryProtocol.History) ∈
          (setup.proposalRecoveryModel.runBehavioralFrom ordinary block.block.length
            ⟨some cursor.current, cursor.trace⟩).support := by
        rw [qAtCursor]
        exact ordinarySupport
      have ownAtEntry : canonicalOwn = ENNReal.ofReal
          (setup.proposalRecoveryModel.ownPlayReachProbability (sourceProfile who)
            (setup.proposalRecoveryModel.ownPlay who q.trace)) :=
        congrArg (fun plays => ENNReal.ofReal
          (setup.proposalRecoveryModel.ownPlayReachProbability (sourceProfile who) plays))
          (setup.proposalRecoveryModel_perfectRecall who canonical.trace q.trace entryInformation)
      have classesAtEntry : canonicalClasses =
          (setup.proposalRecoveryForeignProducts values scale sourceBad scale who q.trace).1 :=
        setup.proposalRecovery_foreign_class_eq_of_information values scale sourceBad scale
          scalePositive scaleBelow sourceBadBelow scalePositive scaleBelow operational.wellFormed
            who canonical.trace q.trace entryInformation canonicalGood qGood
      have ownAtG : anchorOwn = ENNReal.ofReal
          (setup.proposalRecoveryModel.ownPlayReachProbability (sourceProfile who)
            (setup.proposalRecoveryModel.ownPlay who g.trace)) :=
        congrArg (fun plays => ENNReal.ofReal
          (setup.proposalRecoveryModel.ownPlayReachProbability (sourceProfile who) plays))
          (setup.proposalRecoveryModel_perfectRecall who source.anchor.trace g.trace
            (source.anchorInfo.trans gInfo.symm))
      have classesAtG : anchorClasses =
          (setup.proposalRecoveryForeignProducts values scale sourceBad scale who g.trace).1 :=
        setup.proposalRecovery_foreign_class_eq_of_information values scale sourceBad scale
          scalePositive scaleBelow sourceBadBelow scalePositive scaleBelow operational.wellFormed
            who source.anchor.trace g.trace (source.anchorInfo.trans gInfo.symm)
              source.anchorGood sourceGood
      have geometry := positive_original_annotated_geometry setup values implementation
        operational fullValues sourceProfile nativeProfile who control trace actualActing tape q g
          ⟨some targetCurrent, targetTrace⟩ word canonicalPositive event payload actualClean value
            annotation
      have gDepth : g.trace.length = q.trace.length + offset := geometry.2.2.2.1
      have targetDepth : targetTrace.length = q.trace.length + block.block.length :=
        geometry.2.2.2.2
      have pairSupported : (g, ⟨some targetCurrent, targetTrace⟩) ∈ ordinaryPair.support :=
        actualPair.2.2.1
      obtain ⟨middle, prefixSupported, onward⟩ := (PMF.mem_support_bind_iff ..).mp pairSupported
      obtain ⟨last, tailSupported, pairEq⟩ := (PMF.mem_support_map_iff ..).mp onward
      have middleEq : middle = g := congrArg Prod.fst pairEq
      have lastEq : last = ⟨some targetCurrent, targetTrace⟩ := congrArg Prod.snd pairEq
      subst middle
      subst last
      obtain ⟨actualEntry⟩ := qualified_binding_entry setup implementation operational control trace
        who event payload actualClean actualGood
      obtain ⟨_baseCursor, _canonical, _cursorOffset, _source, _refs, _embedding, _lift,
        _views, _config, size⟩ := selected_binding_cursor setup implementation operational who
          control trace event actualEntry true
      have phaseLow : actualEntry.phase.low = low := by
        obtain ⟨rest, installed⟩ := List.head?_eq_some_iff.mp actualEntry.installed
        simp only [low, PhaseRuntimeState.attempt, installed, List.head?_cons,
          Option.map_some, Option.getD_some]
      have offsetInside : offset < block.block.length := by
        have bounds := (actualEntry.phase.mem_events event).mp actualEntry.inside
        change block.block.length = actualEntry.phase.high - actualEntry.phase.low at size
        dsimp only [offset]
        rw [phaseLow] at size bounds
        omega
      have qInitialized : 0 < q.trace.length := by
        rw [qLength]
        have positive {state : setup.proposalRecoveryProtocol.State}
            (path : setup.proposalRecoveryProtocol.Trace state) (initialized : state ≠ none) :
            0 < path.length := by
          cases path with
          | start => exact (initialized rfl).elim
          | extend earlier choices permitted reached => simp only [Trace.length]; omega
        exact positive cursor.trace (by intro impossible; cases impossible)
      have initialCommitting : ProtocolState.atCommit setup.program cursor.current.point =
        true := by
        have entryCommit {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
            (segment : SourceProgram.CommitPrefix Γ O Δ P)
            (suffix : SourceProgram Player L Δ P) (entry : SourceProgram.Config Player L Γ)
            (positive : 0 < segment.length) :
            ProtocolState.atCommit (segment.prepend suffix)
              (ProtocolState.entry (segment.prepend suffix) entry) = true := by
          cases segment with
          | nil => cases Nat.not_lt_zero _ positive
          | commit => rfl
        rw [cursor.point, cursor.origin.atCommit_lift]
        exact entryCommit block.block block.suffix cursor.source blockPositive
      have wholeWindow : block.block.length +
          ProtocolState.commitEnd setup.program cursor.current.point ≤
            ProtocolState.remaining setup.program cursor.current.point := by
        rw [cursor.point, cursor.origin.commitEnd_lift, cursor.origin.remaining_lift]
        exact block.block.length_le_commit_window block.suffix cursor.source
      obtain ⟨wholeFinished, wholeCurrent, wholeTrace, wholeAttempt, wholeHistory,
        _wholePoint, _wholeExcluded, _wholeEntry, _wholeGeneration, wholeWord,
        _wholeLabels, wholeProper⟩ := proposalRecovery_ordinary_commit_block_support setup values
          block.block block.suffix cursor.lift cursor.origin cursor.source cursor.current
            cursor.trace cursor.point (cursor.excluded.trans cursor.entryExcluded.symm)
              ⟨some targetCurrent, targetTrace⟩ wholeSupport
      have literalWord : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetTrace) =
          wholeAttempt.joints.reverse ++ setup.recoveryJointRecall
            (setup.proposalRecoveryEraseTrace cursor.trace) := by
        have same := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace history.trace)) wholeHistory
        exact same.trans wholeWord
      have rows : ∀ (before : setup.proposalRecoveryProtocol.History)
          (joint : Player → Option (ProposalRecoveryMove Player L))
          (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
          (after : setup.proposalRecoveryProtocol.State)
          (moved : after ∈ (setup.proposalRecoveryProtocol.step before.state
            ⟨joint, legal⟩).support),
          TracePrefix q.trace before.trace →
          TracePrefix (before.trace.extend joint legal moved) g.trace →
          ∃ current, before.state = some current ∧
            ProtocolState.atCommit setup.program current.point = true ∧
            ∀ owner move, owner ≠ who → joint owner = some move →
              move.semantic.missing = false ∧ ¬ move.semantic.action.IsFailure := by
        intro before joint legal after moved earlier retained
        have beforeDepth := retained.length_le
        have afterBound : before.trace.length < q.trace.length + block.block.length := by
          simp only [Trace.length] at beforeDepth
          omega
        have erasedEarlier : TracePrefix (setup.proposalRecoveryEraseTrace cursor.trace)
            (setup.proposalRecoveryEraseTrace before.trace) := by
          apply setup.proposalRecoveryEraseTrace_prefix
          exact cursorPrefix before.trace earlier
        obtain ⟨current, stateEq, committing, _endpoint, _balance⟩ :=
          setup.commitRecovery_prefix_inside_commit cursor.current
            (setup.proposalRecoveryEraseTrace cursor.trace) initialCommitting
            (setup.proposalRecoveryEraseTrace before.trace) erasedEarlier (by
              simp only [setup.proposalRecoveryEraseTrace_length]
              have qLength := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
                history.trace.length) qAtCursor
              omega)
        cases sourceState : before.state with
        | none =>
            rw [sourceState] at stateEq
            cases stateEq
        | some sourceCurrent =>
            have controls : sourceCurrent = current :=
              Option.some.inj (sourceState.symm.trans stateEq)
            subst current
            refine ⟨sourceCurrent, rfl, committing, ?_⟩
            intro owner move _different selected
            let slot := before.trace.length - cursor.trace.length
            have inside : slot < wholeAttempt.joints.length := by
              rw [wholeAttempt.joints_length]
              have qLength := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
                history.trace.length) qAtCursor
              dsimp only [slot]
              omega
            obtain ⟨firstState, lastState, firstPrior, choices, permitted, reached,
              firstKept, firstDepth, semantic, _firstAddress, _lastAddress⟩ :=
                source_instruction_chunk_row setup cursor.trace targetTrace (by
                  simpa only [qLength] using qInitialized) wholeAttempt.joints
                    literalWord slot inside
            have gKept := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin ordinary
              (block.block.length - offset) g ⟨some targetCurrent, targetTrace⟩
                tailSupported).tracePrefix
            have sameRow := firstKept.eq_of_same_length (retained.trans gKept) (by
              have lower := earlier.length_le
              have qLength := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
                history.trace.length) qAtCursor
              simp only [Trace.length]
              dsimp only [slot] at firstDepth
              omega)
            have choicesEq : choices = joint := Option.some.inj (by
              have same := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
                (setup.proposalRecoveryJointRecall history.trace).head?) sameRow
              simpa only [Setup.proposalRecoveryJointRecall, List.head?_cons] using same)
            apply wholeProper _ (List.getElem_mem inside) owner move.semantic
            rw [← semantic, choicesEq]
            change (joint owner).map (·.semantic) = some move.semantic
            rw [selected]
            rfl
      obtain ⟨newOwn, ownSuffix, prefixCalibration⟩ :=
        sourceReplay_commit_prefix_calibration setup values scale sourceBad who sourceProfile
          sourcePrescribed q g qKept rows
      obtain ⟨entryAtQ, qCurrent, qTrace, qHistory, _qGood, erasedAtQ⟩ :=
        annotated_entry_erased_history setup values implementation operational sourceProfile
          nativeProfile who control trace tape q word canonicalPositive prefixPositive
            event payload actualClean
      have cursorCurrentEq : cursor.current = qCurrent :=
        Option.some.inj (congrArg History.state (qAtCursor.trans qHistory))
      have entrySaved : entryAtQ.cursor.current.saved = entryAtQ.cursor.current.point := by
        have state := Option.some.inj (congrArg History.state entryAtQ.cursorHistory)
        rw [state]
        rfl
      have erasedCurrent : entryAtQ.cursor.current.eraseHistory = qCurrent.eraseHistory :=
        Option.some.inj (congrArg Prod.fst (congrArg Prod.fst erasedAtQ))
      have currentAtEntry : ProtocolState.remaining setup.program cursor.current.point =
          ProtocolState.remaining setup.program cursor.current.saved := by
        rw [cursorCurrentEq]
        have point := congrArg (fun state : CommitRecoveryState setup.program =>
          ProtocolState.remaining setup.program state.point) erasedCurrent
        have saved := congrArg (fun state : CommitRecoveryState setup.program =>
          ProtocolState.remaining setup.program state.saved) erasedCurrent
        simp only [CommitRecoveryState.eraseHistory, ProtocolState.remaining_withHistory]
          at point saved
        rw [← point, ← saved, entrySaved]
      have cursorOffset : cursor.offset = low := by
        have count := cursor.compiled.countEq
        simp only [eventCount_eq_instructionCount] at count
        change cursor.offset + instructionCount (block.block.prepend block.suffix) =
          instructionCount setup.program at count
        have remaining : ProtocolState.remaining setup.program cursor.current.point =
            instructionCount (block.block.prepend block.suffix) := by
          rw [cursor.point, cursor.origin.remaining_lift, ProtocolState.remaining_entry]
        have saved := congrArg (fun controls => controls.2.2) (cursor.controls blockPositive)
        change instructionCount setup.program -
          ProtocolState.remaining setup.program cursor.current.saved = low at saved
        rw [← currentAtEntry] at saved
        omega
      have embeddingRank : ∀ index, (cursor.embedding.event index).val = low + index.val := by
        intro index
        rw [cursor.compiled.rankEq, cursorOffset]
      let wordProfile := ordinaryBlockProfile setup .concurrent implementation.plan values
        block.block block.suffix cursor.embedding (fun owner view => cursor.views.view owner view)
          (control.execution.application.entry.excluded,
            control.execution.application.generation, low)
          control.execution.application.publicView
          (PhaseProposal.sourceArchive control.execution.network.inputs)
      let ownWordLaw := (block.block.prefixLaw block.suffix wordProfile cursor.source).map
        (SourceProgram.Config.view who)
      let issuedObservation := fun candidate => decide (issuedLedger setup implementation
        block.block low control high who candidate)
      let selectedAction := decodeEventAction setup.program event
        (cast (congrArg EventField.Action actualClean.binding.symm) (.success value))
      let selectedObservation := fun candidate => decide (
        issuedLedger setup implementation block.block low control high who candidate ∧
          block.block.wordAction who offset candidate = selectedAction)
      have issuedPresent : true ∈ (ownWordLaw.map issuedObservation).support :=
        (PMF.mem_support_map_iff ..).mpr ⟨referenceWord.view who,
          (PMF.mem_support_map_iff ..).mpr ⟨referenceWord, referenceWordSupport, rfl⟩,
            decide_eq_true (issuedLedgers who)⟩
      have selectedCylinder : (ownWordLaw.map selectedObservation) true =
          (ownWordLaw.map issuedObservation) true *
            (((fiberPosterior ownWordLaw issuedObservation true).map
              (block.block.wordAction who offset)) selectedAction) := by
        exact observation_fiber_mass ownWordLaw issuedObservation selectedObservation
          (block.block.wordAction who offset) selectedAction issuedPresent (by
            intro candidate _supported
            simp only [issuedObservation, selectedObservation, decide_eq_true_eq])
      let sourceObservation := fun history : setup.proposalRecoveryProtocol.History =>
        match completedAt history with
        | none => false
        | some final => decide (issuedLedger setup implementation block.block low control high who
            (final.view who) ∧ block.block.wordAction who offset (final.view who) = selectedAction)
      have pairCompleted : ordinaryPair.map Prod.snd =
          setup.proposalRecoveryModel.runBehavioralFrom ordinary block.block.length q := by
        simp only [ordinaryPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
        simp only [show (fun history : setup.proposalRecoveryProtocol.History => history) = id
          from rfl, PMF.map_id]
        rw [← setup.proposalRecoveryModel.runBehavioralFrom_add,
          Nat.add_sub_of_le offsetInside.le]
      obtain ⟨coupling, couplingSource, couplingWord, coupled⟩ :=
        ordinary_source_structural_joint setup values implementation control trace phase
          block.block block.suffix cursor
      have sourceMarginal : coupling.map Prod.fst =
          setup.proposalRecoveryModel.runBehavioralFrom ordinary block.block.length q := by
        simpa only [qAtCursor] using couplingSource
      have savedExclusions := actualClean.excluded_eq setup implementation control
        (checkpointSelection setup implementation operational trace).val actualEntry.phase
          actualEntry.installed
      have footprint :
          (control.execution.application.publicView.retired.map fun record =>
            record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
              control.execution.application.current.native.publicView.sourceFailureFootprint.1 low =
                control.execution.application.entry.excluded := by
        have controls := congrArg Prod.fst (cursor.controls blockPositive)
        exact controls.symm.trans (cursor.excluded.trans savedExclusions)
      have wordMarginal : coupling.map Prod.snd =
          block.block.prefixLaw block.suffix wordProfile cursor.source := by
        rw [footprint] at couplingWord
        simpa only [wordProfile, PhaseRuntimeState.attempt, low] using couplingWord
      have jointObservation : coupling.map (sourceObservation ∘ Prod.fst) =
          coupling.map (fun pair => selectedObservation (pair.2.view who)) := by
        apply map_congr_on_support
        intro pair pairSupported
        obtain ⟨final, last, lastTrace, candidate, history, _word, point, exclusions,
          _generation, _instructions, _labels, agree⟩ := coupled pair pairSupported
        have parsed : completedAt pair.1 = some final := by
          rw [history]
          change residualEntry? block.suffix
            (fun point => checkpoint.residual.lift
              (cast (congrArg ProtocolState block.reconstruct)
                (block.block.liftPoint block.suffix point))) last.point = some final
          have sameLift : (fun point => checkpoint.residual.lift
              (cast (congrArg ProtocolState block.reconstruct)
                (block.block.liftPoint block.suffix point))) =
                (fun point => cursor.lift (block.block.liftPoint block.suffix point)) := by
            funext point
            exact (cursorLift _).symm
          rw [sameLift]
          exact (residualEntry?_eq_some_iff
            (cursor.origin.compose (block.block.protocolSuffix block.suffix))
              last.point final).mpr point.symm
        have survives : who ∉ last.excluded := by
          rw [exclusions, cursor.excluded]
          exact actualAlive
        simp only [Function.comp_apply, sourceObservation, parsed, selectedObservation]
        rw [agree who survives]
      have ownMassProjected : ownMass = (ownWordLaw.map selectedObservation) true := by
        calc
          ownMass = ((ordinaryPair.map Prod.snd).map sourceObservation) true := by
            rw [PMF.map_comp]
            rfl
          _ = ((coupling.map Prod.fst).map sourceObservation) true := by
            rw [pairCompleted, sourceMarginal]
          _ = (coupling.map (fun pair => selectedObservation (pair.2.view who))) true := by
            rw [PMF.map_comp, jointObservation]
          _ = (ownWordLaw.map selectedObservation) true := by
            change _ = (((block.block.prefixLaw block.suffix wordProfile cursor.source).map
              (SourceProgram.Config.view who)).map selectedObservation) true
            rw [← wordMarginal, PMF.map_comp, PMF.map_comp]
            rfl
      obtain ⟨middleContext, middleNames, earlier, later, earlierLength, laterLength, split⟩ :=
        block.block.exists_split offset offsetInside.le
      let association := (earlier.prepend_append later block.suffix).symm.trans
        (congrArg (fun segment => segment.prepend block.suffix) split)
      let splitLift := fun point : ProtocolState (earlier.prepend (later.prepend block.suffix)) =>
        cursor.lift (cast (congrArg ProtocolState association) point)
      have splitOrigin : ProtocolSuffix setup.program
          (earlier.prepend (later.prepend block.suffix)) splitLift := by
        have transport {Γ : SourceCtx Player L} {O : Finset VarId}
            (first second : SourceProgram Player L Γ O) (same : first = second)
            (lift : ProtocolState second → ProtocolState setup.program)
            (origin : ProtocolSuffix setup.program second lift) :
            ProtocolSuffix setup.program first (fun point => lift
              (cast (congrArg ProtocolState same) point)) := by
          cases same
          exact origin
        exact transport _ _ association cursor.lift cursor.origin
      have splitPoint : cursor.current.point = splitLift
          (ProtocolState.entry (earlier.prepend (later.prepend block.suffix)) cursor.source) := by
        have entryCast {Γ : SourceCtx Player L} {O : Finset VarId}
            (first second : SourceProgram Player L Γ O) (same : first = second)
            (entry : SourceProgram.Config Player L Γ) :
            cast (congrArg ProtocolState same) (ProtocolState.entry first entry) =
              ProtocolState.entry second entry := by
          cases same
          rfl
        dsimp only [splitLift]
        rw [entryCast _ _ association cursor.source]
        exact cursor.point
      obtain ⟨middleSource, sourceCurrent, sourceTrace, firstAttempt, sourceHistory,
        sourcePoint, sourceExcluded, _sourceEntry, sourceGeneration, _sourceWord,
        _sourceLabels, _sourceProper⟩ := proposalRecovery_ordinary_commit_block_support setup values
          earlier (later.prepend block.suffix) splitLift splitOrigin cursor.source cursor.current
            cursor.trace splitPoint (cursor.excluded.trans cursor.entryExcluded.symm) g (by
              change g ∈ (setup.proposalRecoveryModel.runBehavioralFrom ordinary earlier.length
                ⟨some cursor.current, cursor.trace⟩).support
              rw [qAtCursor, earlierLength]
              exact prefixSupported)
      let originalCut := entry.canonicalCut setup values implementation operational fullValues
        reference referenceTrace who acting event payload clean good
      have sourceInformationAtG : setup.proposalRecoveryModel.infoOf who sourceTrace =
          setup.proposalRecoveryModel.infoOf who g.trace :=
        congrArg (fun history : setup.proposalRecoveryProtocol.History =>
          setup.proposalRecoveryModel.infoOf who history.trace) sourceHistory.symm
      have sourceInformation : setup.proposalRecoveryModel.infoOf who sourceTrace =
          setup.proposalRecoveryModel.infoOf who originalCut.trace :=
        sourceInformationAtG.trans sameInfo
      have signals := (setup.proposalRecoverySignals.withOwnPlayRecall_infoOf_eq_iff who
        sourceTrace originalCut.trace).mp sourceInformation
      have sourceCurrentRead := setup.source_current_of_signals who
        ⟨some sourceCurrent, sourceTrace⟩ ⟨some originalCut.current, originalCut.trace⟩ signals.1
      have sourceView : ProtocolState.observe who setup.program sourceCurrent.point =
          ProtocolState.observe who setup.program originalCut.current.point :=
        Option.some.inj (congrArg Prod.fst sourceCurrentRead)
      have sourceRank : event.val = instructionCount setup.program -
          ProtocolState.remaining setup.program sourceCurrent.point := by
        rw [ProtocolState.remaining_eq_of_observe who setup.program sourceView]
        exact originalCut.rank.symm
      have sourceSurvives : who ∉ sourceCurrent.excluded := by
        rw [sourceExcluded, cursor.excluded]
        exact actualAlive
      have sourceCurrentGeneration : sourceCurrent.generation =
          control.execution.application.generation :=
        sourceGeneration.trans (congrArg (fun controls => controls.2.1)
          (cursor.controls blockPositive))
      have sourceKept : TracePrefix sourceTrace targetTrace := by
        have kept := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin ordinary
          (block.block.length - offset) g ⟨some targetCurrent, targetTrace⟩
            tailSupported).tracePrefix
        change TracePrefix (⟨some sourceCurrent, sourceTrace⟩ :
          setup.proposalRecoveryProtocol.History).trace targetTrace
        rw [← sourceHistory]
        exact kept
      let actualCut := actualEntry.canonicalCut setup values implementation operational fullValues
        control trace who actualActing event payload actualClean actualGood
      obtain ⟨_selectedLow, _selectedHigh, selectedLaw⟩ :=
        sourceReplay_issued_source_callback_atom setup values implementation operational control
          trace block.suffix block.block block.reconstruct.symm block.boundary phase cursor
          blockPositive targetCurrent targetTrace wholeSupport
          referenceWord referenceWordSupport issuedLedgers finished attempt finishedPoint
          finishedExcluded structuralWord who (control.execution.recall who).length event payload
          actualClean.binding control trace .refl List.take_length.symm rfl actualCut.unsent
          actualCut.request sourceCurrent sourceTrace sourceKept sourceRank sourceCurrentGeneration
          sourceSurvives
      have observationEq : (fun candidate => decide (sourceIssuedOwnObservation setup implementation
          block.block low control who (referenceWord.view who)
            (control.execution.recall who).length candidate)) = issuedObservation := by
        funext candidate
        exact decide_eq_decide.mpr
          (issuedLedger_iff_recalled_word_actions setup implementation block.block block.suffix
            cursor.embedding low embeddingRank cursor.views.actionEq trace who
              (referenceWord.view who) candidate (issuedLedgers who)).symm
      rw [observationEq] at selectedLaw
      let selectedAtom := ordinary who (setup.proposalRecoveryModel.infoOf who g.trace) sourceChoice
      have choiceSome : sourceChoice.val ≠ none := by
        intro absent
        have castValue {first second : setup.proposalRecoveryModel.InfoState who}
            (same : first = second) (choice : setup.proposalRecoveryModel.Choice who first) :
            (same ▸ choice).val = choice.val := by cases same; rfl
        have data := source.encoded value
        rw [← castValue gInfo.symm (source.encode value), ← encoded, absent] at data
        simp only [Option.map_none, phaseRecoveryBindingData, Option.elim_none,
          Bool.false_eq_true, ite_false, Option.bind_none, Option.map_none,
          Option.getD_none, Prod.mk.injEq, reduceCtorEq, false_and] at data
      have castChoiceValue {first second : setup.proposalRecoveryModel.InfoState who}
          (same : first = second) (choice : setup.proposalRecoveryModel.Choice who first) :
          (same ▸ choice).val = choice.val := by cases same; rfl
      let sourceChoiceAtPoint := sourceInformationAtG.symm ▸ sourceChoice
      have choiceValue : sourceChoiceAtPoint.val = sourceChoice.val :=
        castChoiceValue sourceInformationAtG.symm sourceChoice
      have choiceLegal := (setup.proposalRecoveryModel.menu_adequate who sourceTrace
        sourceChoiceAtPoint.val).mp sourceChoiceAtPoint.property
      have sourceCommitting : ProtocolState.atCommit setup.program sourceCurrent.point = true :=
        (source_binding_at_rank setup.program sourceCurrent.point event who payload
          actualClean.binding sourceRank).1
      have sourceAction : sourceChoice.val.map (fun move => move.semantic.action) =
          selectedAction := by
        have data : phaseRecoveryBindingData setup .concurrent event who payload
            actualClean.binding (sourceChoice.val.map (·.semantic)) = (.success value, false) := by
          have selected := source.encoded value
          rw [← castChoiceValue gInfo.symm (source.encode value), ← encoded] at selected
          exact selected
        cases selected : sourceChoice.val with
        | none => exact (choiceSome selected).elim
        | some move =>
            rw [choiceValue, selected] at choiceLegal
            obtain ⟨_committing, _acting, decode⟩ := source_binding_at_rank setup.program
              sourceCurrent.point event who payload actualClean.binding sourceRank
            obtain ⟨graphAction, decoded⟩ := decode move.semantic.action choiceLegal.2.1.1
            have encodedAction := encodeEventAction?_decodeEventAction_eq_some setup.program
              event graphAction move.semantic.action decoded
            have proper := properChoice move.semantic (by rw [selected]; rfl)
            have result : cast (congrArg EventField.Action actualClean.binding) graphAction =
                .success value := by
              have result := congrArg Prod.fst data
              simpa only [selected, Option.map_some, phaseRecoveryBindingData,
                Option.elim_some, proper.1, Bool.false_eq_true, ite_false, Option.bind_some,
                encodedAction, Option.map_some, Option.getD_some] using result
            have graphActionEq : graphAction =
                cast (congrArg EventField.Action actualClean.binding.symm) (.success value) := by
              rw [← result]
              simp only [cast_cast, cast_eq]
            simp only [Option.map_some]
            exact decoded.symm.trans (congrArg (decodeEventAction setup.program event)
              graphActionEq)
      have sourceActionLaw := sourceReplay_ordinary_commitment_action_law setup values who
        sourceCurrent sourceTrace event payload
        actualClean.binding sourceRank sourceSurvives
      have sourceActionAtom := sourceReplay_ordinary_commitment_action_atom setup values who
        sourceCurrent sourceTrace sourceCommitting
        sourceChoiceAtPoint (by simpa only [choiceValue] using properChoice)
      have transportAtom {first second : setup.proposalRecoveryModel.InfoState who}
          (same : first = second) (choice : setup.proposalRecoveryModel.Choice who first) :
          ordinary who second (same ▸ choice) = ordinary who first choice := by
        cases same
        rfl
      have sourceChoiceAtom : ordinary who (setup.proposalRecoveryModel.infoOf who sourceTrace)
          sourceChoiceAtPoint = selectedAtom :=
        transportAtom sourceInformationAtG.symm sourceChoice
      rw [sourceChoiceAtom, choiceValue, sourceInformationAtG, sourceAction] at sourceActionAtom
      have selectedAtomEq :
          (((fiberPosterior ownWordLaw issuedObservation true).map
            (block.block.wordAction who offset)) selectedAction) = selectedAtom := by
        rw [← sourceActionLaw] at selectedLaw
        rw [sourceInformationAtG] at selectedLaw
        exact (congrArg (fun law => law selectedAction) selectedLaw).trans sourceActionAtom
      have focalCylinder : ownMass = (ownWordLaw.map issuedObservation) true * selectedAtom := by
        rw [ownMassProjected, selectedCylinder, selectedAtomEq]
      let sourcePrefixObservation := fun candidate => decide (
        ∀ position < offset, block.block.wordAction who position candidate =
          block.block.wordAction who position (referenceWord.view who))
      have phaseHigh : actualEntry.phase.high = low + block.block.length := by
        change block.block.length = actualEntry.phase.high - actualEntry.phase.low at size
        have ordered := actualEntry.phase.nonempty.le
        rw [phaseLow] at size ordered
        omega
      have selectedInside : low ≤ event.val ∧ event.val < low + block.block.length := by
        have interval := (actualEntry.phase.mem_events event).mp actualEntry.inside
        rw [phaseLow, phaseHigh] at interval
        exact interval
      have issuedSourcePrefix : issuedObservation = sourcePrefixObservation := by
        funext candidate
        apply decide_eq_decide.mpr
        exact issuedLedger_iff_prefix_at_request setup implementation block.block block.suffix
          cursor.embedding low embeddingRank cursor.views.actionEq trace actualEntry.phase
            actualEntry.installed phaseLow phaseHigh who event payload actualClean.binding
              actualCut.request selectedInside actualCut.unsent (referenceWord.view who)
                candidate (issuedLedgers who)
      let sourceObservationAt := fun count candidate => decide (
        ∀ position < count, block.block.wordAction who position candidate =
          block.block.wordAction who position (referenceWord.view who))
      have referenceActions : (List.range block.block.length).map
          (fun index => block.block.wordAction who index (referenceWord.view who)) =
            attempt.joints.map (fun joint => (joint who).map (fun move => move.action)) := by
        rw [structuralWord]
        have fixed : ∀ (after : Finset Player)
            (candidate : block.block.Attempt cursor.source cursor.current.excluded finished after),
            after = cursor.current.excluded →
            (List.range block.block.length).map (fun index => block.block.wordAction who index
              ((candidate.withoutMisses ∅ cursor.source).view who)) =
                candidate.joints.map (fun joint => (joint who).map (fun move => move.action)) := by
          intro after candidate unchanged
          subst after
          exact sourceReplay_attempt_owned_actions who block.block cursor.source cursor.source
            cursor.current.excluded
            finished candidate (cursor.excluded.symm ▸ actualAlive)
        exact fixed _ attempt finishedExcluded
      have sourcePositionLaw := sourceReplay_source_prefix_position_law setup values
        implementation operational control trace block.suffix block.block block.reconstruct.symm
          block.boundary phase cursor blockPositive targetCurrent targetTrace wholeSupport
            referenceWord referenceWordSupport issuedLedgers finished attempt finishedPoint
              finishedExcluded structuralWord who event payload actualClean actualEntry actualCut
                phaseLow
                phaseHigh embeddingRank offsetInside
      have semanticWordEq : wholeAttempt.joints = attempt.joints := by
        have reversed := List.append_cancel_right (literalWord.symm.trans finishedWord)
        have same := congrArg List.reverse reversed
        simpa only [List.reverse_reverse] using same
      have referenceWholeActions : (List.range block.block.length).map
          (fun index => block.block.wordAction who index (referenceWord.view who)) =
            wholeAttempt.joints.map (fun joint => (joint who).map (fun move => move.action)) := by
        rw [referenceActions, semanticWordEq]
      have gToTarget : TracePrefix g.trace targetTrace :=
        (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin ordinary
          (block.block.length - offset) g ⟨some targetCurrent, targetTrace⟩
            tailSupported).tracePrefix
      have targetGeneration : targetCurrent.generation = cursor.current.generation :=
        (congrArg CommitRecoveryState.generation
          (Option.some.inj (congrArg History.state wholeHistory))).trans _wholeGeneration
      have startRank : instructionCount setup.program -
          ProtocolState.remaining setup.program cursor.current.point = low := by
        rw [cursor.point, cursor.origin.remaining_lift, ProtocolState.remaining_entry]
        have count := cursor.compiled.countEq
        simp only [eventCount_eq_instructionCount] at count
        rw [cursorOffset] at count
        omega
      have referencePresent (position : Nat) : true ∈
          (ownWordLaw.map (sourceObservationAt position)).support := by
        refine (PMF.mem_support_map_iff ..).mpr ⟨referenceWord.view who,
          (PMF.mem_support_map_iff ..).mpr ⟨referenceWord, referenceWordSupport, rfl⟩, ?_⟩
        apply decide_eq_true
        intro _index _bounded
        rfl
      have sourceFold := sourceReplay_source_prefix_cylinder_fold setup values implementation
        who control checkpoint.residual.tail block phase cursor blockPositive q g qLength
          qInitialized cursorPrefix low offset gDepth offsetInside targetCurrent targetTrace
            gToTarget targetGeneration finishedExcluded actualAlive startRank embeddingRank
              wholeFinished wholeCurrent wholeAttempt literalWord wholeProper referenceWord
                referenceWholeActions ownWordLaw rows sourcePositionLaw referencePresent
      obtain ⟨sourceRecords, sourceRecordsEq, issuedCylinder⟩ := sourceFold g qKept .refl
      have recordsEq : sourceRecords = newOwn :=
        List.append_cancel_right (sourceRecordsEq.symm.trans ownSuffix)
      have focalIssuedMass : (ownWordLaw.map issuedObservation) true =
          ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
            (ordinary who) newOwn) := by
        rw [issuedSourcePrefix]
        change (ownWordLaw.map (sourceObservationAt offset)) true = _
        have lengthEq : g.trace.length - q.trace.length = offset := by omega
        simpa only [lengthEq, recordsEq] using issuedCylinder
      have tailFuel : sourceCommitFuel setup g = block.block.length - offset := by
        rw [sourceHistory]
        change ProtocolState.remaining setup.program sourceCurrent.point -
          ProtocolState.commitEnd setup.program sourceCurrent.point = block.block.length - offset
        let remainingOrigin := splitOrigin.compose (earlier.protocolSuffix
          (later.prepend block.suffix))
        rw [sourcePoint, remainingOrigin.remaining_lift, remainingOrigin.commitEnd_lift,
          ProtocolState.remaining_entry, later.instructionCount_prepend,
          later.commitEnd_entry_prepend block.suffix block.boundary middleSource,
          Nat.add_sub_cancel]
        omega
      have ordinaryTail : setup.proposalRecoveryModel.runBehavioralFrom ordinary
          (block.block.length - offset) g ⟨some targetCurrent, targetTrace⟩ =
            selectedAtom * sourceTail := by
        rw [← tailFuel]
        exact sourceReplay_selected_source_tail_atom setup values who g sourceChoice
          targetCurrent targetTrace choiceSome supported (by rw [tailFuel]; omega)
      rw [ownAtG, classesAtG, ownAtEntry, classesAtEntry]
      rw [pairAtom, ordinaryTail, focalCylinder, focalIssuedMass]
      have ofRealTriple (own : ℝ) (classes continuation : ℝ≥0∞)
          (classesFinite : classes ≠ ⊤) (continuationFinite : continuation ≠ ⊤) :
          ENNReal.ofReal (own * classes.toReal * continuation.toReal) =
            ENNReal.ofReal own * classes * continuation := by
        rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg,
          ENNReal.ofReal_mul' ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal classesFinite, ENNReal.ofReal_toReal continuationFinite]
      have calibrated := congrArg ENNReal.ofReal prefixCalibration
      rw [ENNReal.ofReal_mul'
        (setup.proposalRecoveryModel.ownPlayReachProbability_nonneg (ordinary who) newOwn),
        ofRealTriple _ _ _
          (setup.proposalRecoveryForeignProducts_finite values scale sourceBad scale who
            g.trace).1 (PMF.apply_ne_top _ _),
        ofRealTriple _ _ _
          (setup.proposalRecoveryForeignProducts_finite values scale sourceBad scale who
            q.trace).1 (PMF.apply_ne_top _ _)] at calibrated
      rw [setup.proposalRecoveryModel.playerReachProbability_eq_ownPlayReachProbability,
        setup.proposalRecoveryModel.playerReachProbability_eq_ownPlayReachProbability]
          at calibrated
      have prefixLength : g.trace.length - q.trace.length = offset := by omega
      rw [prefixLength] at calibrated
      calc
        _ = (ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
                (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who g.trace)) *
              (setup.proposalRecoveryForeignProducts values scale sourceBad scale who g.trace).1 *
                setup.proposalRecoveryModel.runBehavioralFrom ordinary offset q g) *
                  selectedAtom * sourceTail := by ac_rfl
        _ = (ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
                (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who q.trace)) *
              (setup.proposalRecoveryForeignProducts values scale sourceBad scale who q.trace).1 *
                sourcePrefix * ENNReal.ofReal
                  (setup.proposalRecoveryModel.ownPlayReachProbability (ordinary who) newOwn)) *
                    selectedAtom * sourceTail := by
                      rw [calibrated]
                      simp only [sourcePrefix, prefixLength]
        _ = _ := by ac_rfl
    have issuedPositive : issued ≠ 0 := by
      rw [issuedValue]
      exact foreignPositive
    have issuedCancel := ENNReal.mul_inv_cancel (mul_ne_zero ownPositive issuedPositive)
      (ENNReal.mul_ne_top ownFinite issuedFinite)
    change setup.proposalRecoveryClosedMass sourceProfile who canonical =
      ENNReal.ofReal canonical.trace.transitionMass * canonicalOwn * canonicalClasses *
        historical at closedFactors
    have numerator :
        anchorOwn * anchorClasses *
          ((nativeModel).historyReachWeight nativeProfile ⟨some control, trace⟩ *
            prefixTapeLaw setup implementation ⟨some control, trace⟩ tape *
            setup.proposalRecoveryClosedLaw sourceProfile who canonical q * beta) =
        coefficient * (setup.proposalRecoveryModel.historyReachWeight sourceProfile g *
          sourceTail) * law.choices script * (ownMass * issued) := by
      rw [nativeScalar]
      calc
        _ = coefficient * law.choices script * issued *
            ((ENNReal.ofReal canonical.trace.transitionMass * historical *
                setup.proposalRecoveryClosedLaw sourceProfile who canonical q) *
              (anchorOwn * anchorClasses * beta)) := by ring
        _ = coefficient * law.choices script * issued *
            ((ENNReal.ofReal canonical.trace.transitionMass * historical *
                setup.proposalRecoveryClosedLaw sourceProfile who canonical q) *
              (canonicalOwn * canonicalClasses * sourcePrefix * ownMass * sourceTail)) := by
          rw [ordinaryRows]
        _ = coefficient * law.choices script *
            (((ENNReal.ofReal canonical.trace.transitionMass * canonicalOwn * canonicalClasses *
                  historical) * setup.proposalRecoveryClosedLaw sourceProfile who canonical q) *
              sourcePrefix * sourceTail) * (ownMass * issued) := by ring
        _ = coefficient * law.choices script *
            ((setup.proposalRecoveryClosedMass sourceProfile who canonical *
                setup.proposalRecoveryClosedLaw sourceProfile who canonical q) *
              sourcePrefix * sourceTail) * (ownMass * issued) := by rw [← closedFactors]
        _ = coefficient * law.choices script *
            (setup.proposalRecoveryModel.historyReachWeight sourceProfile q *
              sourcePrefix * sourceTail) * (ownMass * issued) := by rw [disintegration]
        _ = _ := by rw [← sourcePrefixReach]; ring
    calc
      _ = (anchorOwn * anchorClasses *
          ((nativeModel).historyReachWeight nativeProfile ⟨some control, trace⟩ *
            prefixTapeLaw setup implementation ⟨some control, trace⟩ tape *
            setup.proposalRecoveryClosedLaw sourceProfile who canonical q * beta)) *
            (ownMass * issued)⁻¹ := by ring
      _ = (coefficient * (setup.proposalRecoveryModel.historyReachWeight sourceProfile g *
          sourceTail) * law.choices script) * (ownMass * issued) *
            (ownMass * issued)⁻¹ := by rw [numerator]
      _ = _ := by rw [mul_assoc, issuedCancel, mul_one]


open Classical in
/-- The positive mechanical/source branch supplies the same normalized native
replay law and the original per-history annotation balance. -/
theorem qualified_annotation_native_balance
    (operational : implementation.Operational)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (cleanSite : CleanUnsentBinding setup implementation who past view event payload)
    (_qualified : 0 < qualifiedPrefixMass setup implementation nativeProfile who site event)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site past view
      event payload cleanSite.binding)
    (pairLaw : ForeignPosteriorCutPair setup values implementation)
    (index : MechanicalIndex setup implementation who) (value : L.Val payload)
    (g completed : setup.proposalRecoveryProtocol.History)
    (mechanics : mechanicalCoefficient setup implementation ⟨nativeBad, scale, scale, scale⟩
      nativeProfile who site event index ≠ 0)
    (positiveDensity :
      (if same : setup.proposalRecoveryModel.infoOf who g.trace = source.site.1 then
        if setup.proposalRecoveryForeignGood who g then
          setup.proposalRecoveryModel.historyReachWeight sourceProfile g *
            sourceForcedBlock setup values who g (same.symm ▸ source.encode value) completed
        else 0
      else 0) ≠ 0) :
    let own := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
      (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who source.anchor.trace))
    let classes := (setup.proposalRecoveryForeignProducts values scale sourceBad scale
      who source.anchor.trace).1
    let coefficient := mechanicalCoefficient setup implementation
      ⟨nativeBad, scale, scale, scale⟩ nativeProfile who site event
    let density :=
      if same : setup.proposalRecoveryModel.infoOf who g.trace = source.site.1 then
        if setup.proposalRecoveryForeignGood who g then
          setup.proposalRecoveryModel.historyReachWeight sourceProfile g *
            sourceForcedBlock setup values who g (same.symm ▸ source.encode value) completed
        else 0
      else 0
    ∃ law : PMF ((nativeModel).InformationHistory who site.1),
      ∀ history : (nativeModel).InformationHistory who site.1,
        own * classes *
          (if mechanicalWord setup implementation who history.val.trace = index.1.val then
            ∑' candidate : setup.proposalRecoveryProtocol.History,
              ∑' word : SourceProgram.History Player L,
                annotatedPrefixWeight setup values implementation operational sourceProfile
                    nativeProfile who history.val index.2 candidate word *
                  (if bindingAdmissionBit setup implementation who event history.val index.2
                    then 1 else 0) *
                  sourceForcedBlockJoint setup values implementation who history.val event payload
                    candidate word value (g, completed)
          else 0) = coefficient index * density * law history := by
  classical
  intro own classes coefficient density
  have gInfo : setup.proposalRecoveryModel.infoOf who g.trace = source.site.1 := by
    by_contra different
    exact positiveDensity (by rw [dite_eq_right different])
  have sourceGood : setup.proposalRecoveryForeignGood who g := by
    by_contra bad
    exact positiveDensity (by rw [dite_eq_left gInfo, ite_eq_right bad])
  let sourceChoice := gInfo.symm ▸ source.encode value
  have supported : completed ∈ (sourceForcedBlock setup values who g sourceChoice).support := by
    apply (PMF.mem_support_iff ..).mpr
    intro zero
    exact positiveDensity (by rw [dite_eq_left gInfo, ite_eq_left sourceGood, zero, mul_zero])
  have anchorExists : ∃ history : (nativeModel).InformationHistory who site.1,
      mechanicalWord setup implementation who history.val.trace = index.1.val ∧
      (nativeModel).historyReachWeight nativeProfile history.val ≠ 0 ∧
      prefixTapeLaw setup implementation history.val index.2 ≠ 0 ∧
      (∀ owner, owner ≠ who →
        ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
          implementation.bounds nativeInitial implementation.horizon implementation.scheduler
            owner history.val) ∧
      history.val.state.elim True (fun control =>
        who ∉ control.execution.application.current.excluded) ∧
      bindingAdmissionBit setup implementation who event history.val index.2 = true := by
    by_contra absent
    exact mechanics (by simp only [mechanicalCoefficient, dite_eq_right absent])
  obtain ⟨anchor, anchorWord, anchorPositive, tapePositive, foreign, alive, admitted⟩ :=
    anchorExists
  obtain ⟨reference, referenceTrace, anchorEq, acting, pastEq, viewEq⟩ :=
    native_binding_site_history setup implementation who site past view siteEq anchor
  rw [anchorEq] at anchorWord anchorPositive tapePositive foreign alive admitted
  have referenceInformation : (nativeModel).infoOf who referenceTrace = site.1 := by
    have known := anchor.property
    change (nativeModel).infoOf who anchor.val.trace = site.1 at known
    rw [anchorEq] at known
    exact known
  subst past
  subst view
  obtain ⟨entry⟩ := qualified_binding_entry setup implementation operational reference
    referenceTrace
    who event payload cleanSite foreign
  let nativeCut := entry.canonicalCut setup values implementation operational fullValues reference
    referenceTrace who acting event payload cleanSite foreign
  have cutInfo : setup.proposalRecoveryModel.infoOf who nativeCut.trace = source.site.1 := by
    apply source.actualCut reference (sourceCutTrace setup implementation referenceTrace) nativeCut
    change ((nativeMenu).signals
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon implementation.scheduler).infoOf who
          (sourceCutTrace setup implementation referenceTrace) = site.1
    rw [(nativeMenu).info]
    have direct := referenceInformation
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who referenceTrace = site.1 at direct
    rw [(nativeMenu).info] at direct
    exact direct
  have sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who nativeCut.trace := gInfo.trans cutInfo.symm
  obtain ⟨q, qKept, qLength, qInfo⟩ := source_information_prefix setup who
    ⟨some nativeCut.current, nativeCut.trace⟩ g
      ⟨some nativeCut.cursor.current, nativeCut.cursor.trace⟩ sameInfo.symm nativeCut.past
  have qDepth : q.trace.length =
      (canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩).trace.length :=
    qLength.trans (congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      history.trace.length) entry.canonicalHistory)
  have properChoice : ∀ move, sourceChoice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure := by
    intro move selected
    have castVal {first last : setup.proposalRecoveryModel.InfoState who} (same : first = last)
        (choice : setup.proposalRecoveryModel.Choice who first) :
        (same ▸ choice).val = choice.val := by cases same; rfl
    have data := source.encoded value
    rw [← castVal gInfo.symm (source.encode value), selected] at data
    have notMissing : move.missing = false := by
      cases missing : move.missing with
      | false => rfl
      | true => simp only [phaseRecoveryBindingData, Option.elim_some, missing, ↓reduceIte,
          Prod.mk.injEq, reduceCtorEq, false_and] at data
    refine ⟨notMissing, ?_⟩
    intro failed
    cases encoded : encodeEventAction? setup.program event move.action with
    | none => simp only [phaseRecoveryBindingData, Option.elim_some, notMissing,
        Bool.false_eq_true, ↓reduceIte, Option.bind_some, encoded, Option.map_none,
        Option.getD_none, Prod.mk.injEq, reduceCtorEq, false_and] at data
    | some action =>
      have decoded := decodeEventAction_encodeEventAction?_eq_some setup.program event
        move.action action encoded
      have physical := (decodeEventAction_binding_failure_iff setup.program event who payload
        cleanSite.binding action move.action decoded).mpr failed
      simp only [phaseRecoveryBindingData, Option.elim_some, notMissing, Bool.false_eq_true,
        ↓reduceIte, Option.bind_some, encoded, Option.map_some, Option.getD_some,
        physical, Prod.mk.injEq, reduceCtorEq, false_and] at data
  obtain ⟨targetCurrent, targetTrace, targetEq⟩ :
      ∃ (current : CommitRecoveryState setup.program)
        (trace : setup.proposalRecoveryProtocol.Trace (some current)),
          completed = (⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History) := by
    have onward : TracePrefix g.trace completed.trace := by
      have support := supported
      unfold sourceForcedBlock at support
      obtain ⟨middle, first, rest⟩ := (PMF.mem_support_bind_iff ..).mp support
      exact (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ 1
        g middle first).tracePrefix.trans
          (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ _
            middle completed rest).tracePrefix
    have zeroState : ∀ {state} (trace : setup.proposalRecoveryProtocol.Trace state),
        trace.length = 0 → state = none := by
      intro state trace zero
      cases trace with
      | start => rfl
      | extend prior joint legal moved => simp only [Trace.length] at zero; omega
    have noneZero : ∀ {state} (trace : setup.proposalRecoveryProtocol.Trace state),
        state = none → trace.length = 0 := by
      intro state trace empty
      cases trace with
      | start => rfl
      | @extend before after prior joint legal moved =>
        cases empty
        cases before with
        | none =>
          simp only [Setup.proposalRecoveryProtocol, Setup.commitRecoveryProtocol,
            PMF.mem_support_map_iff] at moved
          obtain ⟨input, _member, impossible⟩ := moved
          cases impossible
        | some current =>
          simp only [Setup.proposalRecoveryProtocol, Setup.commitRecoveryProtocol,
            PMF.mem_support_map_iff] at moved
          obtain ⟨next, _member, impossible⟩ := moved
          cases impossible
    rcases completed with ⟨state, trace⟩
    cases state with
    | some current => exact ⟨current, trace, rfl⟩
    | none =>
      have lastZero := noneZero trace rfl
      have gZero : g.trace.length = 0 := by
        have bound := onward.length_le
        change g.trace.length ≤ trace.length at bound
        omega
      have sameDepth := congrArg (fun information => information.1.2.length) sameInfo
      change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who g.trace).1.2.length =
        (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who nativeCut.trace).1.2.length
          at sameDepth
      rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf]
        at sameDepth
      simp only [setup.source_signal_depth, gZero] at sameDepth
      have impossible := zeroState nativeCut.trace sameDepth.symm
      cases impossible
  cases targetEq
  obtain ⟨law, selected, selectedFacts, readback, support, atoms, coverage⟩ :=
    sourceRawReplay_qualified setup values implementation operational fullValues who reference
      referenceTrace acting event payload cleanSite foreign entry g sameInfo sourceGood sourceChoice
        properChoice targetCurrent targetTrace supported scale nativeBad scalePositive nativeProfile
          nativePrescribed index.2 tapePositive admitted
  let nativeLaw := law.choices.bindOnSupport
    (fun script member => PMF.pure (selected script member))
  let atSite : (nativeModel).InformationHistory who
      ((nativeModel).infoOf who referenceTrace) → (nativeModel).InformationHistory who site.1 :=
    fun history => ⟨history.val, history.property.trans referenceInformation⟩
  refine ⟨nativeLaw.map atSite, ?_⟩
  intro history
  by_cases member : history ∈ (nativeLaw.map atSite).support
  · obtain ⟨image, imageMember, imageEq⟩ := (PMF.mem_support_map_iff ..).mp member
    obtain ⟨script, scriptMember, selectedEq⟩ := (support image).mp imageMember
    cases selectedEq
    cases imageEq
    obtain ⟨replayed, mechanical, reached, taped, good, alive, admitted⟩ :=
      selectedFacts script scriptMember
    obtain ⟨_entryInformation, sameKey⟩ := sourceRawReplay_closed_key setup values implementation
      operational fullValues who reference referenceTrace acting event payload cleanSite foreign
        entry g sameInfo sourceGood sourceChoice properChoice targetCurrent targetTrace supported
          scale law script scriptMember (selected script scriptMember) replayed q qKept qDepth
    have atom := sourceRawReplay_annotation_atom setup values implementation operational fullValues
      who reference referenceTrace acting event payload cleanSite foreign entry g sameInfo
        sourceGood
        sourceChoice properChoice targetCurrent targetTrace supported scale sourceBad nativeBad
          scalePositive scaleBelow sourceBadPositive sourceBadBelow nativeBadPositive nativeBadBelow
            sourceProfile sourcePrescribed nativeProfile nativePrescribed site referenceInformation
              source gInfo value rfl law script scriptMember (selected script scriptMember) replayed
                reached index.2 taped good alive admitted q qKept qDepth sameKey pairLaw
    have coefficientAtom := mechanicalCoefficient_eq_of_anchor setup values implementation
      operational scale nativeBad scalePositive scaleBelow nativeBadPositive nativeBadBelow
        fullValues nativeProfile nativePrescribed who site event index
          (atSite (selected script scriptMember)) (mechanical.trans anchorWord) reached taped good
            alive admitted
    change coefficient index = _ at coefficientAtom
    have scriptAtom := atoms script scriptMember
    have choiceAtom := sourceReplayScriptMass_factor setup values implementation scale who
      ⟨some targetCurrent, targetTrace⟩ reference ⟨some reference, referenceTrace⟩ script
        (law.choices script) (law.atoms script scriptMember)
          (selected script scriptMember).val replayed
    have injective : Function.Injective atSite := by
      intro first second equal
      apply Subtype.ext
      exact congrArg (fun history : (nativeModel).InformationHistory who site.1 =>
        history.val) equal
    have nativeAtom : (nativeLaw.map atSite) (atSite (selected script scriptMember)) =
        law.choices script := by
      rw [pmf_map_apply_of_injective _ injective]
      exact scriptAtom.trans choiceAtom.symm
    rw [nativeAtom, coefficientAtom, ite_eq_left (mechanical.trans anchorWord)]
    simpa only [own, classes, density, dite_eq_left gInfo, ite_eq_left sourceGood] using atom
  · have zeroAtom : (nativeLaw.map atSite) history = 0 := by
      exact (PMF.apply_eq_zero_iff _ _).mpr member
    rw [zeroAtom, mul_zero]
    by_cases matching : mechanicalWord setup implementation who history.val.trace = index.1.val
    · rw [ite_eq_left matching]
      have vanished : (∑' candidate : setup.proposalRecoveryProtocol.History,
          ∑' word : SourceProgram.History Player L,
            annotatedPrefixWeight setup values implementation operational sourceProfile
                nativeProfile who history.val index.2 candidate word *
              (if bindingAdmissionBit setup implementation who event history.val index.2
                then 1 else 0) *
              sourceForcedBlockJoint setup values implementation who history.val event payload
                candidate word value (g, ⟨some targetCurrent, targetTrace⟩)) = 0 := by
        apply ENNReal.tsum_eq_zero.mpr
        intro candidate
        apply ENNReal.tsum_eq_zero.mpr
        intro word
        by_contra positive
        obtain ⟨control, trace, historyEq, actualActing, actualPast, actualView⟩ :=
          native_binding_site_history setup implementation who site
            (reference.execution.recall who) (reference.execution.observe nativeApplication who)
              siteEq history
        have actualClean : CleanUnsentBinding setup implementation who
            (control.execution.recall who) (control.execution.observe nativeApplication who)
              event payload := by
          rw [actualPast, actualView]
          exact cleanSite
        have actualInformation : (nativeModel).infoOf who trace =
            (nativeModel).infoOf who referenceTrace := by
          have siteInformation := history.property
          rw [historyEq] at siteInformation
          exact siteInformation.trans referenceInformation.symm
        have canonicalPositive := (prescribed_source_history_positive setup values scale sourceBad
          scalePositive scaleBelow sourceBadPositive sourceBadBelow fullValues sourceProfile
            sourcePrescribed (canonicalSource setup implementation operational
              ⟨some control, trace⟩)).ne'
        rw [historyEq, nativePrescribed] at positive
        have matchingReference : mechanicalWord setup implementation who trace =
            mechanicalWord setup implementation who referenceTrace := by
          have word := matching
          rw [historyEq] at word
          exact word.trans anchorWord.symm
        obtain ⟨script, scriptMember, replayed⟩ := coverage nativeBad scalePositive scaleBelow
          nativeBadPositive nativeBadBelow fullValues sourceProfile control trace actualActing
            actualInformation index.2 candidate word canonicalPositive payload actualClean value
              positive matchingReference
        have chosenReplay := (selectedFacts script scriptMember).1
        have chosenEq : (selected script scriptMember).val = history.val :=
          (Option.some.inj (chosenReplay.symm.trans replayed)).trans historyEq.symm
        have atSiteEq : atSite (selected script scriptMember) = history := Subtype.ext chosenEq
        apply member
        apply (PMF.mem_support_map_iff ..).mpr
        exact ⟨selected script scriptMember,
          (support _).mpr ⟨script, scriptMember, rfl⟩, atSiteEq⟩
      rw [vanished, mul_zero]
    · rw [ite_eq_right matching, mul_zero]


end Vegas.PhaseProposalQualifiedBinding
