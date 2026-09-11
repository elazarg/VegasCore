/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedPublicChoiceBlock
import Vegas.Compile.WindowedBlockSourceCoupling
import Vegas.Compile.WindowedBlockSample
import Vegas.Compile.WindowedBlockCaches

/-! # Public-choice source successors at actual windowed checkpoints -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem relayPrefix_player_count_eq_zero (before : List P) (who : P)
    (hnotmem : who ∉ before) :
    (before.flatMap fun actor =>
      [Invocation.player actor, Invocation.environment]).countP (fun invocation =>
        match invocation with
        | .player actor => decide (actor = who)
        | .environment => false) = 0 := by
  induction before with
  | nil => rfl
  | cons actor rest ih =>
      simp only [List.mem_cons, not_or] at hnotmem
      have hne : actor ≠ who := fun h => hnotmem.1 (h ▸ rfl)
      simp [List.flatMap_cons, hne, ih hnotmem.2]

omit [DecidableEq P] in
private theorem relayPrefix_environment_count (before : List P) :
    (before.flatMap fun actor =>
      [Invocation.player actor, Invocation.environment]).countP
        Invocation.isEnvironment = before.length := by
  induction before with
  | nil => rfl
  | cons actor rest ih =>
      simp [List.flatMap_cons, Invocation.isEnvironment, ih]

/-- At a ready source public choice, its certified public fallback supplies a
concrete due expiry, successful handler, and the corresponding two-node source
successor. -/
theorem publicChoice_source_relay_eligibility
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName who guard tail).decision)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (execution : runtime.application.PolicyExecution) (activation : Activation Nat) (relay : P)
    (hstate : runtime.Consistent execution.native.application)
    (hactive : execution.native.application.active = some activation)
    (hcode : runtime.image.lookup activation.key = some (.publicChoice
      ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
        fallback fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (hoverdue : activation.since + runtime.windowOf activation.key <
      execution.native.application.base.memory.clock)
    (hfresh : execution.native.pool.lookup
      (relay, execution.native.pool.nextSerial relay) = none) :
    let chosen := L.eval fallback.expr current.current.source.erasePubEnv
    ∃ payload resolved,
      runtime.dueExpiry?
        (execution.native.application.base.memory, execution.native.application.active) =
          some payload ∧
      execution.native.pool.lookup (relay, execution.native.pool.nextSerial relay) = none ∧
      runtime.handle execution.native.application
        ⟨(relay, execution.native.pool.nextSerial relay), payload⟩ = some resolved ∧
      ∃ next : CoupledAt
          (compileCore (.commit name who guard (.reveal publicName who name .here tail))
            fresh build).graph
          (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
            publicName who .here fresh.2.1).1,
        next.current.source = (current.current.source.cons chosen).cons chosen ∧
        resolved.base.Refines next.current.graph.1 := by
  dsimp only
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let code := site.timeoutCode fallback fresh build deadline
  let chosen := L.eval fallback.expr current.current.source.erasePubEnv
  have hready := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
    execution.native.application.base.memory.done hrefines.memory.completed
  have hcompiled := fallback.compiled_evalStore?_eq_source fresh build
    current.current.graph.1.store execution.native.application.base.memory.store
    current.current.source current.current.agrees (fun ref href =>
      hrefines.memory.publicFields ref (fallback.compiled_reads_public fresh build ref href))
  obtain ⟨reads, hreads, heval⟩ := Option.map_eq_some_iff.mp hcompiled
  have hvalid : code.guard.validate execution.native.application.base.memory.store
      ((fallback.compiled fresh build).eval reads) = true := by
    change site.validator fresh build execution.native.application.base.memory.store
      ((fallback.compiled fresh build).eval reads) = true
    rw [heval]
    rw [site.validator_source_of_publiclyValidatable fresh build
      current.current.graph.1.store execution.native.application.base.memory.store
      current.current.source heligible current.current.agrees hrefines.memory.publicFields]
    exact fallback.legal current.current.source
  let resolved := runtime.advanceTo execution.native.application
    (execution.native.application.base.publish code ((fallback.compiled fresh build).eval reads))
  have hhandle : runtime.handle execution.native.application
      ⟨(relay, execution.native.pool.nextSerial relay), .expireChoice activation.key⟩ =
        some resolved := by
    exact runtime.handle_expireChoice_after_window execution.native.application activation
      hstate hactive code hcode ⟨deadline, fallback.compiled fresh build⟩ rfl hready hoverdue
      reads hreads (by simpa [code, site] using hvalid)
      (relay, execution.native.pool.nextSerial relay)
  obtain ⟨value, hvalue, _, next, hsource, hnext⟩ :=
    runtime.handle_expireChoice_source_coupling guard tail fallback fresh build deadline current
      heligible execution.native.application resolved activation
      (relay, execution.native.pool.nextSerial relay) activation.key hactive hcode hrefines hhandle
  have hchosen : value = chosen := hvalue
  subst value
  exact ⟨.expireChoice activation.key, resolved,
    runtime.dueExpiry?_of_publicChoice execution.native.application activation hstate hactive
      code hcode ⟨deadline, fallback.compiled fresh build⟩ rfl hoverdue,
    hfresh, hhandle, next, hsource, hnext⟩

/-- The public-choice expiry certificate remains available after the actual
clock edge and any still-active relay prefix. -/
theorem publicChoice_source_relay_eligibility_after_clock
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName who guard tail).decision)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (instruction : ApplicationInstruction P L) (activation : Activation Nat)
    (execution middle : runtime.application.PolicyExecution)
    (priorRelays : List (@Invocation P)) (relay : P)
    (howner : instruction.submitter = some who)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        (Invocation.environment :: priorRelays).countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 1)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hcode : runtime.image.lookup activation.key = some (.publicChoice
      ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
        fallback fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hconsistent : runtime.Consistent execution.native.application)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (hmiddleActive : runtime.image.activeAddress?
      middle.native.application.base.memory = some instruction.address)
    (hmiddle : middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (.environment :: priorRelays) execution).support) :
    let chosen := L.eval fallback.expr current.current.source.erasePubEnv
    ∃ payload resolved,
      runtime.dueExpiry?
        (middle.native.application.base.memory, middle.native.application.active) =
          some payload ∧
      middle.native.pool.lookup (relay, middle.native.pool.nextSerial relay) = none ∧
      runtime.handle middle.native.application
        ⟨(relay, middle.native.pool.nextSerial relay), payload⟩ = some resolved ∧
      ∃ next : CoupledAt
          (compileCore (.commit name who guard (.reveal publicName who name .here tail))
            fresh build).graph
          (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
            publicName who .here fresh.2.1).1,
        next.current.source = (current.current.source.cons chosen).cons chosen ∧
        resolved.base.Refines next.current.graph.1 := by
  have hinitialIndex := hindex execution.environmentHistory.length
    (Nat.le_refl _) (by
      simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte]
      omega)
  obtain ⟨clocked, hclockLaw, hclock, hclockRefines, hclockActivation,
      hclockActive⟩ := runtime.block_clock_step_checkpoint roster players execution
    instruction activation current.current.graph.1 hinitialIndex hslot hactive
    hactivation hkey hrefines
  have hclockedSupport : clocked ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) [.environment] execution).support := by
    rw [hclockLaw]
    simp
  have hclockedLength := runtime.application.runPolicies_environmentHistory_length players
    (runtime.blockEnvironment roster) [.environment] execution clocked hclockedSupport
  have hmiddleTail : middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) priorRelays clocked).support := by
    rw [show Invocation.environment :: priorRelays =
      [Invocation.environment] ++ priorRelays by rfl,
      MessageApplication.runPolicies_append, hclockLaw, FinDist.pure_bind] at hmiddle
    exact hmiddle
  obtain ⟨hmiddleRefines, hmiddleActivation, hclockMono⟩ :=
    runtime.runPolicies_refines_of_final_active roster players priorRelays clocked middle
      instruction who current.current.graph.1 howner (by
        intro index hlo hhi
        apply hindex index
        · omega
        · simp only [List.countP_cons, List.countP_nil,
            Invocation.isEnvironment, ↓reduceIte] at hclockedLength ⊢
          omega) hclockRefines hclockActive hmiddleActive hmiddleTail
  have hmiddleConsistent := runtime.runPolicies_consistent players
    (runtime.blockEnvironment roster) (.environment :: priorRelays) execution middle
    hconsistent hmiddle
  have hmiddleFresh := (runtime.application.runPolicies_serialsBeforeNext players
    (runtime.blockEnvironment roster) (.environment :: priorRelays) execution middle
    hserials hmiddle).lookup_nextSerial_eq_none relay
  have hmiddleActivation' : middle.native.application.active = some activation :=
    hmiddleActivation.trans (hclockActivation.trans hactivation)
  have hoverdue : activation.since + runtime.windowOf activation.key <
      middle.native.application.base.memory.clock := by
    rw [hkey]
    omega
  exact runtime.publicChoice_source_relay_eligibility guard tail fallback fresh build deadline
    current middle activation relay hmiddleConsistent hmiddleActivation' hcode hmiddleRefines
    heligible hoverdue hmiddleFresh

/-- An actual latest-submission service edge resolving a public choice carries
the accepted choice or certified fallback to its source successor. -/
theorem environment_latest_publicChoice_source_coupling
    (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (actor : P)
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName who guard tail).decision)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (execution next : runtime.application.PolicyExecution) (activation : Activation Nat)
    (hpolicy : environment execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native) =
        FinDist.pure (runtime.liftEnvironmentCommand
          (runtime.image.application.latestSubmissionCommand actor
            (runtime.eraseEnvironmentView
              (MessageApplication.State.environmentView runtime.application execution.native)))))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some ((PublicChoiceSite.atHead name publicName who guard tail).code
        fresh build).endpoint.publicationNode)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = ((PublicChoiceSite.atHead name publicName who guard tail).code
      fresh build).endpoint.publicationNode)
    (hcode : runtime.image.lookup ((PublicChoiceSite.atHead name publicName who guard tail).code
      fresh build).endpoint.publicationNode = some (.publicChoice
          ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
            fallback fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? next.native.application.base.memory ≠
      some ((PublicChoiceSite.atHead name publicName who guard tail).code
        fresh build).endpoint.publicationNode)
    (hnext : next ∈ (runtime.application.invoke players environment execution
      .environment).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1),
      evalGuard guard chosen ((current.current.source.toView who).eraseEnv) = true ∧
        sourceNext.current.source = (current.current.source.cons chosen).cons chosen ∧
        next.native.application.base.Refines sourceNext.current.graph.1 ∧
        next.native.application.FreshActivation := by
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let Witness := { pair :
    L.Val ty × CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph
      (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1 //
    evalGuard guard pair.1 ((current.current.source.toView who).eraseEnv) = true ∧
      pair.2.current.source = (current.current.source.cons pair.1).cons pair.1 }
  let target : Witness → Config
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph := fun witness => witness.1.2.current.graph.1
  obtain ⟨witness, hnextRefines, hnextFresh, _⟩ :=
    runtime.environment_latest_source_witness players environment actor execution next
      (site.code fresh build).endpoint.publicationNode Witness target (fun _ _ => True)
      hpolicy hactive hinactive (by
        intro message resolved hhandle
        obtain ⟨chosen, sourceNext, hlegal, hsource, hresolved⟩ :=
          runtime.handle_publicChoice_or_expiry_source_coupling guard tail fallback fresh build
            deadline current heligible execution.native.application resolved activation
            (site.code fresh build).endpoint.publicationNode message hactivation hkey hcode
            hrefines hhandle
        exact ⟨⟨(chosen, sourceNext), hlegal, hsource⟩, hresolved,
          runtime.handle_freshActivation execution.native.application resolved _ hhandle,
          trivial⟩)
      hnext
  exact ⟨witness.1.1, witness.1.2, witness.2.1, witness.2.2,
    hnextRefines, hnextFresh⟩

/-- Source coupling at the ordinary service slot of a public-choice block. -/
theorem blockEnvironment_normal_publicChoice_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName who guard tail).decision)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (execution next : runtime.application.PolicyExecution) (activation : Activation Nat)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some (.publicChoice
        ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
          fallback fresh build deadline)))
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 0)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some ((PublicChoiceSite.atHead name publicName who guard tail).code
        fresh build).endpoint.publicationNode)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = ((PublicChoiceSite.atHead name publicName who guard tail).code
      fresh build).endpoint.publicationNode)
    (hcode : runtime.image.lookup
      ((PublicChoiceSite.atHead name publicName who guard tail).code fresh build
        |>.endpoint.publicationNode) = some (.publicChoice
          ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
            fallback fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? next.native.application.base.memory ≠
      some ((PublicChoiceSite.atHead name publicName who guard tail).code
        fresh build).endpoint.publicationNode)
    (hnext : next ∈ (runtime.application.invoke players
      (runtime.blockEnvironment roster) execution .environment).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1),
      evalGuard guard chosen ((current.current.source.toView who).eraseEnv) = true ∧
        sourceNext.current.source = (current.current.source.cons chosen).cons chosen ∧
        next.native.application.base.Refines sourceNext.current.graph.1 ∧
        next.native.application.FreshActivation := by
  let site := PublicChoiceSite.atHead name publicName who guard tail
  apply runtime.environment_latest_publicChoice_source_coupling players
    (runtime.blockEnvironment roster)
    (site.timeoutCode fallback fresh build deadline).endpoint.owner guard tail fallback fresh
    build deadline current
    heligible execution next activation
  · exact runtime.blockEnvironment_normal roster execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native)
      (.publicChoice (site.timeoutCode fallback fresh build deadline)) hindex hactive hslot |>.trans
        (by simp [ApplicationImage.serviceCommand])
  · exact hactive
  · exact hactivation
  · exact hkey
  · exact hcode
  · exact hrefines
  · exact hinactive
  · exact hnext

/-- Source coupling at a reserved relay slot of a public-choice block. -/
theorem blockEnvironment_relay_publicChoice_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy) (actor : P) (rosterIndex : Nat)
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName who guard tail).decision)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (execution next : runtime.application.PolicyExecution) (activation : Activation Nat)
    (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length % (roster.length + 2) = rosterIndex + 2)
    (hwho : roster[rosterIndex]? = some actor)
    (hinstruction : instruction = .publicChoice
      ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
        fallback fresh build deadline))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hcode : runtime.image.lookup instruction.address = some instruction)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? next.native.application.base.memory ≠
      some instruction.address)
    (hnext : next ∈ (runtime.application.invoke players
      (runtime.blockEnvironment roster) execution .environment).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1),
      evalGuard guard chosen ((current.current.source.toView who).eraseEnv) = true ∧
        sourceNext.current.source = (current.current.source.cons chosen).cons chosen ∧
        next.native.application.base.Refines sourceNext.current.graph.1 ∧
        next.native.application.FreshActivation := by
  subst instruction
  let site := PublicChoiceSite.atHead name publicName who guard tail
  apply runtime.environment_latest_publicChoice_source_coupling players
    (runtime.blockEnvironment roster) actor guard tail fallback fresh build deadline current
    heligible execution next activation
  · have hpolicy := runtime.blockEnvironment_relay roster execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native)
      (.publicChoice (site.timeoutCode fallback fresh build deadline)) rosterIndex actor hindex
      hactive hslot hwho
    refine hpolicy.trans (congrArg FinDist.pure ?_)
    simp only [MessageApplication.latestSubmissionCommand, eraseEnvironmentView,
      MessageApplication.State.environmentView, WindowedApplication.application]
    cases hserial : execution.native.pool.nextSerial actor with
    | zero => rfl
    | succ serial =>
        simp only [liftEnvironmentCommand]
        split <;> rfl
  · exact hactive
  · exact hactivation
  · exact hkey
  · exact hcode
  · exact hrefines
  · exact hinactive
  · exact hnext

/-- An unchanged relay in a duplicate-free roster forces a ready public choice
inactive by the end of its complete relay suffix. -/
theorem publicChoice_relay_roster_inactive
    (runtime : WindowedApplication P L)
    (beforeRoster afterRoster : List P) (owner relay : P)
    (hroster : (beforeRoster ++ relay :: afterRoster).Nodup)
    (base : runtime.application.PlayerPolicy)
    (players : P → runtime.application.PlayerPolicy)
    (hrelay : players relay = runtime.blockPlayer relay base)
    {Γ : VCtx P L} {name publicName : VarId} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName owner guard tail).decision)
    (fresh : FreshBindings (.commit name owner guard (.reveal publicName owner name .here tail)))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh build).graph build)
    (heligible : (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable
      fresh build)
    (instruction : ApplicationInstruction P L) (activation : Activation Nat)
    (execution final : runtime.application.PolicyExecution)
    (howner : instruction.submitter = some owner)
    (hplayerIndex : runtime.image.instructions[(execution.principalHistory relay).length / 3]? =
      some instruction)
    (hplayerSlot : (execution.principalHistory relay).length % 3 = 2)
    (henvironmentSlot : execution.environmentHistory.length %
      ((beforeRoster ++ relay :: afterRoster).length + 2) = 1)
    (hindexRange : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        (beforeRoster.length + afterRoster.length + 2) →
      runtime.image.instructions[index /
        ((beforeRoster ++ relay :: afterRoster).length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hcode : runtime.image.lookup activation.key = some (.publicChoice
      ((PublicChoiceSite.atHead name publicName owner guard tail).timeoutCode
        fallback fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hconsistent : runtime.Consistent execution.native.application)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment (beforeRoster ++ relay :: afterRoster))
      ([Invocation.environment] ++ beforeRoster.flatMap (fun actor =>
        [Invocation.player actor, Invocation.environment]) ++
          [Invocation.player relay, Invocation.environment] ++
          afterRoster.flatMap (fun actor =>
            [Invocation.player actor, Invocation.environment]))
      execution).support) :
    runtime.image.activeAddress? final.native.application.base.memory ≠
      some instruction.address := by
  let roster := beforeRoster ++ relay :: afterRoster
  let before : List (@Invocation P) := [Invocation.environment] ++
    beforeRoster.flatMap fun actor => [Invocation.player actor, Invocation.environment]
  let suffix : List (@Invocation P) := afterRoster.flatMap fun actor =>
    [Invocation.player actor, Invocation.environment]
  have hrelayIndex : roster[beforeRoster.length]? = some relay := by
    simp [roster]
  apply runtime.runPolicies_relay_segment_inactive roster players relay base hrelay
    instruction beforeRoster.length hrelayIndex before suffix execution
  · intro middle hmiddle index hlo hhi
    have henvironmentLength := runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) before execution middle hmiddle
    apply hindexRange index
    · simp only [before, List.countP_append, List.countP_cons, List.countP_nil,
        Invocation.isEnvironment, ↓reduceIte, relayPrefix_environment_count]
        at henvironmentLength
      omega
    · simp only [before, suffix, List.countP_append, List.countP_cons,
        List.countP_nil, Invocation.isEnvironment, ↓reduceIte,
        Bool.false_eq_true, relayPrefix_environment_count] at hhi henvironmentLength ⊢
      omega
  · intro middle hmiddle hmiddleActive
    have hnotmem : relay ∉ beforeRoster := by
      intro hmem
      exact (List.nodup_append.mp hroster).2.2 relay hmem relay (by simp) rfl
    have hplayerLength := runtime.application.runPolicies_principalHistory_length relay
      players (runtime.blockEnvironment roster) before execution middle hmiddle
    have henvironmentLength := runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) before execution middle hmiddle
    simp only [before, List.countP_append, List.countP_cons, List.countP_nil,
      Invocation.isEnvironment, ↓reduceIte] at hplayerLength henvironmentLength
    have hplayerLength' : (middle.principalHistory relay).length =
        (execution.principalHistory relay).length := by
      rw [hplayerLength]
      simp only [Nat.add_eq_left, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      apply List.countP_eq_zero.mpr
      intro invocation hmem
      cases invocation with
      | environment => simp
      | player actor =>
          simp only [List.mem_flatMap] at hmem
          obtain ⟨candidate, hcandidate, hpair⟩ := hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
          rcases hpair with heq | hfalse
          · have hactor : actor = candidate := Invocation.player.inj heq
            subst actor
            intro h
            have heq : candidate = relay := of_decide_eq_true h
            exact hnotmem (heq ▸ hcandidate)
          · simp at hfalse
    rw [relayPrefix_environment_count] at henvironmentLength
    obtain ⟨payload, resolved, hdue, hfresh, hhandle, _⟩ :=
      runtime.publicChoice_source_relay_eligibility_after_clock roster players guard tail
        fallback fresh build deadline current heligible instruction activation execution middle
        (beforeRoster.flatMap fun actor =>
          [Invocation.player actor, Invocation.environment]) relay howner
        (by
          intro index hlo hhi
          apply hindexRange index hlo
          simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte,
            relayPrefix_environment_count] at hhi
          omega) henvironmentSlot hactive hactivation hkey hcode hrefines hconsistent
        hserials hmiddleActive (by simpa [before] using hmiddle)
    refine ⟨payload, resolved, ?_, ?_, ?_, ?_, hdue, hfresh, hhandle, ?_⟩
    · rwa [hplayerLength']
    · rwa [hplayerLength']
    · apply hindexRange middle.environmentHistory.length
      · omega
      · omega
    · have hslot' : execution.environmentHistory.length % (roster.length + 2) = 1 := by
        simpa [roster] using henvironmentSlot
      have hlt : 1 + beforeRoster.length < roster.length + 2 := by
        simp [roster]
        omega
      have hwhole : 1 + (1 + beforeRoster.length) < roster.length + 2 := by
        simp [roster]
        omega
      rw [henvironmentLength, Nat.add_mod, hslot', Nat.mod_eq_of_lt hlt,
        Nat.mod_eq_of_lt hwhole]
      omega
    · intro index hlo hhi
      apply hindexRange index
      · omega
      · simp only [suffix, relayPrefix_environment_count] at hhi ⊢
        omega
  · simpa [before, suffix, List.append_assoc] using hfinal

/-- The first resolving edge of an actual public-choice relay segment supplies
the source successor retained through the inactive suffix. -/
theorem runPolicies_publicChoice_relay_pairs_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (relays : List P) (rosterOffset : Nat)
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName who guard tail).decision)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (deadline : Nat) (execution final : runtime.application.PolicyExecution)
    (activation : Activation Nat)
    (hrelays : ∀ index actor, relays[index]? = some actor →
      roster[rosterOffset + index]? = some actor)
    (hbound : rosterOffset + relays.length ≤ roster.length)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + relays.length →
      runtime.image.instructions[index / (roster.length + 2)]? = some (.publicChoice
        ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
          fallback fresh build deadline)))
    (hslot : execution.environmentHistory.length % (roster.length + 2) = rosterOffset + 2)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some ((PublicChoiceSite.atHead name publicName who guard tail).code
        fresh build).endpoint.publicationNode)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = ((PublicChoiceSite.atHead name publicName who guard tail).code
      fresh build).endpoint.publicationNode)
    (hcode : runtime.image.lookup
      ((PublicChoiceSite.atHead name publicName who guard tail).code fresh build
        |>.endpoint.publicationNode) = some (.publicChoice
          ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
            fallback fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? final.native.application.base.memory ≠
      some ((PublicChoiceSite.atHead name publicName who guard tail).code
        fresh build).endpoint.publicationNode)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster)
      (relays.flatMap fun actor => [Invocation.player actor, .environment])
      execution).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1),
      evalGuard guard chosen ((current.current.source.toView who).eraseEnv) = true ∧
        sourceNext.current.source = (current.current.source.cons chosen).cons chosen ∧
        final.native.application.base.Refines sourceNext.current.graph.1 ∧
        final.native.application.FreshActivation := by
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let timed := site.timeoutCode fallback fresh build deadline
  let Witness := { pair :
    L.Val ty × CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph
      (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1 //
    evalGuard guard pair.1 ((current.current.source.toView who).eraseEnv) = true ∧
      pair.2.current.source = (current.current.source.cons pair.1).cons pair.1 }
  let target : Witness → Config
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph := fun witness => witness.1.2.current.graph.1
  obtain ⟨witness, hfinalRefines, hfinalFresh, _⟩ :=
    runtime.runPolicies_relay_pairs_source_witness roster players relays rosterOffset
      (.publicChoice timed) who current.current.graph.1 execution final activation Witness target
      (fun _ _ => True) hrelays hbound hindex hslot (by rfl) hactive hactivation hrefines
      hinactive (by
        intro actor index afterPlayer afterRelay hactor hrelayIndex hrelaySlot
          hplayerActive hplayerActivation hplayerRefines hafterInactive henvironment
        obtain ⟨chosen, sourceNext, hlegal, hsource, hnextRefines, hnextFresh⟩ :=
          runtime.blockEnvironment_relay_publicChoice_source_coupling roster players actor index
            guard tail fallback fresh build deadline current heligible afterPlayer afterRelay
            activation (.publicChoice timed) hrelayIndex hrelaySlot hactor rfl hplayerActive
            hplayerActivation hkey hcode hplayerRefines hafterInactive henvironment
        exact ⟨⟨(chosen, sourceNext), hlegal, hsource⟩, hnextRefines, hnextFresh,
          trivial⟩)
      (by intro witness before after schedule hcertificate hinactive hsupported _; trivial)
      hfinal
  exact ⟨witness.1.1, witness.1.2, witness.2.1, witness.2.2,
    hfinalRefines, hfinalFresh⟩

end Vegas.WindowedApplication

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name publicName : VarId} {owner : P} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
variable {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ}

/-- A complete generated service block resolves a public-choice head to a
legal two-node source successor. A roster relay running the reference policy
supplies permissionless fallback settlement. -/
theorem publicChoice_block_resolution
    (publicGuard : (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable
      fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName owner guard tail).decision)
    (deadline : Nat)
    (hselect : choice ((PublicChoiceSite.atHead name publicName owner guard tail).code
      fresh state) = some ⟨deadline, fallback.compiled fresh state⟩)
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.publicChoice (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile current execution)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster)
    (hreference :
      root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement relay =
        root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf relay)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
          fresh state).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1),
      evalGuard guard chosen ((current.current.source.toView owner).eraseEnv) = true ∧
        sourceNext.current.source = (current.current.source.cons chosen).cons chosen ∧
        final.native.application.base.Refines sourceNext.current.graph.1 ∧
        final.native.application.FreshActivation ∧
        (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
          final.native.application.base.memory ≠
            some ((PublicChoiceSite.atHead name publicName owner guard tail).code
              fresh state).endpoint.publicationNode := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let site := PublicChoiceSite.atHead name publicName owner guard tail
  let code := site.code fresh state
  let timed := site.timeoutCode fallback fresh state deadline
  let before := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let relayPairs := roster.flatMap fun actor => [Invocation.player actor, .environment]
  have hhead : (ApplicationPlan.publicChoice (newName := newName) (unresolved := unresolved)
      (fresh := fresh) publicGuard nextPlan).instructions deadlineOf =
        .publicChoice code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := checkpoint.instruction_at (.publicChoice code) _ hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.publicChoice code)
    (List.mem_of_getElem? hindexOriginal)
  change (root.image deadlineOf).lookup code.endpoint.publicationNode =
    some (.publicChoice code) at hlookupOriginal
  have hlookup : runtime.image.lookup timed.endpoint.publicationNode =
      some (.publicChoice timed) := by
    change runtime.image.lookup code.endpoint.publicationNode = some (.publicChoice timed)
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts]
    rw [hlookupOriginal]
    simp only [Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
    have hselect' : choice code = some (site.timeout fallback fresh state deadline) := by
      simpa only [code, site, PublicChoiceSite.timeout] using hselect
    rw [hselect']
    rfl
  have hlength := checkpoint.environmentHistory_length
  have hquotient : execution.environmentHistory.length / (roster.length + 2) =
      blockIndex := by
    rw [hlength, Nat.mul_div_cancel]
    omega
  have hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some (.publicChoice timed) := by
    simp only [hquotient, runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
    have hselect' : choice code = some (site.timeout fallback fresh state deadline) := by
      simpa only [code, site, PublicChoiceSite.timeout] using hselect
    rw [hselect']
    rfl
  have hindexBlock : runtime.image.instructions[blockIndex]? = some (.publicChoice timed) := by
    rwa [hquotient] at hindex
  have hindexRange : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + roster.length + 2 →
      runtime.image.instructions[index / (roster.length + 2)]? =
        some (.publicChoice timed) := by
    intro index hlo hhi
    have hsame : index / (roster.length + 2) =
        execution.environmentHistory.length / (roster.length + 2) := by
      have hmod : execution.environmentHistory.length % (roster.length + 2) = 0 := by
        rw [hlength]
        exact Nat.mul_mod_left _ _
      have hbase := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
      apply Nat.div_eq_of_lt_le
      · rw [hbase]
        omega
      · rw [Nat.add_mul, hbase]
        omega
    rw [hsame]
    exact hindex
  have hactiveExecution := checkpoint.activeAddress?_head (.publicChoice code) _ hhead
  obtain ⟨activation, hactivationExecution, hkeyOriginal, _⟩ :=
    checkpoint.active_origin_clock (.publicChoice code) _ hhead
  have hkey : activation.key = timed.endpoint.publicationNode := hkeyOriginal
  have hbeforeNoEnvironment : Invocation.environment ∉ before := by
    simp [before]
  have hbeforeCount : before.countP Invocation.isEnvironment = 0 := by
    apply List.countP_eq_zero.mpr
    intro invocation hmem
    rcases List.mem_flatMap.mp hmem with ⟨actor, _, hpair⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
    rcases hpair with hpair | hpair <;> subst invocation <;>
      simp [Invocation.isEnvironment]
  have hrelayCount : relayPairs.countP Invocation.isEnvironment = roster.length := by
    have relayCount : ∀ entries : List P,
        (entries.flatMap fun actor => [Invocation.player actor, .environment]).countP
          Invocation.isEnvironment = entries.length := by
      intro entries
      induction entries with
      | nil => rfl
      | cons actor rest ih =>
          simp only [List.flatMap_cons, List.countP_append, List.countP_cons,
            List.countP_nil, Invocation.isEnvironment, Bool.false_eq_true,
            ↓reduceIte, ih, List.length_cons, Nat.add_comm]
    exact relayCount roster
  have hrosterPositive : 0 < roster.length := by
    obtain ⟨index, hindexLt, _⟩ := List.mem_iff_getElem.mp hrelay
    omega
  have hdecomposed : WindowedApplication.blockInvocations roster =
      before ++ (Invocation.environment :: Invocation.environment :: relayPairs) := by
    simp only [WindowedApplication.blockInvocations, before, relayPairs,
      List.cons_append, List.nil_append, List.append_assoc]
  rw [hdecomposed, MessageApplication.runPolicies_append] at hfinal
  simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
  obtain ⟨polled, hpolled, hremaining⟩ := hfinal
  rw [show Invocation.environment :: Invocation.environment :: relayPairs =
    [Invocation.environment] ++ (Invocation.environment :: relayPairs) by rfl,
    MessageApplication.runPolicies_append] at hremaining
  simp only [FinDist.support_bind, Set.mem_iUnion] at hremaining
  obtain ⟨included, hincludedRun, hafterIncluded⟩ := hremaining
  have hincluded : included ∈ (runtime.application.invoke players
      (runtime.blockEnvironment roster) polled .environment).support := by
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincludedRun
  have hpublicPolled := runtime.runPolicies_players_publicState players
    (runtime.blockEnvironment roster) before hbeforeNoEnvironment execution polled hpolled
  have hmemoryPolled := congrArg Prod.fst hpublicPolled
  change polled.native.application.base.memory = execution.native.application.base.memory
    at hmemoryPolled
  have hactivePolled : runtime.image.activeAddress?
      polled.native.application.base.memory = some timed.endpoint.publicationNode := by
    rw [hmemoryPolled]
    exact hactiveExecution
  have hactivationPolledEq := congrArg Prod.snd hpublicPolled
  change polled.native.application.active = execution.native.application.active
    at hactivationPolledEq
  have hactivationPolled : polled.native.application.active = some activation :=
    hactivationPolledEq.trans hactivationExecution
  have hrefinesPolled := runtime.runPolicies_players_refines players
    (runtime.blockEnvironment roster) before hbeforeNoEnvironment execution polled
    checkpoint.refines hpolled
  have hpolledLength := runtime.application.runPolicies_environmentHistory_length players
    (runtime.blockEnvironment roster) before execution polled hpolled
  rw [hbeforeCount, Nat.add_zero] at hpolledLength
  have hindexPolled : runtime.image.instructions[polled.environmentHistory.length /
      (roster.length + 2)]? = some (.publicChoice timed) := by
    rw [hpolledLength]
    exact hindex
  have hslotPolled : polled.environmentHistory.length % (roster.length + 2) = 0 := by
    rw [hpolledLength, hlength]
    exact Nat.mul_mod_left _ _
  have hincludedLength := runtime.application.runPolicies_environmentHistory_length players
    (runtime.blockEnvironment roster) [Invocation.environment] polled included hincludedRun
  simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment, ↓reduceIte,
    Nat.zero_add] at hincludedLength
  by_cases hincludedInactive : runtime.image.activeAddress?
      included.native.application.base.memory ≠ some timed.endpoint.publicationNode
  · obtain ⟨chosen, sourceNext, hlegal, hsource, hincludedRefines, hincludedFresh⟩ :=
      runtime.blockEnvironment_normal_publicChoice_source_coupling roster players guard tail
        fallback fresh state deadline current publicGuard polled included activation hindexPolled
        hslotPolled hactivePolled hactivationPolled hkey hlookup hrefinesPolled
        hincludedInactive hincluded
    have hremainingIndex : ∀ index, included.environmentHistory.length ≤ index →
        index < included.environmentHistory.length +
          (Invocation.environment :: relayPairs).countP Invocation.isEnvironment →
        runtime.image.instructions[index / (roster.length + 2)]? =
          some (.publicChoice timed) := by
      intro index hlo hhi
      apply hindexRange index
      · omega
      · simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte,
          hrelayCount] at hhi
        omega
    have hpublicFinal := runtime.runPolicies_block_inactive roster players
      (Invocation.environment :: relayPairs) included final (.publicChoice timed)
      hremainingIndex hincludedInactive hafterIncluded
    have hfinalInactive : runtime.image.activeAddress?
        final.native.application.base.memory ≠ some timed.endpoint.publicationNode := by
      have hmemory := congrArg Prod.fst hpublicFinal
      change final.native.application.base.memory = included.native.application.base.memory
        at hmemory
      rwa [hmemory]
    refine ⟨chosen, sourceNext, hlegal, hsource, ?_, ?_, ?_⟩
    · exact runtime.runPolicies_block_inactive_refines sourceNext.current.graph.1 roster
        players (Invocation.environment :: relayPairs) included final (.publicChoice timed)
        hremainingIndex hincludedInactive hincludedRefines hafterIncluded
    · exact runtime.runPolicies_block_inactive_freshActivation roster players
        (Invocation.environment :: relayPairs) included final (.publicChoice timed)
        hremainingIndex hincludedInactive hincludedFresh hafterIncluded
    · exact hfinalInactive
  · have hincludedActive : runtime.image.activeAddress?
        included.native.application.base.memory = some timed.endpoint.publicationNode :=
      Classical.byContradiction hincludedInactive
    obtain ⟨hincludedRefines, hincludedActivationEq, _⟩ :=
      runtime.invoke_refines_of_active roster players polled included .environment
        (.publicChoice timed) owner current.current.graph.1 hindexPolled (by rfl) hrefinesPolled
        hactivePolled hincludedActive hincluded
    have hactivationIncluded : included.native.application.active = some activation :=
      hincludedActivationEq.trans hactivationPolled
    have hslotIncluded : included.environmentHistory.length % (roster.length + 2) = 1 := by
      rw [hincludedLength, hpolledLength, hlength]
      simp [Nat.add_mod]
    have hindexIncluded : runtime.image.instructions[included.environmentHistory.length /
        (roster.length + 2)]? = some (.publicChoice timed) := by
      apply hindexRange included.environmentHistory.length
      · rw [hincludedLength, hpolledLength]
        omega
      · rw [hincludedLength, hpolledLength]
        omega
    obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp hrelay
    have hrelayPolicy : players relay = runtime.blockPlayer relay
        (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile relay)) :=
      hreference
    have hprincipalStart := checkpoint.historyAlignment hroster relay hrelay |>.1
    have hprincipalPolled := runtime.application.runPolicies_principalHistory_length relay
      players (runtime.blockEnvironment roster) before execution polled hpolled
    have hpolls := WindowedApplication.ordinaryPolls_player_count roster hroster relay
    change before.countP _ = _ at hpolls
    have hprincipalPolled' : (polled.principalHistory relay).length =
        3 * blockIndex + 2 := by
      have hcounted := hprincipalPolled.trans
        (congrArg (fun count => (execution.principalHistory relay).length + count) hpolls)
      simp only [hrelay, if_pos] at hcounted
      omega
    have hprincipalIncluded := runtime.application.runPolicies_principalHistory_length relay
      players (runtime.blockEnvironment roster) [Invocation.environment] polled included
      hincludedRun
    simp only [List.countP_cons, List.countP_nil, Bool.false_eq_true, ↓reduceIte,
      Nat.add_zero] at hprincipalIncluded
    have hplayerIndex : runtime.image.instructions[(included.principalHistory relay).length / 3]? =
        some (.publicChoice timed) := by
      rw [hprincipalIncluded, hprincipalPolled']
      have hdivision : (3 * blockIndex + 2) / 3 = blockIndex := by omega
      rw [hdivision]
      exact hindexBlock
    have hplayerSlot : (included.principalHistory relay).length % 3 = 2 := by
      rw [hprincipalIncluded, hprincipalPolled']
      omega
    have hprefixSupport : included ∈ (runtime.application.runPolicies players
        (runtime.blockEnvironment roster) (before ++ [Invocation.environment])
        execution).support := by
      rw [MessageApplication.runPolicies_append, FinDist.support_bind]
      exact Set.mem_iUnion.mpr ⟨polled, Set.mem_iUnion.mpr ⟨hpolled, hincludedRun⟩⟩
    have hsettled : runtime.image.activeAddress? final.native.application.base.memory ≠
        some timed.endpoint.publicationNode := by
      have hrosterSplit : (beforeRoster ++ relay :: afterRoster).Nodup := by
        rwa [← hsplit]
      apply runtime.publicChoice_relay_roster_inactive beforeRoster afterRoster owner relay
        hrosterSplit (runtime.liftPlayerPolicy
          (root.liftProfile deadlineOf rootProfile relay)) players hrelayPolicy guard tail fallback
        fresh state deadline current publicGuard (.publicChoice timed) activation included final
        (by rfl) hplayerIndex hplayerSlot
      · simpa [← hsplit] using hslotIncluded
      · intro index hlo hhi
        have hsplitLength := congrArg List.length hsplit
        simp only [List.length_append, List.length_cons] at hsplitLength
        have hsame := hindexRange index (by omega) (by omega)
        rw [hsplit] at hsame
        exact hsame
      · exact hincludedActive
      · exact hactivationIncluded
      · exact hkey
      · rw [hkey]
        exact hlookup
      · exact hincludedRefines
      · exact runtime.runPolicies_consistent players (runtime.blockEnvironment roster)
          (before ++ [Invocation.environment]) execution included checkpoint.consistent
          hprefixSupport
      · exact runtime.application.runPolicies_serialsBeforeNext players
          (runtime.blockEnvironment roster) (before ++ [Invocation.environment]) execution
          included checkpoint.serialsBeforeNext hprefixSupport
      · simpa [relayPairs, hsplit, List.append_assoc] using hafterIncluded
    obtain ⟨clocked, hclockLaw, _, hclockedRefines, hclockedActivationEq,
        hclockedActive⟩ :=
      runtime.block_clock_step_checkpoint roster players included (.publicChoice timed) activation
        current.current.graph.1 hindexIncluded hslotIncluded hincludedActive
        hactivationIncluded hkey hincludedRefines
    have hrelayFinal : final ∈ (runtime.application.runPolicies players
        (runtime.blockEnvironment roster) relayPairs clocked).support := by
      rw [show Invocation.environment :: relayPairs =
        [Invocation.environment] ++ relayPairs by rfl,
        MessageApplication.runPolicies_append, hclockLaw, FinDist.pure_bind] at hafterIncluded
      exact hafterIncluded
    have hclockedLength := runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) [Invocation.environment] included clocked (by
        rw [hclockLaw]
        exact FinDist.mem_support_pure.mpr rfl)
    simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment, ↓reduceIte,
      Nat.zero_add] at hclockedLength
    obtain ⟨chosen, sourceNext, hlegal, hsource, hfinalRefines, hfinalFresh⟩ :=
      runtime.runPolicies_publicChoice_relay_pairs_source_coupling roster players roster 0 guard
        tail fallback fresh state current publicGuard deadline clocked final activation
        (by intro index actor hactor; simpa using hactor) (by simp)
        (by
          intro index hlo hhi
          apply hindexRange index
          · omega
          · omega)
        (by
          rw [hclockedLength, hincludedLength, hpolledLength, hlength]
          have htwo : 2 < roster.length + 2 := by omega
          simp [Nat.add_mod, Nat.mod_eq_of_lt htwo])
        hclockedActive (hclockedActivationEq.trans hactivationIncluded) hkey hlookup
        hclockedRefines hsettled hrelayFinal
    refine ⟨chosen, sourceNext, hlegal, hsource, hfinalRefines, hfinalFresh, ?_⟩
    exact hsettled

/-- Every supported complete public-choice block produces a genuine successor
checkpoint for the commit/reveal continuation, together with its actual legal
source value and settlement of the predecessor address. -/
theorem publicChoice_block
    (publicGuard : (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable
      fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName owner guard tail).decision)
    (deadline : Nat)
    (hselect : choice ((PublicChoiceSite.atHead name publicName owner guard tail).code
      fresh state) = some ⟨deadline, fallback.compiled fresh state⟩)
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.publicChoice (newName := newName)
        (unresolved := unresolved) publicGuard nextPlan) profile current execution)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster)
    (hreference :
      root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement relay =
        root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf relay)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
          fresh state).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1),
      sourceNext.current.source = (current.current.source.cons chosen).cons chosen ∧
        evalGuard guard chosen ((current.current.source.toView owner).eraseEnv) = true ∧
        SmallStep.Star
          ⟨Γ, current.current.source,
            .commit name owner guard (.reveal publicName owner name .here tail)⟩
          ⟨(publicName, .pub ty) :: (name, .sealed owner ty) :: Γ,
            sourceNext.current.source, tail⟩ ∧
        WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster focal
          replacement (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
            sourceNext final ∧
        (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
          final.native.application.base.memory ≠
            some ((PublicChoiceSite.atHead name publicName owner guard tail).code
              fresh state).endpoint.publicationNode := by
  obtain ⟨chosen, sourceNext, hlegal, hsource, hrefines, hfresh, hinactive⟩ :=
    publicChoice_block_resolution publicGuard nextPlan profile fallback deadline hselect current
      execution final checkpoint hroster relay hrelay hreference hfinal
  have hsteps := (PublicChoiceSite.atHead name publicName owner guard tail)
    |>.completePublication_source_steps current.current.source chosen hlegal
  rw [← hsource] at hsteps
  refine ⟨chosen, sourceNext, hsource, hlegal, hsteps, ?_, hinactive⟩
  refine ⟨.publicChoice checkpoint.continuation, ?_, hrefines,
    checkpoint.reached_after_block final hfinal, ?_, hfresh⟩
  · have hcount := checkpoint.blockCount
    have hhead : (ApplicationPlan.publicChoice (newName := newName)
        (unresolved := unresolved) (fresh := fresh) publicGuard nextPlan).instructions deadlineOf =
          .publicChoice ((PublicChoiceSite.atHead name publicName owner guard tail).code
            fresh state) :: nextPlan.instructions deadlineOf := rfl
    rw [hhead, List.length_cons] at hcount
    omega
  · exact block_caches (.publicChoice (newName := newName) (unresolved := unresolved)
      (fresh := fresh) publicGuard nextPlan) nextPlan profile deadlineOf _ rfl binding choice
      windowOf roster hroster focal replacement blockIndex current execution final checkpoint
      hfinal

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_block_resolution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_block_resolution

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_block'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.publicChoice_block
