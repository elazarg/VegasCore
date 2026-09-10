/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationContinuationReadout
import Vegas.Compile.ApplicationInitialReads
import Vegas.Compile.PublicChoicePhaseExecution
import Vegas.Compile.BindingPhaseExecution
import Interaction.MessageApplicationCounters

/-! # An unchanged player's choices after arbitrary native interaction

Only the current owner must retain its original lifted source policy. Other
players, the preceding invocation schedule, and the preceding environment may
be arbitrary. The source checkpoint, fresh own decision cache, and immediate
inclusion of this phase's submission remain explicit premises.

The conclusion gives the full native phase law and its exact source successor.
It neither resamples an already cached choice nor establishes a source-local
backtranslation for a deviating owner.
-/

noncomputable section

namespace Vegas.ApplicationPlan.ProfileContinuation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- An unchanged owner's fresh public-choice kernel survives arbitrary
initialized native interaction by the other principals. The environment used
for the following phase need not be the one used for the prefix; it must include
the freshly submitted envelope on every supported branch. Source state and
compiler cursor are proof witnesses, never policy inputs. -/
theorem publicChoice_phase_of_unchanged_owner
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg}
    {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
    {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ}
    {publicGuard : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh state}
    {nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1}
    {profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail))}
    (continuation : ProfileContinuation root rootProfile
      (.publicChoice (newName := newName) (unresolved := unresolved)
        (fresh := fresh) publicGuard nextPlan) profile)
    (deadlineOf : Nat → Nat)
    (players : P → (root.image deadlineOf).application.PlayerPolicy)
    (howner : players who = root.liftProfile deadlineOf rootProfile who)
    (priorEnvironment : (root.image deadlineOf).application.EnvironmentPolicy)
    (previous : List (@Invocation P))
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (hreached : execution ∈ ((root.image deadlineOf).application.runPolicies
      players priorEnvironment previous
      (PolicyExecution.initial (root.image deadlineOf).application
        (MessageApplication.State.initial (root.image deadlineOf).application
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial
              (compileCore rootProg rootFresh rootState).graph))))).support)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state).graph state)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (hinitial : BuildResult.InitialReadsPublic
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state) (eventGuardOf state who guard).choiceReads)
    (hcache : ChoiceEncoding.cachedValue (root.image deadlineOf).application
      ((ApplicationImage.choiceEncoding (P := P) (state.nodes.length + 1) ty).submission
        (root.image deadlineOf).application) (execution.principalHistory who) = none)
    (environment : (root.image deadlineOf).application.EnvironmentPolicy)
    (henvironment : ∀ chosen ∈
        (profile who (.here guard (.reveal publicName who name .here tail))
          ((current.current.source.toView who).eraseEnv)).support,
      ∀ submitted ∈ ((root.image deadlineOf).application.playerStep who execution
        (.submit ((ApplicationImage.choiceEncoding (state.nodes.length + 1) ty).encode
          chosen.1))).support,
      environment submitted.environmentHistory
          (State.environmentView (root.image deadlineOf).application submitted.native) =
        FinDist.pure (.include (who, execution.native.pool.nextSerial who))) :
    let image := root.image deadlineOf
    let site := PublicChoiceSite.atHead name publicName who guard tail
    let code := site.code fresh state
    let choices := profile who site.decision ((current.current.source.toView who).eraseEnv)
    let encoding := ApplicationImage.choiceEncoding (P := P) code.endpoint.publicationNode ty
    let id := (who, execution.native.pool.nextSerial who)
    (image.application.runPolicies players environment [.player who, .environment] execution =
      choices.bind fun chosen =>
        (image.application.playerStep who execution (.submit (encoding.encode chosen.1))).bind
          fun submitted => image.application.environmentPolicyStep submitted (.include id)) ∧
    (∀ chosen ∈ choices.support,
      ∀ submitted ∈ (image.application.playerStep who execution
        (.submit (encoding.encode chosen.1))).support,
      ∀ included ∈ (image.application.environmentPolicyStep submitted (.include id)).support,
      ∃ next : CoupledAt
          (compileCore (.commit name who guard (.reveal publicName who name .here tail))
            fresh state).graph
          (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
            publicName who .here fresh.2.1).1,
        next.current.source = (current.current.source.cons chosen.1).cons chosen.1 ∧
          included.native.application.Refines next.current.graph.1) ∧
    ∀ _hactive : image.activeAddress? execution.native.application.memory =
        some code.endpoint.publicationNode,
      image.orderedApplication.runPolicies players environment
          [.player who, .environment] execution =
        image.application.runPolicies players environment
          [.player who, .environment] execution := by
  let image := root.image deadlineOf
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let code := site.code fresh state
  have hmem : ApplicationInstruction.publicChoice code ∈ root.instructions deadlineOf := by
    obtain ⟨before, hbefore⟩ := continuation.instructions_suffix deadlineOf
    rw [hbefore]
    exact List.mem_append_right before List.mem_cons_self
  have hcode : image.lookup code.endpoint.publicationNode = some (.publicChoice code) :=
    root.image_lookup_of_mem deadlineOf (.publicChoice code) hmem
  have hready := current.current.nextReady current.completedPrefix
    (site.choiceNode fresh state) rfl
  obtain ⟨reads, hreadout, hreads, _⟩ :=
    continuation.runPolicies_ownerReadout?_of_ready_source_view deadlineOf who players howner
      priorEnvironment previous execution hreached site.decision current.current.graph.1
      hrefines hready hinitial current.current.source
      (BuildState.Agrees.view current.current.agrees who)
  have hunresolved : execution.native.application.memory.done (state.nodes.length + 1) =
      false := by
    apply Bool.eq_false_iff.mpr
    intro hdone
    have hdoneGraph := (hrefines.memory.completed (site.publicationNode fresh state)).mp hdone
    have hlt := (current.completedPrefix _).mp hdoneGraph
    change state.nodes.length + 1 < state.nodes.length at hlt
    omega
  have hdoneView : (State.observe image.application execution.native who).application.done
      (state.nodes.length + 1) = false := hunresolved
  have hpolicy : ∀ history,
      players who history (State.observe image.application execution.native who) =
        (site.imageController fresh state image
          (image.ownerReadout? who (eventGuardOf state who guard).choiceReads)
          (profile who site.decision) (fun _ _ => false)).policy image.application history
            (State.observe image.application execution.native who) := by
    intro history
    rw [howner]
    unfold ApplicationPlan.liftProfile
    rw [continuation.liftProfileIn_eq_of_refines image deadlineOf current
      execution.native hrefines who history]
    simp only [ApplicationPlan.liftProfileIn, hdoneView, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hlookup := image.application.runPolicies_initial_lookup_nextSerial_eq_none
    players priorEnvironment previous
    (ApplicationImage.State.initial
      (ApplicationImage.Memory.initial (compileCore rootProg rootFresh rootState).graph))
    execution hreached who
  exact PublicChoiceSite.publicChoice_head_phase_source_law guard tail fresh state current
    image (profile who site.decision) players environment execution hrefines publicGuard hcode
    reads hpolicy henvironment hlookup hcache hreadout hreads

/-- An unchanged owner's fresh opaque-binding kernel after an arbitrary
initialized native prefix. The included handle has the exact acceptance-time
snapshot of the sampled source value. Other owners need not use lifted policies
or have canonical registrations. -/
theorem binding_phase_of_unchanged_owner
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg}
    {name : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (insert name pending) tail}
    {fresh : FreshBindings (.commit name who guard tail)} {state : BuildState P L Γ}
    {unrestricted : UnrestrictedBinding guard}
    {nextPlan : ApplicationPlan accounted fresh.2 (state.addCommitEvent name who guard fresh.1).1}
    {profile : SourceBehavioralProfile (.commit name who guard tail)}
    (continuation : ProfileContinuation root rootProfile
      (.binding (newName := newName) (fresh := fresh) unrestricted nextPlan) profile)
    (deadlineOf : Nat → Nat)
    (players : P → (root.image deadlineOf).application.PlayerPolicy)
    (howner : players who = root.liftProfile deadlineOf rootProfile who)
    (priorEnvironment : (root.image deadlineOf).application.EnvironmentPolicy)
    (previous : List (@Invocation P))
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (hreached : execution ∈ ((root.image deadlineOf).application.runPolicies
      players priorEnvironment previous
      (PolicyExecution.initial (root.image deadlineOf).application
        (MessageApplication.State.initial (root.image deadlineOf).application
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial
              (compileCore rootProg rootFresh rootState).graph))))).support)
    (current : CoupledAt (compileCore (.commit name who guard tail) fresh state).graph state)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (hinitial : BuildResult.InitialReadsPublic (compileCore (.commit name who guard tail)
      fresh state) (eventGuardOf state who guard).choiceReads)
    (hcache : (root.image deadlineOf).registrationCache state.nextField
      (execution.principalHistory who) = none)
    (hsubmitted : ChoiceEncoding.cachedValue (root.image deadlineOf).application
      (((.here guard tail : SourceDecisionSite who (.commit name who guard tail)
        Γ name ty guard).bindingCode fresh state state.nextField).encoding.submission
          (root.image deadlineOf).application) (execution.principalHistory who) = none)
    (environment : (root.image deadlineOf).application.EnvironmentPolicy)
    (henvironment : ∀ chosen ∈
        (profile who (.here guard tail) ((current.current.source.toView who).eraseEnv)).support,
      ∀ registered ∈ ((root.image deadlineOf).application.playerStep who execution
        (.privateCommand (.register state.nextField ⟨ty, chosen.1⟩))).support,
      ∀ submitted ∈ ((root.image deadlineOf).application.playerStep who registered
        (.submit (.binding state.nodes.length (who, state.nextField)))).support,
      environment submitted.environmentHistory
          (State.environmentView (root.image deadlineOf).application submitted.native) =
        FinDist.pure (.include (who, execution.native.pool.nextSerial who))) :
    let image := root.image deadlineOf
    let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
      .here guard tail
    let field := site.compiledField fresh state
    let code := site.bindingCode fresh state field
    let choices := profile who site ((current.current.source.toView who).eraseEnv)
    let id := (who, execution.native.pool.nextSerial who)
    (image.application.runPolicies players environment
        [.player who, .player who, .environment] execution =
      choices.bind fun chosen =>
        (image.application.playerStep who execution
          (.privateCommand (.register field ⟨ty, chosen.1⟩))).bind fun registered =>
          (image.application.playerStep who registered
            (.submit (.binding code.node (who, field)))).bind fun submitted =>
              image.application.environmentPolicyStep submitted (.include id)) ∧
    (∀ chosen ∈ choices.support,
      ∀ registered ∈ (image.application.playerStep who execution
        (.privateCommand (.register field ⟨ty, chosen.1⟩))).support,
      ∀ submitted ∈ (image.application.playerStep who registered
        (.submit (.binding code.node (who, field)))).support,
      ∀ included ∈ (image.application.environmentPolicyStep submitted (.include id)).support,
      ∃ next : CoupledAt (compileCore (.commit name who guard tail) fresh state).graph
          (state.addCommitEvent name who guard fresh.1).1,
        next.current.source = current.current.source.cons chosen.1 ∧
          included.native.application.Refines next.current.graph.1 ∧
          ApplicationImage.AcceptedSnapshot field (who, field) (some ⟨ty, chosen.1⟩)
            included.native.application) ∧
    (image.activeAddress? execution.native.application.memory = some code.node →
      image.orderedApplication.runPolicies players environment
          [.player who, .player who, .environment] execution =
        image.application.runPolicies players environment
          [.player who, .player who, .environment] execution) := by
  let image := root.image deadlineOf
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let field := site.compiledField fresh state
  let code := site.bindingCode fresh state field
  have hmem : ApplicationInstruction.bind code ∈ root.instructions deadlineOf := by
    obtain ⟨before, hbefore⟩ := continuation.instructions_suffix deadlineOf
    rw [hbefore]
    exact List.mem_append_right before List.mem_cons_self
  have hcode : image.lookup code.node = some (.bind code) :=
    root.image_lookup_of_mem deadlineOf (.bind code) hmem
  have hreadyData := SourceDecisionSite.binding_ready_at_source_prefix guard tail fresh state
    current execution.native.application.memory.done hrefines.memory.completed
  obtain ⟨reads, hreadout, _, hview⟩ :=
    continuation.runPolicies_ownerReadout?_of_ready_source_view deadlineOf who players howner
      priorEnvironment previous execution hreached site current.current.graph.1 hrefines
      hreadyData.1 hinitial current.current.source
      (BuildState.Agrees.view current.current.agrees who)
  have hconsistent : image.RegistrationConsistent execution :=
    image.runPolicies_registrationCache
      (ApplicationImage.Memory.initial (compileCore rootProg rootFresh rootState).graph)
      players priorEnvironment previous execution hreached
  have hdoneView : (State.observe image.application execution.native who).application.done
      state.nodes.length = false := hreadyData.2.1
  have hpolicy : ∀ history,
      players who history (State.observe image.application execution.native who) =
        site.bindingPolicy fresh state image (profile who site) history
          (State.observe image.application execution.native who) := by
    intro history
    rw [howner]
    unfold ApplicationPlan.liftProfile
    rw [continuation.liftProfileIn_eq_of_refines image deadlineOf current
      execution.native hrefines who history]
    simp only [ApplicationPlan.liftProfileIn, hdoneView, Bool.false_eq_true, ↓reduceIte, site]
  have hlookup := image.application.runPolicies_initial_lookup_nextSerial_eq_none
    players priorEnvironment previous
    (ApplicationImage.State.initial
      (ApplicationImage.Memory.initial (compileCore rootProg rootFresh rootState).graph))
    execution hreached who
  exact SourceDecisionSite.binding_phase_source_law guard tail fresh state current image
    (profile who site) players environment execution hrefines hconsistent hcode reads hpolicy
    henvironment hlookup hcache hsubmitted hreadout hview

end Vegas.ApplicationPlan.ProfileContinuation

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.publicChoice_phase_of_unchanged_owner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.publicChoice_phase_of_unchanged_owner

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.binding_phase_of_unchanged_owner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.binding_phase_of_unchanged_owner
