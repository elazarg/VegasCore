/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationBlockFallbacks
import Vegas.Compile.WindowedBindingCheckpoint
import Vegas.Compile.WindowedPublicChoiceCheckpoint
import Vegas.Compile.WindowedConditionalCheckpoint
import Vegas.Compile.WindowedSampleCheckpoint

/-! # Source evidence along actual windowed execution prefixes

Each edge retains an actual block execution and its source extension. Opaque
binding values are fixed by the acceptance snapshot or the source fallback;
arbitrary refinement witnesses cannot replace them. These are proof objects
over the emitted interpreter, not another runtime or a source evaluator.
No paired information-agreement premise is stored in a prefix.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A single structural source extension, retaining the actual resolved value
needed for policy extraction. The final native state is relevant to opaque
binding extraction; the prefix separately records native execution support. -/
inductive BlockSourceStep
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (final : ApplicationImage.State P L) :
    {Γ Δ : VCtx P L} → {pending nextPending : Finset VarId} →
    {prog : VegasCore P L Γ} → {nextProg : VegasCore P L Δ} →
    {accounted : CommitmentAccounting pending prog} →
    {nextAccounted : CommitmentAccounting nextPending nextProg} →
    {fresh : FreshBindings prog} → {nextFresh : FreshBindings nextProg} →
    {state : BuildState P L Γ} → {nextState : BuildState P L Δ} →
    ApplicationPlan accounted fresh state → SourceBehavioralProfile prog →
    CoupledAt (compileCore prog fresh state).graph state →
    ApplicationPlan nextAccounted nextFresh nextState → SourceBehavioralProfile nextProg →
    CoupledAt (compileCore nextProg nextFresh nextState).graph nextState → Prop where
  | sample {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {ty : L.Ty}
      {dist : L.DistExpr (erasePubVCtx Γ) ty}
      {tail : VegasCore P L ((name, .pub ty) :: Γ)}
      {accounted : CommitmentAccounting pending tail}
      {fresh : FreshBindings (.sample name dist tail)} {state : BuildState P L Γ}
      {next : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1}
      {profile : SourceBehavioralProfile (.sample name dist tail)}
      {current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state}
      {sourceNext : CoupledAt (compileCore tail fresh.2
        (state.addSampleEvent name dist fresh.1).1).graph
        (state.addSampleEvent name dist fresh.1).1}
      (value : L.Val ty)
      (draw : value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support)
      (source : sourceNext.current.source = current.current.source.cons value) :
      BlockSourceStep binding final (.sample next) profile current next
        profile.afterSample sourceNext
  | binding {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {owner : P}
      {ty : L.Ty} {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
      {tail : VegasCore P L ((name, .sealed owner ty) :: Γ)}
      {newName : name ∉ pending} {accounted : CommitmentAccounting (insert name pending) tail}
      {fresh : FreshBindings (.commit name owner guard tail)} {state : BuildState P L Γ}
      {unrestricted : UnrestrictedBinding guard}
      {next : ApplicationPlan accounted fresh.2 (state.addCommitEvent name owner guard fresh.1).1}
      {profile : SourceBehavioralProfile (.commit name owner guard tail)}
      {current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state}
      {sourceNext : CoupledAt (compileCore tail fresh.2
        (state.addCommitEvent name owner guard fresh.1).1).graph
        (state.addCommitEvent name owner guard fresh.1).1}
      (fallback : SourceDecisionSite.PublicFallback (.here guard tail)) (deadline : Nat)
      (selected : binding ((.here guard tail : SourceDecisionSite owner
        (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
          ((.here guard tail : SourceDecisionSite owner
            (.commit name owner guard tail) Γ name ty guard).compiledField fresh state)) =
        some ⟨deadline, fallback.compiled fresh state⟩)
      (value : L.Val ty)
      (source : sourceNext.current.source = current.current.source.cons value)
      (resolved : value = BindingCode.resolvedValue
        ((.here guard tail : SourceDecisionSite owner
          (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
            ((.here guard tail : SourceDecisionSite owner
              (.commit name owner guard tail) Γ name ty guard).compiledField fresh state))
        (L.eval fallback.expr current.current.source.erasePubEnv) final) :
      BlockSourceStep binding final (.binding (newName := newName) unrestricted next)
        profile current next profile.afterCommit sourceNext
  | publicChoice {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId}
      {owner : P} {ty : L.Ty}
      {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
      {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
      {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
      {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
      {fresh : FreshBindings (.commit name owner guard (.reveal publicName owner name .here tail))}
      {state : BuildState P L Γ}
      {publicGuard : (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable
        fresh state}
      {next : ApplicationPlan accounted fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1}
      {profile : SourceBehavioralProfile
        (.commit name owner guard (.reveal publicName owner name .here tail))}
      {current : CoupledAt (compileCore
        (.commit name owner guard (.reveal publicName owner name .here tail))
          fresh state).graph state}
      {sourceNext : CoupledAt (compileCore tail fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1}
      (value : L.Val ty)
      (source : sourceNext.current.source = (current.current.source.cons value).cons value)
      (legal : evalGuard guard value ((current.current.source.toView owner).eraseEnv) = true) :
      BlockSourceStep binding final
        (.publicChoice (newName := newName) (unresolved := unresolved) publicGuard next)
        profile current next profile.afterCommit.afterReveal sourceNext
  | conditional {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId}
      {owner : P} {ty : L.Ty}
      {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
      {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
      {spec : ConditionalOpening guard} {unresolved : spec.source ∈ pending}
      {newName : name ∉ pending}
      {accounted : CommitmentAccounting (pending.erase spec.source) tail}
      {fresh : FreshBindings (.commit name owner guard (.reveal publicName owner name .here tail))}
      {state : BuildState P L Γ}
      {publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
        |>.PubliclyValidatable fresh state}
      {next : ApplicationPlan accounted fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1}
      {profile : SourceBehavioralProfile
        (.commit name owner guard (.reveal publicName owner name .here tail))}
      {current : CoupledAt (compileCore
        (.commit name owner guard (.reveal publicName owner name .here tail))
          fresh state).graph state}
      {sourceNext : CoupledAt (compileCore tail fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1}
      (result : Option (L.Val spec.secretTy))
      (admissible : result = none ∨ result = some (current.current.source.get spec.binding))
      (source : sourceNext.current.source =
        (current.current.source.cons (spec.encoding.symm result)).cons (spec.encoding.symm result))
      (legal : evalGuard guard (spec.encoding.symm result)
        ((current.current.source.toView owner).eraseEnv) = true) :
      BlockSourceStep binding final
        (.conditional (unresolved := unresolved) (newName := newName) publicGuard next)
        profile current next profile.afterCommit.afterReveal sourceNext
  | conditionalCopy {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId}
      {owner : P} {ty : L.Ty}
      {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
      {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
      {spec : ConditionalOpening guard}
      {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
      {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
      {fresh : FreshBindings (.commit name owner guard (.reveal publicName owner name .here tail))}
      {state : BuildState P L Γ}
      {publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
        |>.PubliclyValidatable fresh state}
      {next : ApplicationPlan accounted fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1}
      {profile : SourceBehavioralProfile
        (.commit name owner guard (.reveal publicName owner name .here tail))}
      {current : CoupledAt (compileCore
        (.commit name owner guard (.reveal publicName owner name .here tail))
          fresh state).graph state}
      {sourceNext : CoupledAt (compileCore tail fresh.2.2
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1}
      (result : Option (L.Val spec.secretTy))
      (admissible : result = none ∨ result = some (current.current.source.get spec.binding))
      (source : sourceNext.current.source =
        (current.current.source.cons (spec.encoding.symm result)).cons (spec.encoding.symm result))
      (legal : evalGuard guard (spec.encoding.symm result)
        ((current.current.source.toView owner).eraseEnv) = true) :
      BlockSourceStep binding final
        (.conditionalCopy (newName := newName) (unresolved := unresolved) spec publicGuard next)
        profile current next profile.afterCommit.afterReveal sourceNext

namespace BlockSourceStep

/-- Every recorded source edge is an actual written-order source execution. -/
theorem source_steps
    {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
    {final : ApplicationImage.State P L}
    {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
    {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
    {accounted : CommitmentAccounting pending prog}
    {nextAccounted : CommitmentAccounting nextPending nextProg}
    {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
    {state : BuildState P L Γ} {nextState : BuildState P L Δ}
    {plan : ApplicationPlan accounted fresh state}
    {nextPlan : ApplicationPlan nextAccounted nextFresh nextState}
    {profile : SourceBehavioralProfile prog} {nextProfile : SourceBehavioralProfile nextProg}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {sourceNext : CoupledAt (compileCore nextProg nextFresh nextState).graph nextState}
    (transition :
      BlockSourceStep binding final plan profile current nextPlan nextProfile sourceNext) :
    SmallStep.Star ⟨Γ, current.current.source, prog⟩
      ⟨Δ, sourceNext.current.source, nextProg⟩ := by
  cases transition with
  | sample value draw source =>
      rw [source]
      exact .single (.sample _ _ value draw)
  | binding fallback deadline selected value source resolved =>
      rw [source]
      exact .single (.commit _ _ value (‹UnrestrictedBinding _› _ value))
  | publicChoice value source legal =>
      rw [source]
      exact (SmallStep.Star.single (.commit _ _ value legal)).trans (.single (.reveal .here _))
  | conditional result admissible source legal =>
      rw [source]
      exact (SmallStep.Star.single (.commit _ _ _ legal)).trans (.single (.reveal .here _))
  | conditionalCopy result admissible source legal =>
      rw [source]
      exact (SmallStep.Star.single (.commit _ _ _ legal)).trans (.single (.reveal .here _))

end BlockSourceStep

variable {rootContext : VCtx P L} {rootPending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}

/-- A canonical single-run source prefix. Every edge has an actual full-block
support witness, a structural source step, and a genuine successor checkpoint.
The initial source configuration is fixed, rather than recovered from a final
native refinement witness. -/
inductive WindowedSourcePrefix
    (root : ApplicationPlan rootAccounted rootFresh rootState)
    (rootProfile : SourceBehavioralProfile rootProg) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat)
    (service : (root.windowed deadlineOf binding choice windowOf).Service) (focal : P)
    (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState) :
    {Γ : VCtx P L} → {pending : Finset VarId} → {prog : VegasCore P L Γ} →
    {accounted : CommitmentAccounting pending prog} → {fresh : FreshBindings prog} →
    {state : BuildState P L Γ} → Nat → ApplicationPlan accounted fresh state →
    SourceBehavioralProfile prog → CoupledAt (compileCore prog fresh state).graph state →
    (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution → Prop where
  | initial
      (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf service
        focal replacement 0 root rootProfile initial
          (root.windowedInitialExecution deadlineOf binding choice windowOf)) :
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf service focal
        replacement initial 0 root rootProfile initial
          (root.windowedInitialExecution deadlineOf binding choice windowOf)
  | step {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
      {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
      {accounted : CommitmentAccounting pending prog}
      {nextAccounted : CommitmentAccounting nextPending nextProg}
      {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
      {state : BuildState P L Γ} {nextState : BuildState P L Δ}
      {blockIndex : Nat} {plan : ApplicationPlan accounted fresh state}
      {nextPlan : ApplicationPlan nextAccounted nextFresh nextState}
      {profile : SourceBehavioralProfile prog} {nextProfile : SourceBehavioralProfile nextProg}
      {current : CoupledAt (compileCore prog fresh state).graph state}
      {sourceNext : CoupledAt (compileCore nextProg nextFresh nextState).graph nextState}
      {execution final :
        (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
      (previous : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf service
        focal replacement initial blockIndex plan profile current execution)
      (block : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (service.players (root.liftProfile deadlineOf rootProfile) focal replacement)
        service.environment service.invocations execution).support)
      (source : BlockSourceStep binding final.native.application.base
        plan profile current nextPlan nextProfile sourceNext)
      (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf service
        focal replacement (blockIndex + 1) nextPlan nextProfile sourceNext final) :
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf service focal
        replacement initial (blockIndex + 1) nextPlan nextProfile sourceNext final

namespace WindowedSourcePrefix

/-- The endpoint checkpoint is supplied by the checked block construction,
not by a separate admission condition on the replacement policy. -/
theorem checkpoint
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
    {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
    {windowOf : Nat → Nat}
    {service : (root.windowed deadlineOf binding choice windowOf).Service} {focal : P}
    {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
    {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} {blockIndex : Nat} {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile prog}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf service focal
      replacement initial blockIndex plan profile current execution) :
    WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf service focal
      replacement blockIndex plan profile current execution := by
  cases trace <;> assumption

/-- A canonical native prefix retains a complete sequential source witness
from its fixed initial source environment. This is support-level execution
correspondence; it does not assert equality of probability laws. -/
theorem source_steps
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
    {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
    {windowOf : Nat → Nat}
    {service : (root.windowed deadlineOf binding choice windowOf).Service} {focal : P}
    {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
    {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} {blockIndex : Nat} {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile prog}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf service focal
      replacement initial blockIndex plan profile current execution) :
    SmallStep.Star ⟨rootContext, initial.current.source, rootProg⟩
      ⟨Γ, current.current.source, prog⟩ := by
  induction trace with
  | initial => exact .refl _
  | step previous block source checkpoint ih => exact ih.trans source.source_steps

end WindowedSourcePrefix

end Vegas.ApplicationPlan
