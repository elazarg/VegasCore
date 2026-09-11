/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingReadiness
import Vegas.Compile.WindowedBindingSubmission
import Vegas.Compile.WindowedBindingCheckpoint
import Vegas.Compile.WindowedNormalSuffix

/-! # Exact complete-block law for unchanged binding owners

The source draw indexes a concrete native branch: private registration,
opaque-handle submission, and the rest of the fixed block service. This
factorization retains probabilities and arbitrary intervening raw commands.
Each supported fixed-draw branch reaches the source successor containing that
draw. Fresh preparation and the acceptance-time snapshot identify the value;
remaining raw traffic preserves that snapshot.
-/

noncomputable section

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
variable {windowOf : Nat → Nat} {roster : List P} {focal owner : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending}
variable {accounted : CommitmentAccounting (insert name pending) tail}
variable {fresh : FreshBindings (.commit name owner guard tail)} {state : BuildState P L Γ}

/-- Factor a complete binding block through its unchanged owner's source
kernel. Earlier polls remain inside the chosen-value branch; the equality
does not condition on acceptance, discard failed runs, or select witnesses. -/
theorem binding_block_source_factorization
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name owner guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name owner guard tail))
    (current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
        profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
      replacement
    let environment := runtime.blockEnvironment roster
    let before := beforeRoster.flatMap fun actor => [.player actor, .player actor]
    let remaining :=
      (afterRoster.flatMap fun actor => [.player actor, .player actor]) ++
        [.environment, .environment] ++
          roster.flatMap fun actor => [.player actor, .environment]
    let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
      .here guard tail
    let kernel := profile owner site ((current.current.source.toView owner).eraseEnv)
    runtime.application.runPolicies players environment
        (WindowedApplication.blockInvocations roster) execution =
      kernel.bind fun chosen =>
        (runtime.application.runPolicies players environment before execution).bind fun middle =>
          (runtime.application.playerStep owner middle
            (.privateCommand (.register (site.compiledField fresh state) ⟨ty, chosen.1⟩))).bind
              fun registered =>
                (runtime.application.playerStep owner registered
                  (.submit (.binding
                    (site.bindingCode fresh state (site.compiledField fresh state)).node
                    (owner, site.compiledField fresh state)))).bind fun submitted =>
                      runtime.application.runPolicies players environment remaining submitted := by
  dsimp only
  let runtime := root.windowed deadlineOf binding choice windowOf
  let environment := runtime.blockEnvironment roster
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let remaining :=
    (afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]) ++
      [Invocation.environment, .environment] ++
        roster.flatMap fun actor => [Invocation.player actor, .environment]
  have hnotOwner : owner ∉ beforeRoster := by
    intro hmem
    have hparts := List.nodup_append.mp (hsplit ▸ hroster)
    exact hparts.2.2 owner hmem owner (by simp) rfl
  have hbeforeEnvironment : Invocation.environment ∉ before := by simp [before]
  have hbeforeOwner : Invocation.player owner ∉ before := by simp [before, hnotOwner]
  have hpolls := checkpoint.binding_polls_source_law_after_others hinitial hroster
    howner hother environment before hbeforeEnvironment hbeforeOwner
  have hschedule : WindowedApplication.blockInvocations roster =
      (before ++ [Invocation.player owner, .player owner]) ++ remaining := by
    simp only [WindowedApplication.blockInvocations, before, remaining, hsplit,
      List.flatMap_append, List.flatMap_cons, List.append_assoc]
  rw [hschedule, MessageApplication.runPolicies_append, hpolls]
  simp only [FinDist.bind_bind]
  rw [FinDist.bind_comm]

/-- A supported fixed binding draw reaches its corresponding sequential source
successor. The native owner uses a fresh write-once preparation slot; the value
is frozen at acceptance and retained through the rest of the actual block. -/
theorem binding_fixed_branch_source_coupling
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name owner guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name owner guard tail))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (deadline : Nat)
    (hselect : binding ((.here guard tail : SourceDecisionSite owner
      (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
        ((.here guard tail : SourceDecisionSite owner
          (.commit name owner guard tail) Γ name ty guard).compiledField fresh state)) =
      some ⟨deadline, fallback.compiled fresh state⟩)
    (current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
        profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (chosen : { value // evalGuard guard value
      ((current.current.source.toView owner).eraseEnv) = true })
    (hchosen : chosen ∈ (profile owner (.here guard tail)
      ((current.current.source.toView owner).eraseEnv)).support)
    (hbranch : final ∈
      (let runtime := root.windowed deadlineOf binding choice windowOf
       let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
         replacement
       let environment := runtime.blockEnvironment roster
       let before := beforeRoster.flatMap fun actor => [.player actor, .player actor]
       let remaining :=
         (afterRoster.flatMap fun actor => [.player actor, .player actor]) ++
           [.environment, .environment] ++
             roster.flatMap fun actor => [.player actor, .environment]
       let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
         .here guard tail
       (runtime.application.runPolicies players environment before execution).bind fun middle =>
         (runtime.application.playerStep owner middle
           (.privateCommand (.register (site.compiledField fresh state) ⟨ty, chosen.1⟩))).bind
             fun registered =>
               (runtime.application.playerStep owner registered
                 (.submit (.binding
                   (site.bindingCode fresh state (site.compiledField fresh state)).node
                   (owner, site.compiledField fresh state)))).bind fun submitted =>
                     runtime.application.runPolicies players environment remaining
                       submitted).support) :
    ∃ sourceNext : CoupledAt
        (compileCore (.commit name owner guard tail) fresh state).graph
        (state.addCommitEvent name owner guard fresh.1).1,
      sourceNext.current.source = current.current.source.cons chosen.1 ∧
        SmallStep ⟨Γ, current.current.source, .commit name owner guard tail⟩
          ⟨(name, .sealed owner ty) :: Γ, sourceNext.current.source, tail⟩ ∧
        WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster focal
          replacement (blockIndex + 1) nextPlan profile.afterCommit sourceNext final ∧
        (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
          final.native.application.base.memory ≠ some state.nodes.length ∧
        chosen.1 = BindingCode.resolvedValue ((.here guard tail : SourceDecisionSite owner
          (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
            ((.here guard tail : SourceDecisionSite owner
              (.commit name owner guard tail) Γ name ty guard).compiledField fresh state))
          (L.eval fallback.expr current.current.source.erasePubEnv)
            final.native.application.base := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let environment := runtime.blockEnvironment roster
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let after := afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let suffix := Invocation.environment ::
    roster.flatMap fun actor => [Invocation.player actor, .environment]
  have hfactor := checkpoint.binding_block_source_factorization unrestricted nextPlan profile
    current execution hinitial hroster howner hother beforeRoster afterRoster hsplit
  have hfull : final ∈ (runtime.application.runPolicies players environment
      (WindowedApplication.blockInvocations roster) execution).support := by
    rw [hfactor]
    rw [FinDist.support_bind]
    exact Set.mem_iUnion.mpr ⟨chosen, Set.mem_iUnion.mpr ⟨hchosen, hbranch⟩⟩
  dsimp only at hbranch
  simp only [List.append_assoc] at hbranch
  change final ∈ ((runtime.application.runPolicies players environment before execution).bind
    fun middle => (runtime.application.playerStep owner middle
      (.privateCommand (.register (site.compiledField fresh state) ⟨ty, chosen.1⟩))).bind
        fun registered => (runtime.application.playerStep owner registered
          (.submit (.binding code.node (owner, site.compiledField fresh state)))).bind
            fun submitted => runtime.application.runPolicies players environment
              (after ++ .environment :: suffix) submitted).support at hbranch
  simp only [FinDist.support_bind, Set.mem_iUnion] at hbranch
  obtain ⟨middle, hmiddle, registered, hregistered, submitted, hsubmitted, hremaining⟩ := hbranch
  rw [MessageApplication.runPolicies_append] at hremaining
  simp only [FinDist.support_bind, Set.mem_iUnion, MessageApplication.runPolicies] at hremaining
  obtain ⟨polled, hafter, included, hincluded, hfinal⟩ := hremaining
  have hbeforeEnvironment : Invocation.environment ∉ before := by simp [before]
  have hbeforeOwner : Invocation.player owner ∉ before := by
    have hnot : owner ∉ beforeRoster := by
      intro hmem
      exact (List.nodup_append.mp (hsplit ▸ hroster)).2.2 owner hmem owner (by simp) rfl
    simp [before, hnot]
  have hafterEnvironment : Invocation.environment ∉ after := by simp [after]
  have hafterOwner : Invocation.player owner ∉ after := by
    have hnot := (List.nodup_cons.mp (List.nodup_append.mp (hsplit ▸ hroster)).2.1).1
    simp [after, hnot]
  have hprepared := runtime.runPolicies_register_submit_prepared owner
    (site.compiledField fresh state) ⟨ty, chosen.1⟩
    (.binding code.node (owner, site.compiledField fresh state)) players environment before after
    hbeforeEnvironment hbeforeOwner hafterEnvironment hafterOwner execution polled
    (checkpoint.binding_preparation_empty hother) (by
      simp only [FinDist.support_bind, Set.mem_iUnion]
      exact ⟨middle, hmiddle, registered, hregistered, submitted, hsubmitted, hafter⟩)
  have hpolls := checkpoint.binding_polls_source_law_after_others hinitial hroster howner
    hother environment before hbeforeEnvironment hbeforeOwner
  have hbeforePair : submitted ∈ (runtime.application.runPolicies players environment
      (before ++ [.player owner, .player owner]) execution).support := by
    rw [hpolls]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨middle, hmiddle, chosen, hchosen, registered, hregistered, hsubmitted⟩
  have hpollSchedule : roster.flatMap (fun actor =>
      [Invocation.player actor, .player actor]) =
      (before ++ [.player owner, .player owner]) ++ after := by
    simp [hsplit, before, after, List.append_assoc]
  have hpolled : polled ∈ (runtime.application.runPolicies players environment
      (roster.flatMap fun actor => [.player actor, .player actor]) execution).support := by
    rw [hpollSchedule, MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨submitted, hbeforePair, hafter⟩
  obtain ⟨_, hinactive, haccepted⟩ := checkpoint.binding_ordinary_inclusion hinitial hroster
    howner hother polled included hpolled hincluded
  change included.native.application.base = polled.native.application.base.bind
    { code with timeout := binding code } (owner, site.compiledField fresh state) at haccepted
  have hhead : (ApplicationPlan.binding (newName := newName) (fresh := fresh)
      unrestricted nextPlan).instructions deadlineOf =
        .bind code :: nextPlan.instructions deadlineOf := rfl
  have hnormal : included ∈ (runtime.application.runPolicies players environment
      ((roster.flatMap fun actor => [.player actor, .player actor]) ++ [.environment])
      execution).support := by
    rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨polled, hpolled, by
      simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hincluded⟩
  have hframe := checkpoint.after_normal_frame _ _ hhead included final hinactive hnormal hfinal
  have hmemory : final.native.application.base.memory =
      included.native.application.base.memory := congrArg Prod.fst hframe
  have hfrozen : final.native.application.base.frozen =
      included.native.application.base.frozen := congrArg (fun frame => frame.2.2) hframe
  have hvalue : code.resolvedValue (L.eval fallback.expr current.current.source.erasePubEnv)
      final.native.application.base = chosen.1 := by
    unfold BindingCode.resolvedValue
    rw [hmemory, hfrozen, haccepted]
    simp only [ApplicationImage.State.bind, ↓reduceIte, hprepared, Option.bind_some]
    simp [TypedValue.as?]
  obtain ⟨actual, sourceNext, hsource, hnext, hactual, hinactiveFinal, hstep⟩ :=
    checkpoint.binding_block unrestricted nextPlan profile fallback deadline hselect current
      execution final hroster owner howner hother hfull
  have heq : actual = chosen.1 := hactual.trans hvalue
  rw [heq] at hsource
  exact ⟨sourceNext, hsource, hstep, hnext, hinactiveFinal, hvalue.symm⟩

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_block_source_factorization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_block_source_factorization

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_fixed_branch_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_fixed_branch_source_coupling
