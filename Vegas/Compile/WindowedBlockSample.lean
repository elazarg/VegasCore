/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockIsolation
import Vegas.Compile.WindowedActivationFreshness
import Vegas.Compile.ApplicationSampleExecution

/-! # Exact chance kernels at windowed block checkpoints -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Proof-side reconstruction of the actual windowed successor of one sample
draw. The environment chooses the kernel, never this value. -/
def sampleExecution (runtime : WindowedApplication P L)
    (execution : runtime.application.PolicyExecution) (code : SampleCode L)
    (value : L.Val code.dist.ty) : runtime.application.PolicyExecution :=
  { execution with
    native := { execution.native with
      application := (runtime.advanceTo execution.native.application
        (execution.native.application.base.sample code value)) }
    environmentHistory := execution.environmentHistory ++
      [⟨MessageApplication.State.environmentView runtime.application execution.native,
        .application (.sample code.node)⟩]
    nativeTrace := execution.nativeTrace ++ [.environment (.sample code.node)] }

/-- Sampling the active instruction finishes it and starts any successor
window at the current clock, even if the old window had already aged. -/
theorem sampleExecution_freshActivation (runtime : WindowedApplication P L)
    (execution : runtime.application.PolicyExecution) (code : SampleCode L)
    (value : L.Val code.dist.ty)
    (hactive : execution.native.application.active.map Activation.key = some code.node) :
    (runtime.sampleExecution execution code value).native.application.FreshActivation := by
  let next := execution.native.application.base.sample code value
  have hdone : next.memory.done code.node = true := by
    simp [next, ApplicationImage.State.sample]
  have hchanged : execution.native.application.active.map Activation.key ≠
      runtime.image.activeAddress? next.memory := by
    rw [hactive]
    intro heq
    have hnotDone := runtime.image.activeAddress?_not_done next.memory code.node heq.symm
    rw [hdone] at hnotDone
    contradiction
  change (runtime.advanceTo execution.native.application next).FreshActivation
  rw [advanceTo, Activation.refresh_changed _ _ _ hchanged]
  intro activation hactivation
  simp only [Option.mem_map] at hactivation
  obtain ⟨key, _, rfl⟩ := hactivation
  rfl

private def baseExecution (runtime : WindowedApplication P L)
    (execution : runtime.application.PolicyExecution) :
    runtime.image.application.PolicyExecution :=
  show runtime.image.application.PolicyExecution from runtime.eraseExecution execution

/-- At an active sample address, the actual windowed environment step has the
source draw jointly with its concrete activation-tracked successor. -/
theorem environmentPolicyStep_sample_source_coupling
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (tail : VegasCore P L ((name, .pub ty) :: Γ))
    (fresh : FreshBindings (.sample name dist tail)) (state : BuildState P L Γ)
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution : runtime.application.PolicyExecution)
    (hcode : runtime.image.lookup state.nodes.length =
      some (.sample (ApplicationPlan.headSampleCode fresh state)))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some state.nodes.length)
    (hrefines : execution.native.application.base.Refines current.current.graph.1) :
    runtime.application.environmentPolicyStep execution
        (.application (.sample state.nodes.length)) =
      (L.evalDist dist current.current.source.eraseSampleEnv).map
        (runtime.sampleExecution execution (ApplicationPlan.headSampleCode fresh state)) ∧
    ∀ value, value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support →
      ∃ next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
          (state.addSampleEvent name dist fresh.1).1,
        next.current.source = current.current.source.cons value ∧
        ApplicationImage.State.Refines
          (runtime.sampleExecution execution
            (ApplicationPlan.headSampleCode fresh state) value).native.application.base
          next.current.graph.1 := by
  have hphase := ApplicationPlan.sample_phase_source_coupling dist tail fresh state runtime.image
    hcode current (runtime.baseExecution execution) hrefines
  constructor
  · simp only [MessageApplication.environmentPolicyStep,
      EnvironmentPolicyCommand.toAction, MessageApplication.advance,
      MessageApplication.step, FinDist.bind_map, FinDist.bind_bind]
    change (runtime.environmentStep execution.native.application
      (.sample state.nodes.length)).bind _ = _
    rw [environmentStep, runtime.image.ordered_sample_eq _ _ hactive]
    rw [FinDist.bind_map]
    simp only [FinDist.pure_bind]
    rw [← FinDist.map_eq_bind]
    have hkernel := congrArg
      (FinDist.map (fun out => out.native.application)) hphase.1
    simp only [MessageApplication.environmentPolicyStep,
      EnvironmentPolicyCommand.toAction, MessageApplication.advance,
      MessageApplication.step, ApplicationImage.application,
      FinDist.bind_bind, FinDist.map_bind, FinDist.map_pure,
      FinDist.pure_bind, FinDist.bind_pure, FinDist.bind_map,
      FinDist.map_comp, Function.comp_def, baseExecution, eraseExecution,
      ApplicationImage.sampleExecution] at hkernel
    change runtime.image.sample execution.native.application.base state.nodes.length =
      (L.evalDist dist current.current.source.eraseSampleEnv).map
        (fun value => execution.native.application.base.sample
          (ApplicationPlan.headSampleCode fresh state) value) at hkernel
    rw [hkernel, FinDist.map_comp]
    rfl
  · intro value hvalue
    obtain ⟨next, hsource, hrefinesNext⟩ := hphase.2 value hvalue
    exact ⟨next, hsource, hrefinesNext⟩

/-- Raw player polling preserves a fixed source-refinement checkpoint. -/
theorem runPolicies_players_refines (runtime : WindowedApplication P L)
    {G : Graph P L} {cfg : Config G}
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) (henvironment : Invocation.environment ∉ schedule)
    (execution next : runtime.application.PolicyExecution)
    (hrefines : execution.native.application.base.Refines cfg)
    (hnext : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    next.native.application.base.Refines cfg := by
  induction schedule generalizing execution with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hrefines
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      cases invocation with
      | environment => exact False.elim (henvironment (List.mem_cons_self ..))
      | player who =>
          simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have hmiddleRefines : middle.native.application.base.Refines cfg := by
            cases command with
            | privateCommand command =>
                cases command with
                | register slot value =>
                    simp only [MessageApplication.playerStep, PlayerCommand.toAction,
                      MessageApplication.advance, MessageApplication.step, application,
                      FinDist.pure_bind, FinDist.mem_support_pure] at hstep
                    subst middle
                    exact hrefines.register who slot value
            | submit payload | replay id | wait =>
                simp only [MessageApplication.playerStep, PlayerCommand.toAction,
                  MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
                  FinDist.mem_support_pure] at hstep
                subst middle
                exact hrefines
          exact ih (fun hmem => henvironment (List.mem_cons_of_mem _ hmem))
            middle hmiddleRefines hnext

/-- Arbitrary raw player polls before a block's normal environment slot remain
jointly independent of the source draw. The right side retains every sampled
polling state and attaches the exact activation-tracked successor to each draw. -/
theorem runPolicies_block_sample_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (tail : VegasCore P L ((name, .pub ty) :: Γ))
    (fresh : FreshBindings (.sample name dist tail)) (state : BuildState P L Γ)
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (players : P → runtime.application.PlayerPolicy)
    (before : List (@Invocation P)) (henvironment : Invocation.environment ∉ before)
    (execution : runtime.application.PolicyExecution)
    (hcode : runtime.image.lookup state.nodes.length =
      some (.sample (ApplicationPlan.headSampleCode fresh state)))
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? =
        some (.sample (ApplicationPlan.headSampleCode fresh state)))
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 0)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some state.nodes.length)
    (hrefines : execution.native.application.base.Refines current.current.graph.1) :
    (runtime.application.runPolicies players (runtime.blockEnvironment roster)
        (before ++ [.environment]) execution =
      (runtime.application.runPolicies players (runtime.blockEnvironment roster)
        before execution).bind fun middle =>
          (L.evalDist dist current.current.source.eraseSampleEnv).map
            (runtime.sampleExecution middle (ApplicationPlan.headSampleCode fresh state))) ∧
    ∀ middle ∈ (runtime.application.runPolicies players
        (runtime.blockEnvironment roster) before execution).support,
      ∀ value, value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support →
        ∃ next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
            (state.addSampleEvent name dist fresh.1).1,
          next.current.source = current.current.source.cons value ∧
          ApplicationImage.State.Refines
            (runtime.sampleExecution middle
              (ApplicationPlan.headSampleCode fresh state) value).native.application.base
            next.current.graph.1 := by
  have hprefixPublic := fun middle hmiddle =>
    runtime.runPolicies_players_publicState players (runtime.blockEnvironment roster)
      before henvironment execution middle hmiddle
  have hprefixRefines := fun middle hmiddle =>
    runtime.runPolicies_players_refines players (runtime.blockEnvironment roster)
      before henvironment execution middle hrefines hmiddle
  have hprefixEnvironmentLength : ∀ middle ∈
      (runtime.application.runPolicies players (runtime.blockEnvironment roster)
        before execution).support,
      middle.environmentHistory.length = execution.environmentHistory.length := by
    intro middle hmiddle
    have hlength := runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) before execution middle hmiddle
    have hcount : before.countP Invocation.isEnvironment = 0 := by
      apply List.countP_eq_zero.mpr
      intro invocation hmem
      cases invocation with
      | player who => simp [Invocation.isEnvironment]
      | environment => exact False.elim (henvironment hmem)
    simpa only [hcount, Nat.add_zero] using hlength
  constructor
  · rw [MessageApplication.runPolicies_append]
    apply FinDist.bind_congr
    intro middle hmiddle
    have hpublic := hprefixPublic middle hmiddle
    have hmemory : middle.native.application.base.memory =
        execution.native.application.base.memory := congrArg Prod.fst hpublic
    have hactivation := congrArg Prod.snd hpublic
    have hlength := hprefixEnvironmentLength middle hmiddle
    have hpolicy := runtime.blockEnvironment_normal roster middle.environmentHistory
      (MessageApplication.State.environmentView runtime.application middle.native)
      (.sample (ApplicationPlan.headSampleCode fresh state))
      (by simpa only [hlength] using hindex)
      (by
        change runtime.image.activeAddress? middle.native.application.base.memory =
          some state.nodes.length
        rw [hmemory, hactive])
      (by simpa only [hlength] using hslot)
    simp only [MessageApplication.runPolicies, MessageApplication.invoke, hpolicy,
      ApplicationImage.serviceCommand, liftEnvironmentCommand, FinDist.pure_bind,
      FinDist.bind_pure]
    exact (runtime.environmentPolicyStep_sample_source_coupling dist tail fresh state current
      middle hcode (by rw [hmemory]; exact hactive)
      (hprefixRefines middle hmiddle)).1
  · intro middle hmiddle value hvalue
    have hpublic := hprefixPublic middle hmiddle
    have hmemory : middle.native.application.base.memory =
        execution.native.application.base.memory := congrArg Prod.fst hpublic
    exact (runtime.environmentPolicyStep_sample_source_coupling dist tail fresh state current
      middle hcode (by rw [hmemory]; exact hactive)
      (hprefixRefines middle hmiddle)).2 value hvalue

/-- Extending a normal sample slot by an address-aligned inactive suffix keeps
the source draw joint with the complete runtime execution. Raw suffix players
may still change histories, pools, and private preparation; only public memory
and activation stutter after the sampled successor. -/
theorem runPolicies_block_sample_suffix_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (tail : VegasCore P L ((name, .pub ty) :: Γ))
    (fresh : FreshBindings (.sample name dist tail)) (state : BuildState P L Γ)
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (players : P → runtime.application.PlayerPolicy)
    (before suffix : List (@Invocation P))
    (henvironment : Invocation.environment ∉ before)
    (execution : runtime.application.PolicyExecution)
    (hcode : runtime.image.lookup state.nodes.length =
      some (.sample (ApplicationPlan.headSampleCode fresh state)))
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? =
        some (.sample (ApplicationPlan.headSampleCode fresh state)))
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 0)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some state.nodes.length)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hsuffixIndex : ∀ middle ∈ (runtime.application.runPolicies players
        (runtime.blockEnvironment roster) before execution).support,
      ∀ value, value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support →
      ∀ index,
        (runtime.sampleExecution middle
          (ApplicationPlan.headSampleCode fresh state) value).environmentHistory.length ≤ index →
        index < (runtime.sampleExecution middle
          (ApplicationPlan.headSampleCode fresh state) value).environmentHistory.length +
            suffix.countP Invocation.isEnvironment →
        runtime.image.instructions[index / (roster.length + 2)]? =
          some (.sample (ApplicationPlan.headSampleCode fresh state))) :
    (runtime.application.runPolicies players (runtime.blockEnvironment roster)
        ((before ++ [.environment]) ++ suffix) execution =
      (runtime.application.runPolicies players (runtime.blockEnvironment roster)
        before execution).bind fun middle =>
          (L.evalDist dist current.current.source.eraseSampleEnv).bind fun value =>
            runtime.application.runPolicies players (runtime.blockEnvironment roster) suffix
              (runtime.sampleExecution middle
                (ApplicationPlan.headSampleCode fresh state) value)) ∧
    ∀ middle ∈ (runtime.application.runPolicies players
        (runtime.blockEnvironment roster) before execution).support,
      ∀ value, value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support →
        ∃ next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
            (state.addSampleEvent name dist fresh.1).1,
          next.current.source = current.current.source.cons value ∧
          ApplicationImage.State.Refines
            (runtime.sampleExecution middle
              (ApplicationPlan.headSampleCode fresh state) value).native.application.base
            next.current.graph.1 ∧
          ∀ final, final ∈ (runtime.application.runPolicies players
              (runtime.blockEnvironment roster) suffix
              (runtime.sampleExecution middle
                (ApplicationPlan.headSampleCode fresh state) value)).support →
            (final.native.application.base.memory, final.native.application.active) =
              ((runtime.sampleExecution middle
                (ApplicationPlan.headSampleCode fresh state) value).native.application.base.memory,
               (runtime.sampleExecution middle
                (ApplicationPlan.headSampleCode fresh state) value).native.application.active) := by
  have hsample := runtime.runPolicies_block_sample_source_coupling roster dist tail fresh state
    current players before henvironment execution hcode hindex hslot hactive hrefines
  constructor
  · rw [MessageApplication.runPolicies_append, hsample.1, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro middle _
    rw [FinDist.bind_map]
    rfl
  · intro middle hmiddle value hvalue
    obtain ⟨next, hsource, hrefinesNext⟩ := hsample.2 middle hmiddle value hvalue
    refine ⟨next, hsource, hrefinesNext, ?_⟩
    intro final hfinal
    let sampled := runtime.sampleExecution middle
      (ApplicationPlan.headSampleCode fresh state) value
    have hinactive : runtime.image.activeAddress? sampled.native.application.base.memory ≠
        some (ApplicationPlan.headSampleCode fresh state).node := by
      intro hstillActive
      have hnotDone := runtime.image.activeAddress?_not_done
        sampled.native.application.base.memory
        (ApplicationPlan.headSampleCode fresh state).node hstillActive
      have hdone : sampled.native.application.base.memory.done
          (ApplicationPlan.headSampleCode fresh state).node = true := by
        simp [sampled, sampleExecution, advanceTo, ApplicationImage.State.sample]
      rw [hdone] at hnotDone
      contradiction
    exact runtime.runPolicies_block_inactive roster players suffix sampled final
      (.sample (ApplicationPlan.headSampleCode fresh state))
      (hsuffixIndex middle hmiddle value hvalue) hinactive hfinal

/-- One entire fixed service block preserves a source chance draw jointly with
the native execution and the exact successor source configuration. The slot
range and inactive suffix are derived from the emitted block, not supplied as
additional fairness or completion premises. Players remain arbitrary. -/
theorem runPolicies_full_block_sample_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (tail : VegasCore P L ((name, .pub ty) :: Γ))
    (fresh : FreshBindings (.sample name dist tail)) (state : BuildState P L Γ)
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (players : P → runtime.application.PlayerPolicy)
    (execution : runtime.application.PolicyExecution)
    (hcode : runtime.image.lookup state.nodes.length =
      some (.sample (ApplicationPlan.headSampleCode fresh state)))
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some (.sample (ApplicationPlan.headSampleCode fresh state)))
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 0)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some state.nodes.length)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hconsistent : runtime.Consistent execution.native.application) :
    let before := roster.flatMap (fun actor => [Invocation.player actor, .player actor])
    let suffix := Invocation.environment ::
      roster.flatMap (fun actor => [Invocation.player actor, .environment])
    (runtime.application.runPolicies players (runtime.blockEnvironment roster)
        (blockInvocations roster) execution =
      (runtime.application.runPolicies players (runtime.blockEnvironment roster)
        before execution).bind fun middle =>
          (L.evalDist dist current.current.source.eraseSampleEnv).bind fun value =>
            runtime.application.runPolicies players (runtime.blockEnvironment roster) suffix
              (runtime.sampleExecution middle (ApplicationPlan.headSampleCode fresh state) value)) ∧
    ∀ middle ∈ (runtime.application.runPolicies players
        (runtime.blockEnvironment roster) before execution).support,
      ∀ value, value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support →
        ∃ next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
            (state.addSampleEvent name dist fresh.1).1,
          next.current.source = current.current.source.cons value ∧
          ∀ final, final ∈ (runtime.application.runPolicies players
              (runtime.blockEnvironment roster) suffix
              (runtime.sampleExecution middle
                (ApplicationPlan.headSampleCode fresh state) value)).support →
            final.native.application.base.Refines next.current.graph.1 ∧
              final.native.application.FreshActivation := by
  let before := roster.flatMap (fun actor => [Invocation.player actor, Invocation.player actor])
  let suffix := Invocation.environment ::
    roster.flatMap (fun actor => [Invocation.player actor, Invocation.environment])
  have hbefore : Invocation.environment ∉ before := by simp [before]
  have hbeforeCount : before.countP Invocation.isEnvironment = 0 := by
    apply List.countP_eq_zero.mpr
    intro call hmem
    cases call with
    | player actor => simp [Invocation.isEnvironment]
    | environment => exact False.elim (hbefore hmem)
  have hsuffixCount : suffix.countP Invocation.isEnvironment = roster.length + 1 := by
    have relayCount : ∀ entries : List P, (entries.flatMap fun actor =>
        [Invocation.player actor, Invocation.environment]).countP Invocation.isEnvironment =
        entries.length := by
      intro entries
      induction entries with
      | nil => rfl
      | cons actor rest ih => simp [List.flatMap_cons, Invocation.isEnvironment, ih]
    simp only [suffix, List.countP_cons, Invocation.isEnvironment, ↓reduceIte, relayCount]
  have hmiddleLength : ∀ middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) before execution).support,
      middle.environmentHistory.length = execution.environmentHistory.length := by
    intro middle hmiddle
    simpa only [hbeforeCount, Nat.add_zero] using
      runtime.application.runPolicies_environmentHistory_length players
        (runtime.blockEnvironment roster) before execution middle hmiddle
  have hrange : ∀ middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) before execution).support,
      ∀ value : L.Val ty, ∀ index,
        (runtime.sampleExecution middle (ApplicationPlan.headSampleCode fresh state)
          value).environmentHistory.length ≤ index →
        index < (runtime.sampleExecution middle (ApplicationPlan.headSampleCode fresh state)
          value).environmentHistory.length + suffix.countP Invocation.isEnvironment →
        runtime.image.instructions[index / (roster.length + 2)]? =
          some (.sample (ApplicationPlan.headSampleCode fresh state)) := by
    intro middle hmiddle value index hlo hhi
    have hlength : (runtime.sampleExecution middle (ApplicationPlan.headSampleCode fresh state)
        value).environmentHistory.length = execution.environmentHistory.length + 1 := by
      simp only [sampleExecution, List.length_append, List.length_singleton,
        hmiddleLength middle hmiddle]
    rw [hlength] at hlo hhi
    rw [hsuffixCount] at hhi
    have hquotient : index / (roster.length + 2) =
        execution.environmentHistory.length / (roster.length + 2) := by
      have hbase := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hslot)
      apply Nat.div_eq_of_lt_le
      · rw [hbase]
        omega
      · rw [Nat.add_mul, hbase]
        omega
    rw [hquotient]
    exact hindex
  have hphase := runtime.runPolicies_block_sample_suffix_source_coupling roster dist tail
    fresh state current players before suffix hbefore execution hcode hindex hslot hactive
    hrefines (fun middle hmiddle value _ => hrange middle hmiddle value)
  refine ⟨?_, ?_⟩
  · simpa only [blockInvocations, before, suffix, List.append_assoc,
      List.cons_append, List.nil_append]
      using hphase.1
  · intro middle hmiddle value hvalue
    obtain ⟨next, hsource, hnextRefines, _⟩ := hphase.2 middle hmiddle value hvalue
    refine ⟨next, hsource, ?_⟩
    intro final hfinal
    let sampled := runtime.sampleExecution middle (ApplicationPlan.headSampleCode fresh state)
      value
    have hinactive : runtime.image.activeAddress? sampled.native.application.base.memory ≠
        some (ApplicationPlan.headSampleCode fresh state).node := by
      intro hstillActive
      have hnotDone := runtime.image.activeAddress?_not_done sampled.native.application.base.memory
        (ApplicationPlan.headSampleCode fresh state).node hstillActive
      have hdone : sampled.native.application.base.memory.done
          (ApplicationPlan.headSampleCode fresh state).node = true := by
        simp [sampled, sampleExecution, advanceTo, ApplicationImage.State.sample]
      rw [hdone] at hnotDone
      contradiction
    refine ⟨runtime.runPolicies_block_inactive_refines next.current.graph.1 roster players suffix
      sampled final (.sample (ApplicationPlan.headSampleCode fresh state))
      (hrange middle hmiddle value) hinactive hnextRefines hfinal, ?_⟩
    have hpublic := runtime.runPolicies_players_publicState players
      (runtime.blockEnvironment roster) before hbefore execution middle hmiddle
    have hactivation : middle.native.application.active.map Activation.key =
        some (ApplicationPlan.headSampleCode fresh state).node := by
      calc
        _ = execution.native.application.active.map Activation.key :=
          congrArg (fun pair : ApplicationImage.Memory P L × Option (Activation Nat) =>
            pair.2.map Activation.key) hpublic
        _ = _ := hconsistent.1.trans hactive
    exact runtime.runPolicies_block_inactive_freshActivation roster players suffix sampled final
      (.sample (ApplicationPlan.headSampleCode fresh state)) (hrange middle hmiddle value)
      hinactive (runtime.sampleExecution_freshActivation middle _ value hactivation) hfinal

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_block_sample_suffix_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.WindowedApplication.runPolicies_block_sample_suffix_source_coupling

/-- info: 'Vegas.WindowedApplication.runPolicies_full_block_sample_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_full_block_sample_source_coupling
