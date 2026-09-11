/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryIsolation
import Vegas.Compile.WindowedBlockSample
import Interaction.MessageApplicationEnvironmentCommands

/-! # Chance blocks under delivery-enabled service -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
private theorem ordinaryPolls_environmentCount (roster : List P) :
    (roster.flatMap (fun actor => [Invocation.player actor,
      Invocation.player actor])).countP Invocation.isEnvironment = 0 := by
  induction roster with
  | nil => rfl
  | cons actor rest ih =>
      simp only [List.flatMap_cons, List.countP_append, List.countP_cons,
        List.countP_nil, Invocation.isEnvironment, Bool.false_eq_true, ↓reduceIte,
        Nat.zero_add]
      exact ih

omit [DecidableEq P] in
private theorem deliveryPolls_environmentCount (recipients : List P) :
    (recipients.map (fun _ =>
      (Invocation.environment : @Invocation P))).countP Invocation.isEnvironment =
        recipients.length := by
  induction recipients with
  | nil => rfl
  | cons recipient rest ih =>
      simp only [List.map_cons, List.countP_cons, Invocation.isEnvironment, ↓reduceIte,
        List.length_cons]
      exact congrArg Nat.succ ih

omit [DecidableEq P] in
private theorem reactionPolls_environmentCount (roster : List P) :
    (roster.map Invocation.player).countP Invocation.isEnvironment = 0 := by
  induction roster with
  | nil => rfl
  | cons actor rest ih =>
      simp only [List.map_cons, List.countP_cons, Invocation.isEnvironment,
        Bool.false_eq_true, ↓reduceIte]
      exact ih

/-- The delivery coordinates preceding a sample instruction are genuine
service invocations, but each executes `wait`: sampling has no pending envelope
to select or recipient-specific packet to deliver. The statement retains the
actual environment histories produced by those invocations. -/
theorem runPolicies_deliverySamplePrefix
    (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy)
    (roster all before rest : List P) (blockIndex : Nat)
    (code : SampleCode L)
    (hall : all = before ++ rest)
    (execution : runtime.application.PolicyExecution)
    (hlength : execution.environmentHistory.length =
      blockIndex * (all.length + roster.length + 2) + before.length)
    (hindex : runtime.image.instructions[blockIndex]? = some (.sample code))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some code.node) :
    runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster all)
        (rest.map fun _ => (Invocation.environment : @Invocation P)) execution =
      runtime.application.runEnvironmentCommands
        (rest.map fun _ => MessageInterface.EnvironmentPolicyCommand.wait) execution := by
  induction rest generalizing before execution with
  | nil => rfl
  | cons recipient rest ih =>
      have hwidth : 0 < all.length + roster.length + 2 := by omega
      have hbefore : before.length < all.length := by
        rw [hall, List.length_append, List.length_cons]
        omega
      have hdivision : execution.environmentHistory.length /
          (all.length + roster.length + 2) = blockIndex := by
        rw [hlength, Nat.mul_comm blockIndex, Nat.mul_add_div hwidth,
          Nat.div_eq_of_lt (by omega), Nat.add_zero]
      have hslot : execution.environmentHistory.length %
          (all.length + roster.length + 2) = before.length := by
        rw [hlength, Nat.mul_comm blockIndex, Nat.mul_add_mod,
          Nat.mod_eq_of_lt (by omega)]
      have hrecipient : all[before.length]? = some recipient := by
        rw [hall]
        simp
      have hpolicy := runtime.deliveryBlockEnvironment_delivery roster all
        execution.environmentHistory
        (State.environmentView runtime.application execution.native)
        (.sample code) before.length recipient (by rwa [hdivision]) hactive hslot hbefore
        hrecipient
      have hwait : runtime.deliveryBlockEnvironment roster all execution.environmentHistory
          (State.environmentView runtime.application execution.native) = FinDist.pure .wait := by
        rw [hpolicy]
        rfl
      simp only [List.map_cons, MessageApplication.runPolicies, MessageApplication.invoke,
        hwait, FinDist.pure_bind, MessageApplication.runEnvironmentCommands]
      apply FinDist.bind_congr
      intro next hnext
      simp only [MessageApplication.environmentStep_wait,
        FinDist.mem_support_pure] at hnext
      subst next
      apply ih (before ++ [recipient])
        (by simpa only [List.append_assoc, List.singleton_append] using hall)
      · simp [List.length_append, hlength, Nat.add_assoc]
      · exact hactive

/-- A complete delivery-enabled sample block retains the exact source chance
kernel. Delivery coordinates are idle for a sample, all player coordinates use
the supplied raw policies, and every supported inactive suffix still refines
the source successor selected by the actual draw. -/
theorem runPolicies_full_delivery_block_sample_source_coupling
    (runtime : WindowedApplication P L) (roster recipients : List P)
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
      (recipients.length + roster.length + 2)]? =
        some (.sample (ApplicationPlan.headSampleCode fresh state)))
    (hslot : execution.environmentHistory.length %
      (recipients.length + roster.length + 2) = 0)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some state.nodes.length)
    (hrefines : execution.native.application.base.Refines current.current.graph.1) :
    let before := roster.flatMap (fun actor => [.player actor, .player actor]) ++
      recipients.map (fun _ => Invocation.environment) ++ roster.map Invocation.player
    let suffix := Invocation.environment ::
      roster.flatMap (fun actor => [.player actor, .environment])
    (runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients)
        (deliveryBlockInvocations roster recipients) execution =
      (runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients) before execution).bind fun middle =>
          (L.evalDist dist current.current.source.eraseSampleEnv).bind fun value =>
            runtime.application.runPolicies players
              (runtime.deliveryBlockEnvironment roster recipients) suffix
              (runtime.sampleExecution middle
                (ApplicationPlan.headSampleCode fresh state) value)) ∧
    ∀ middle ∈ (runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients) before execution).support,
      ∀ value, value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support →
        ∃ next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
            (state.addSampleEvent name dist fresh.1).1,
          next.current.source = current.current.source.cons value ∧
          ∀ final, final ∈ (runtime.application.runPolicies players
              (runtime.deliveryBlockEnvironment roster recipients) suffix
              (runtime.sampleExecution middle
                (ApplicationPlan.headSampleCode fresh state) value)).support →
            final.native.application.base.Refines next.current.graph.1 := by
  let instruction : ApplicationInstruction P L :=
    .sample (ApplicationPlan.headSampleCode fresh state)
  let width := recipients.length + roster.length + 2
  let before := roster.flatMap (fun actor => [.player actor, .player actor]) ++
    recipients.map (fun _ => Invocation.environment) ++ roster.map Invocation.player
  let suffix := Invocation.environment ::
    roster.flatMap (fun actor => [.player actor, .environment])
  have hbeforeCount : before.countP Invocation.isEnvironment = recipients.length := by
    have hpolls := ordinaryPolls_environmentCount roster
    have hdeliveries := deliveryPolls_environmentCount recipients
    have hreactions := reactionPolls_environmentCount roster
    simp only [before, List.countP_append, hpolls, hdeliveries, hreactions,
      Nat.zero_add, Nat.add_zero]
  have hsuffixCount : suffix.countP Invocation.isEnvironment = roster.length + 1 := by
    have hrelay : ∀ entries : List P,
        (entries.flatMap fun actor => [Invocation.player actor,
          Invocation.environment]).countP Invocation.isEnvironment = entries.length := by
      intro entries
      induction entries with
      | nil => rfl
      | cons actor rest ih => simp [List.flatMap_cons, Invocation.isEnvironment, ih]
    simp [suffix, Invocation.isEnvironment, hrelay]
  have hprefixInvariant : ∀ middle,
      middle ∈ (runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients) before execution).support →
      middle.native.application.base.Refines current.current.graph.1 ∧
        (middle.native.application.base.memory, middle.native.application.active) =
          (execution.native.application.base.memory, execution.native.application.active) := by
    intro middle hmiddle
    apply runtime.application.runPolicies_idleEnvironment_invariant players
      (runtime.deliveryBlockEnvironment roster recipients) before execution middle
      (fun application => application.base.Refines current.current.graph.1 ∧
        (application.base.memory, application.active) =
          (execution.native.application.base.memory, execution.native.application.active))
    · intro application actor command hinvariant
      cases command with
      | register slot value =>
          exact ⟨hinvariant.1.register actor slot value, hinvariant.2⟩
    · intro point hpoint hlo hhi
      have hpointLength : point.environmentHistory.length <
          execution.environmentHistory.length + recipients.length := by
        simpa only [hbeforeCount] using hhi
      have hwidth : 0 < width := by simp [width]
      have hbase := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hslot)
      have hbase' : width * (execution.environmentHistory.length / width) =
          execution.environmentHistory.length := by
        simpa [width, Nat.mul_comm] using hbase
      have hquotient : point.environmentHistory.length / width =
          execution.environmentHistory.length / width := by
        apply Nat.div_eq_of_lt_le
        · rw [hbase]
          omega
        · rw [Nat.add_mul, hbase]
          simp only [width]
          omega
      have hpointIndex : runtime.image.instructions[point.environmentHistory.length / width]? =
          some instruction := by
        rw [hquotient]
        exact hindex
      have hmodDecomp := Nat.mod_add_div point.environmentHistory.length width
      have hslotRange : point.environmentHistory.length % width < recipients.length := by
        rw [hquotient, hbase'] at hmodDecomp
        omega
      let recipient := recipients[point.environmentHistory.length % width]
      have hrecipient : recipients[point.environmentHistory.length % width]? = some recipient := by
        exact List.getElem?_eq_getElem hslotRange
      have hactivePoint : runtime.image.activeAddress?
          (State.environmentView runtime.application point.native).application.1 =
            some instruction.address := by
        change runtime.image.activeAddress? point.native.application.base.memory =
          some state.nodes.length
        have hmemory : point.native.application.base.memory =
            execution.native.application.base.memory := congrArg Prod.fst hpoint.2
        rw [hmemory]
        exact hactive
      have hdelivery := runtime.deliveryBlockEnvironment_delivery roster recipients
        point.environmentHistory (State.environmentView runtime.application point.native)
        instruction (point.environmentHistory.length % width) recipient hpointIndex hactivePoint
        rfl hslotRange hrecipient
      rw [hdelivery]
      rfl
    · exact ⟨hrefines, rfl⟩
    · exact hmiddle
  have hmiddleLength : ∀ middle,
      middle ∈ (runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients) before execution).support →
      middle.environmentHistory.length =
        execution.environmentHistory.length + recipients.length := by
    intro middle hmiddle
    simpa only [hbeforeCount] using
      runtime.application.runPolicies_environmentHistory_length players
        (runtime.deliveryBlockEnvironment roster recipients) before execution middle hmiddle
  have hnormal :
      runtime.application.runPolicies players
          (runtime.deliveryBlockEnvironment roster recipients) (before ++ [.environment])
          execution =
        (runtime.application.runPolicies players
          (runtime.deliveryBlockEnvironment roster recipients) before execution).bind fun middle =>
            (L.evalDist dist current.current.source.eraseSampleEnv).map
              (runtime.sampleExecution middle
                (ApplicationPlan.headSampleCode fresh state)) := by
    rw [MessageApplication.runPolicies_append]
    apply FinDist.bind_congr
    intro middle hmiddle
    have hinvariant := hprefixInvariant middle hmiddle
    have hlength := hmiddleLength middle hmiddle
    have hwidth : 0 < width := by simp [width]
    have hbase := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hslot)
    have hbase' : width * (execution.environmentHistory.length / width) =
        execution.environmentHistory.length := by
      simpa [width, Nat.mul_comm] using hbase
    have hdivision : middle.environmentHistory.length / width =
        execution.environmentHistory.length / width := by
      rw [hlength]
      apply Nat.div_eq_of_lt_le
      · rw [hbase]
        omega
      · rw [Nat.add_mul, hbase]
        omega
    have hmod : middle.environmentHistory.length % width = recipients.length := by
      rw [hlength] at hdivision ⊢
      have hdecomp := Nat.mod_add_div middle.environmentHistory.length width
      rw [hlength, hdivision, hbase'] at hdecomp
      omega
    have hpolicy := runtime.deliveryBlockEnvironment_normal roster recipients
      middle.environmentHistory (State.environmentView runtime.application middle.native)
      instruction (by rw [hdivision]; exact hindex)
      (by
        change runtime.image.activeAddress? middle.native.application.base.memory =
          some state.nodes.length
        have hmemory : middle.native.application.base.memory =
            execution.native.application.base.memory := congrArg Prod.fst hinvariant.2
        rw [hmemory]
        exact hactive)
      hmod
    simp only [MessageApplication.runPolicies, MessageApplication.invoke, hpolicy,
      instruction, ApplicationImage.serviceCommand, liftEnvironmentCommand,
      FinDist.pure_bind, FinDist.bind_pure]
    exact (runtime.environmentPolicyStep_sample_source_coupling dist tail fresh state current
      middle hcode
      (by
        have hmemory : middle.native.application.base.memory =
            execution.native.application.base.memory := congrArg Prod.fst hinvariant.2
        rw [hmemory]
        exact hactive) hinvariant.1).1
  have hsuffixRange : ∀ middle,
      middle ∈ (runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients) before execution).support →
      ∀ value : L.Val ty, ∀ index,
        (runtime.sampleExecution middle (ApplicationPlan.headSampleCode fresh state)
          value).environmentHistory.length ≤ index →
        index < (runtime.sampleExecution middle (ApplicationPlan.headSampleCode fresh state)
          value).environmentHistory.length + suffix.countP Invocation.isEnvironment →
        runtime.image.instructions[index / width]? = some instruction := by
    intro middle hmiddle value index hlo hhi
    have hlength : (runtime.sampleExecution middle (ApplicationPlan.headSampleCode fresh state)
        value).environmentHistory.length = execution.environmentHistory.length +
          recipients.length + 1 := by
      simp [sampleExecution, hmiddleLength middle hmiddle]
    rw [hlength] at hlo hhi
    rw [hsuffixCount] at hhi
    have hbase := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hslot)
    have hbase' : width * (execution.environmentHistory.length / width) =
        execution.environmentHistory.length := by
      simpa [width, Nat.mul_comm] using hbase
    have hquotient : index / width = execution.environmentHistory.length / width := by
      apply Nat.div_eq_of_lt_le
      · rw [hbase]
        omega
      · rw [Nat.add_mul, hbase]
        omega
    rw [hquotient]
    exact hindex
  constructor
  · have hschedule : deliveryBlockInvocations roster recipients =
        (before ++ [.environment]) ++ suffix := by
      simp [deliveryBlockInvocations, before, suffix, List.append_assoc]
    rw [hschedule, MessageApplication.runPolicies_append, hnormal, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro middle _
    rw [FinDist.bind_map]
    rfl
  · intro middle hmiddle value hvalue
    obtain ⟨next, hsource, hrefinesNext⟩ :=
      (runtime.environmentPolicyStep_sample_source_coupling dist tail fresh state current
        middle hcode
        (by
          have hstate := hprefixInvariant middle hmiddle
          have hmemory : middle.native.application.base.memory =
              execution.native.application.base.memory := congrArg Prod.fst hstate.2
          rw [hmemory]
          exact hactive)
        (hprefixInvariant middle hmiddle).1).2 value hvalue
    refine ⟨next, hsource, ?_⟩
    intro final hfinal
    let sampled := runtime.sampleExecution middle (ApplicationPlan.headSampleCode fresh state) value
    have hinactive : runtime.image.activeAddress? sampled.native.application.base.memory ≠
        some instruction.address := by
      intro hstillActive
      have hnotDone := runtime.image.activeAddress?_not_done sampled.native.application.base.memory
        instruction.address hstillActive
      have hdone : sampled.native.application.base.memory.done instruction.address = true := by
        change sampled.native.application.base.memory.done state.nodes.length = true
        simp [sampled, sampleExecution, advanceTo, ApplicationImage.State.sample]
      rw [hdone] at hnotDone
      contradiction
    exact runtime.runPolicies_deliveryBlock_inactive_refines next.current.graph.1 roster recipients
      players suffix sampled final instruction (hsuffixRange middle hmiddle value) hinactive
      hrefinesNext hfinal

end Vegas.WindowedApplication
