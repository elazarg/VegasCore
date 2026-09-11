/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.BindingTimeoutCompilation
import Vegas.Compile.WindowedRelayResolution
import Vegas.Compile.WindowedSourceSafety
import VegasTests.ConditionalApplicationImage

/-! # Resolution-ready states of the generated conditional fragment -/

noncomputable section

namespace VegasTests.ConditionalApplicationImage

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  GameTheory.Math.Probability

/-- The source-authorized nonresponse value for the initial binding. -/
def bindingFallback : SourceDecisionSite.PublicFallback initialSite where
  expr := .constBool false
  legal := by intro _; rfl

def bindingSelector (code : BindingCode Player simpleExpr) :
    Option (PublicFallbackCode simpleExpr code.ty) :=
  bindingFallback.selectBindingTimeout source.fresh compilerInitial 0 code

/-- The actual generated, ordered, activation-relative application. -/
def runtime : WindowedApplication Player simpleExpr :=
  applicationPlan.windowed (fun _ => 0) bindingSelector (fun _ => none) (fun _ => 10)

def timedBindingCode : BindingCode Player simpleExpr :=
  bindingFallback.bindingTimeoutCode source.fresh compilerInitial 0

def initialPolicyExecution : runtime.application.PolicyExecution :=
  MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (runtime.initial initialNative))

/-- Remaining emitted instructions, counted by their unique dispatch addresses. -/
def unresolvedCount (state : WindowedApplication.State Player simpleExpr) : Nat :=
  runtime.image.instructions.countP fun instruction => !state.base.memory.done instruction.address

theorem runtime_instructions : runtime.image.instructions =
    [.bind timedBindingCode, .conditional (conditionalCode 0)] := by
  rfl

@[simp] theorem timedBindingCode_owner : timedBindingCode.owner = 0 := rfl
@[simp] theorem timedBindingCode_ty : timedBindingCode.ty = .bool := rfl
@[simp] theorem timedBindingCode_node : timedBindingCode.node = 0 := rfl
@[simp] theorem timedBindingCode_sourceField : timedBindingCode.sourceField = 0 := rfl
@[simp] theorem timedBindingCode_sourceSlot : timedBindingCode.sourceSlot = 0 := rfl
@[simp] theorem timedBindingCode_requires : timedBindingCode.requires = [] := rfl

@[simp] theorem conditionalCode_sourceField : (conditionalCode 0).sourceField = 0 := rfl
@[simp] theorem conditionalCode_secretTy : (conditionalCode 0).secretTy = .bool := rfl
@[simp] theorem conditionalSite_secretTy :
    conditionalSite.specification.secretTy = .bool := rfl
@[simp] theorem conditionalCode_owner : (conditionalCode 0).endpoint.owner = 0 := rfl
@[simp] theorem conditionalCode_sourceSlot :
    (conditionalCode 0).endpoint.sourceSlot = 0 := rfl

@[simp] theorem runtime_lookup_binding :
    runtime.image.lookup timedBindingCode.node = some (.bind timedBindingCode) := by
  rw [ApplicationImage.lookup, runtime_instructions]
  rfl

@[simp] theorem runtime_lookup_conditional :
    runtime.image.lookup (conditionalCode 0).endpoint.publicationNode =
      some (.conditional (conditionalCode 0)) := by
  rw [ApplicationImage.lookup, runtime_instructions]
  rfl

/-- Atomic conditional resolution keeps its generated choice and publication
completion flags equal in every state satisfying the ordered-prefix invariant. -/
theorem conditional_done_eq (state : WindowedApplication.State Player simpleExpr)
    (hprefix : runtime.image.CompletedPrefix state.base.memory) :
    state.base.memory.done 1 = state.base.memory.done 2 := by
  rcases hprefix with ⟨before, rest, himage, hdone⟩
  rw [runtime_instructions] at himage
  cases before with
  | nil =>
      have hdone1 : state.base.memory.done 1 = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        have hmem := (hdone 1).mp htrue
        simp at hmem
      have hdone2 : state.base.memory.done 2 = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        have hmem := (hdone 2).mp htrue
        simp at hmem
      rw [hdone1, hdone2]
  | cons first tail =>
      cases tail with
      | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at himage
          rcases himage with ⟨rfl, rfl⟩
          have hdone1 : state.base.memory.done 1 = false := by
            rw [Bool.eq_false_iff]
            intro htrue
            have hmem := (hdone 1).mp htrue
            simp [ApplicationInstruction.coveredNodes] at hmem
          have hdone2 : state.base.memory.done 2 = false := by
            rw [Bool.eq_false_iff]
            intro htrue
            have hmem := (hdone 2).mp htrue
            simp [ApplicationInstruction.coveredNodes] at hmem
          rw [hdone1, hdone2]
      | cons second tail =>
          cases tail with
          | nil =>
              simp only [List.cons_append, List.nil_append, List.cons.injEq] at himage
              rcases himage with ⟨rfl, rfl, rfl⟩
              have hdone1 : state.base.memory.done 1 = true :=
                (hdone 1).mpr (by simp [ApplicationInstruction.coveredNodes])
              have hdone2 : state.base.memory.done 2 = true :=
                (hdone 2).mpr (by simp [ApplicationInstruction.coveredNodes])
              rw [hdone1, hdone2]
          | cons third more =>
              have hlength := congrArg List.length himage
              simp only [List.length_cons, List.length_append, List.length_nil] at hlength
              omega

theorem unresolvedCount_le_two (state : WindowedApplication.State Player simpleExpr) :
    unresolvedCount state ≤ 2 := by
  unfold unresolvedCount
  calc
    _ ≤ runtime.image.instructions.length := List.countP_le_length
    _ = 2 := by rw [runtime_instructions]; rfl

/-- For this exact generated fragment, the two dispatch addresses are complete
exactly when all three graph nodes are complete. `CompletedPrefix` supplies the
atomic equality of the conditional choice and publication nodes. -/
theorem finished_iff_dispatch_done
    (state : WindowedApplication.State Player simpleExpr)
    (hprefix : runtime.image.CompletedPrefix state.base.memory) :
    state.base.memory.finished compiled.graph.nodeCount = true ↔
      state.base.memory.done 0 = true ∧ state.base.memory.done 2 = true := by
  have hpair := conditional_done_eq state hprefix
  unfold ApplicationImage.Memory.finished
  change
    (state.base.memory.done 0 &&
      (state.base.memory.done 1 && (state.base.memory.done 2 && true))) = true ↔ _
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨hbinding, _, hconditional⟩
    exact ⟨hbinding, hconditional.1⟩
  · rintro ⟨hbinding, hconditional⟩
    exact ⟨hbinding, hpair.trans hconditional, ⟨hconditional, trivial⟩⟩

theorem unresolvedCount_zero_iff_finished
    (state : WindowedApplication.State Player simpleExpr)
    (hprefix : runtime.image.CompletedPrefix state.base.memory) :
    unresolvedCount state = 0 ↔
      state.base.memory.finished compiled.graph.nodeCount = true := by
  rw [finished_iff_dispatch_done state hprefix]
  unfold unresolvedCount
  rw [runtime_instructions]
  simp only [List.countP_cons, List.countP_nil, ApplicationInstruction.address]
  cases hzero : state.base.memory.done 0 <;>
    cases hconditional : state.base.memory.done 2 <;>
    simp [hzero, hconditional]

theorem finished_active_none
    (state : WindowedApplication.State Player simpleExpr)
    (hprefix : runtime.image.CompletedPrefix state.base.memory)
    (hconsistent : runtime.Consistent state)
    (hfinished : state.base.memory.finished compiled.graph.nodeCount = true) :
    state.active = none := by
  obtain ⟨hbinding, hconditional⟩ :=
    (finished_iff_dispatch_done state hprefix).mp hfinished
  have haddress : runtime.image.activeAddress? state.base.memory = none := by
    simp [ApplicationImage.activeAddress?, runtime_instructions, hbinding, hconditional,
      ApplicationInstruction.address]
  cases hactive : state.active with
  | none => rfl
  | some activation =>
      have hkeys := hconsistent.1
      simp [hactive, haddress] at hkeys

theorem inactive_finished
    (state : WindowedApplication.State Player simpleExpr)
    (hprefix : runtime.image.CompletedPrefix state.base.memory)
    (hconsistent : runtime.Consistent state)
    (hinactive : state.active = none) :
    state.base.memory.finished compiled.graph.nodeCount = true := by
  have haddress : runtime.image.activeAddress? state.base.memory = none := by
    simpa [hinactive] using hconsistent.1.symm
  apply (finished_iff_dispatch_done state hprefix).mpr
  by_cases hbinding : state.base.memory.done 0 = true
  · refine ⟨hbinding, ?_⟩
    by_cases hconditional : state.base.memory.done 2 = true
    · exact hconditional
    · have hconditionalFalse := Bool.eq_false_iff.mpr hconditional
      have : runtime.image.activeAddress? state.base.memory = some 2 := by
        simp [ApplicationImage.activeAddress?, runtime_instructions, hbinding,
          hconditionalFalse, ApplicationInstruction.address]
      rw [this] at haddress
      contradiction
  · have hbindingFalse := Bool.eq_false_iff.mpr hbinding
    have : runtime.image.activeAddress? state.base.memory = some 0 := by
      simp [ApplicationImage.activeAddress?, runtime_instructions, hbindingFalse,
        ApplicationInstruction.address]
    rw [this] at haddress
    contradiction

/-- The safety invariants of an initialized generated run suffice to classify
an overdue active state. It is either finished, or its actual public expiry
handler succeeds and strictly decreases the number of unresolved emitted
instructions. No progress or completion premise is stored in the invariants. -/
theorem overdue_expiry_resolves
    (state : WindowedApplication.State Player simpleExpr)
    (cfg : Config compiled.graph)
    (hrefines : state.base.Refines cfg)
    (hprefix : runtime.image.CompletedPrefix state.base.memory)
    (hresolved : runtime.image.ResolvedBindings state.base)
    (hconsistent : runtime.Consistent state)
    (hoverdue : ∀ activation, state.active = some activation →
      activation.since + runtime.windowOf activation.key < state.base.memory.clock)
    (id : MessageId Player) :
    state.base.memory.finished compiled.graph.nodeCount = true ∨
      ∃ payload next,
        runtime.dueExpiry? (state.base.memory, state.active) = some payload ∧
        runtime.handle state ⟨id, payload⟩ = some next ∧
        unresolvedCount next < unresolvedCount state := by
  by_cases hbindingDone : state.base.memory.done 0 = true
  · by_cases hconditionalDone : state.base.memory.done 2 = true
    · left
      have hpair := conditional_done_eq state hprefix
      unfold ApplicationImage.Memory.finished
      apply List.all_eq_true.mpr
      intro node hnode
      rw [List.mem_range] at hnode
      change node < 3 at hnode
      cases node with
      | zero => exact hbindingDone
      | succ node =>
          cases node with
          | zero => simpa [hpair] using hconditionalDone
          | succ node =>
              cases node with
              | zero => exact hconditionalDone
              | succ node => omega
    · right
      have hconditionalFalse : state.base.memory.done 2 = false :=
        Bool.eq_false_iff.mpr hconditionalDone
      have hchoiceFalse : state.base.memory.done 1 = false := by
        rw [conditional_done_eq state hprefix]
        exact hconditionalFalse
      have hactiveAddress : runtime.image.activeAddress? state.base.memory = some 2 := by
        simp [ApplicationImage.activeAddress?, runtime_instructions, hbindingDone,
          hconditionalFalse, ApplicationInstruction.address]
      cases hactive : state.active with
      | none =>
          have := hconsistent.1
          simp [hactive, hactiveAddress] at this
      | some activation =>
          have hkey : activation.key = 2 := by
            simpa [hactive, hactiveAddress] using hconsistent.1
          have hlookup : runtime.image.lookup activation.key =
              some (.conditional (conditionalCode 0)) := by
            simpa [hkey] using runtime_lookup_conditional
          obtain ⟨disposition, haccepted, hcanonical⟩ :=
            hresolved timedBindingCode (by simp [runtime_instructions]) hbindingDone
          have hbinding : ∃ accepted,
              (conditionalCode 0).binding? state.base.memory = some accepted ∧
              (∀ handle, accepted = .opaque handle → handle = (0, 0)) := by
            cases disposition with
            | «opaque» handle =>
                refine ⟨.opaque handle,
                  ((conditionalCode 0).binding?_opaque_iff _ handle).2 (by
                    change state.base.memory.accepted 0 = some (.opaque handle)
                    exact haccepted), ?_⟩
                intro other heq
                cases heq
                simpa using hcanonical handle rfl
            | publicDefault typed =>
                obtain ⟨spec, hfield, _, htyped, _⟩ :=
                  hrefines.bindings.publicDefault _ typed (by simpa using haccepted)
                obtain ⟨expected, hexpected, hexpectedTy, _⟩ :=
                  conditionalSite.compiledSourceField source.fresh compilerInitial
                have hspec : spec = expected := Option.some.inj (hfield.symm.trans hexpected)
                subst expected
                have hty : typed.ty = (conditionalCode 0).secretTy := by
                  exact (htyped.trans hexpectedTy).trans conditionalSite_secretTy
                cases typed with
                | mk ty value =>
                    cases hty
                    refine ⟨.publicDefault value,
                      ((conditionalCode 0).binding?_publicDefault_iff _ value).2
                        ⟨⟨_, value⟩, (by
                          change state.base.memory.accepted 0 =
                            some (.publicDefault ⟨.bool, value⟩)
                          exact haccepted), by simp [TypedValue.as?]⟩, ?_⟩
                    intro handle heq
                    cases heq
          have hready : (conditionalCode 0).endpoint.readyDisposition
              ((conditionalCode 0).binding? state.base.memory)
              state.base.memory.done = true := by
            obtain ⟨accepted, haccepted, hcanonical⟩ := hbinding
            rw [haccepted]
            cases accepted with
            | «opaque» handle =>
                have hh := hcanonical handle rfl
                simp [ConditionalPublication.readyDisposition, ConditionalPublication.ready,
                  hh, hchoiceFalse, hconditionalFalse, hbindingDone]
            | publicDefault value =>
                simp [ConditionalPublication.readyDisposition,
                  ConditionalPublication.defaultReady, hchoiceFalse,
                  hconditionalFalse, hbindingDone]
          let next := runtime.advanceTo state
            (state.base.publishConditional (conditionalCode 0) none)
          refine ⟨.conditional 2 .expire, next, ?_, ?_, ?_⟩
          · unfold WindowedApplication.dueExpiry?
            simp only [Option.bind_eq_bind, Option.bind_some]
            rw [if_pos ⟨by simpa [hkey] using hactiveAddress,
              hoverdue activation hactive⟩, hlookup]
            simp [ApplicationInstruction.expiryPayload?]
          · simpa [hkey, next] using runtime.handle_conditionalExpire_after_window
              state activation hconsistent hactive (conditionalCode 0) hlookup hready
              (hoverdue activation hactive) id
          · simp only [unresolvedCount, runtime_instructions, List.countP_cons,
              List.countP_nil, ApplicationInstruction.address, next,
              WindowedApplication.advanceTo, ApplicationImage.State.publishConditional]
            simp [hbindingDone, hconditionalFalse]
  · right
    have hbindingFalse : state.base.memory.done 0 = false :=
      Bool.eq_false_iff.mpr hbindingDone
    have hactiveAddress : runtime.image.activeAddress? state.base.memory = some 0 := by
      simp [ApplicationImage.activeAddress?, runtime_instructions, hbindingFalse,
        ApplicationInstruction.address]
    cases hactive : state.active with
    | none =>
        have := hconsistent.1
        simp [hactive, hactiveAddress] at this
    | some activation =>
        have hkey : activation.key = 0 := by
          simpa [hactive, hactiveAddress] using hconsistent.1
        have hlookup : runtime.image.lookup activation.key = some (.bind timedBindingCode) := by
          simpa [hkey] using runtime_lookup_binding
        have hcfgNotDone : (⟨0, by decide⟩ : Fin compiled.graph.nodeCount) ∉ cfg.done := by
          intro hdone
          have htrue := (hrefines.memory.completed ⟨0, by decide⟩).2 hdone
          rw [hbindingFalse] at htrue
          contradiction
        have hunbound : state.base.memory.accepted timedBindingCode.sourceField = none := by
          change state.base.memory.accepted 0 = none
          exact hrefines.accepted_eq_none_of_not_done
            (⟨0, by decide⟩ : Fin compiled.graph.nodeCount) hcfgNotDone
        let timeout : PublicFallbackCode simpleExpr timedBindingCode.ty :=
          ⟨0, bindingFallback.compiled source.fresh compilerInitial⟩
        have htimeout : timedBindingCode.timeout = some timeout := rfl
        let value : simpleExpr.Val timedBindingCode.ty := false
        have hvalue : timeout.value.evalStore? state.base.memory.store = some value := by
          rfl
        let next := runtime.advanceTo state
          (state.base.defaultBind timedBindingCode ⟨timedBindingCode.ty, value⟩)
        refine ⟨.expireBinding 0, next, ?_, ?_, ?_⟩
        · unfold WindowedApplication.dueExpiry?
          simp only [Option.bind_eq_bind, Option.bind_some]
          rw [if_pos ⟨by simpa [hkey] using hactiveAddress,
            hoverdue activation hactive⟩, hlookup]
          simp [ApplicationInstruction.expiryPayload?, htimeout]
        · simpa [hkey, next] using runtime.handle_expireBinding_after_window state activation
            hconsistent hactive timedBindingCode hlookup timeout htimeout hunbound hbindingFalse
            (by rfl) (hoverdue activation hactive) value hvalue id
        · simp only [unresolvedCount, runtime_instructions, List.countP_cons,
            List.countP_nil, ApplicationInstruction.address, next,
            WindowedApplication.advanceTo, ApplicationImage.State.defaultBind]
          cases hconditional : state.base.memory.done 2 <;> simp [hbindingFalse, hconditional]

end VegasTests.ConditionalApplicationImage
