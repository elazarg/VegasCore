/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanAllocation
import VegasTests.Fixtures

/-! # Out-of-order binding in a generated application image

Two independent opaque bindings precede either binding's conditional
disposition. The second binding is graph-ready before the first and can be
included by the shared message application. Its completed-node set is then
not any written-order prefix.
-/

noncomputable section

namespace VegasTests.ApplicationEarlyBinding

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction GameTheory.Math.Probability

abbrev Player := Fin 2
abbrev FirstBound : VCtx Player simpleExpr := [(0, .sealed 0 .bool)]
abbrev BothBound : VCtx Player simpleExpr :=
  [(1, .sealed 1 .bool), (0, .sealed 0 .bool)]

def firstOpeningGuard :
    Expr ((2, .option .bool) :: eraseVCtx (viewVCtx (0 : Player) BothBound)) .bool :=
  .ite (.isNone (.var 2 .here)) (.constBool true)
    (.eq (.var 2 .here) (.some (.var 0 (.there .here))))

abbrev AfterFirstOpening : VCtx Player simpleExpr :=
  [(3, .pub (.option .bool)), (2, .sealed 0 (.option .bool))] ++ BothBound

def secondOpeningGuard :
    Expr ((4, .option .bool) ::
      eraseVCtx (viewVCtx (1 : Player) AfterFirstOpening)) .bool :=
  .ite (.isNone (.var 4 .here)) (.constBool true)
    (.eq (.var 4 .here) (.some (.var 1 (.there (.there .here)))))

abbrev TerminalContext : VCtx Player simpleExpr :=
  [(5, .pub (.option .bool)), (4, .sealed 1 (.option .bool))] ++ AfterFirstOpening

def tail : VegasCore Player simpleExpr TerminalContext := .ret []

def core : VegasCore Player simpleExpr [] :=
  .commit 0 0 (.constBool true)
    (.commit 1 1 (.constBool true)
      (.commit 2 0 firstOpeningGuard
        (.reveal 3 0 2 .here
          (.commit 4 1 secondOpeningGuard
            (.reveal 5 1 4 .here tail)))))

def source : GraphProgram Player simpleExpr where
  Γ := []
  prog := core
  env := VEnv.empty simpleExpr
  wctx := by simp
  fresh := by simp [core, tail, FreshBindings, Fresh]

def firstSpecification : ConditionalOpening
    (Γ := BothBound) (copyName := 2) (who := (0 : Player))
    (copyTy := .option .bool) firstOpeningGuard where
  secretTy := .bool
  source := 0
  binding := .there .here
  encoding := Equiv.refl (Option Bool)
  sound := by
    intro env chosen hlegal
    change (if chosen.isNone then true else
      decide (chosen = some (env.get (.there .here)))) = true at hlegal
    cases chosen <;> simp_all
  decline_legal := by intro _; rfl

def secondSpecification : ConditionalOpening
    (Γ := AfterFirstOpening) (copyName := 4) (who := (1 : Player))
    (copyTy := .option .bool) secondOpeningGuard where
  secretTy := .bool
  source := 1
  binding := .there (.there .here)
  encoding := Equiv.refl (Option Bool)
  sound := by
    intro env chosen hlegal
    change (if chosen.isNone then true else
      decide (chosen = some (env.get (.there (.there .here))))) = true at hlegal
    cases chosen <;> simp_all
  decline_legal := by intro _; rfl

def accounting : CommitmentAccounting ∅ core := by
  unfold core
  apply CommitmentAccounting.commit (by simp)
  apply CommitmentAccounting.commit (by simp)
  apply CommitmentAccounting.opening firstSpecification
  · simp [firstSpecification]
  · simp
  apply CommitmentAccounting.opening secondSpecification
  · simp [firstSpecification, secondSpecification]
  · simp
  exact CommitmentAccounting.ret (by decide)

def checked : WFProgram Player simpleExpr where
  core := source
  accounted := accounting
  legal := by
    unfold source core
    constructor
    · intro _
      exact ⟨false, rfl⟩
    · constructor
      · intro _
        exact ⟨false, rfl⟩
      · constructor
        · intro _
          exact ⟨none, rfl⟩
        · constructor
          · intro _
            exact ⟨none, rfl⟩
          · trivial

def compilerInitial : BuildState Player simpleExpr source.Γ :=
  BuildState.fromInitial (initialState source.Γ source.env source.wctx)

def secondSite : SourceDecisionSite (1 : Player) source.prog FirstBound 1 .bool
    (.constBool true) := .commit (.here _ _)

def firstOpeningSite : CommitmentAccounting.OpeningSite accounting := by
  unfold accounting
  apply CommitmentAccounting.OpeningSite.commit
  apply CommitmentAccounting.OpeningSite.commit
  apply CommitmentAccounting.OpeningSite.here

def secondOpeningSite : CommitmentAccounting.OpeningSite accounting := by
  unfold accounting
  apply CommitmentAccounting.OpeningSite.commit
  apply CommitmentAccounting.OpeningSite.commit
  apply CommitmentAccounting.OpeningSite.openingTail
  apply CommitmentAccounting.OpeningSite.here

def firstConditionalSite : ConditionalPublicationSite source.prog :=
  firstOpeningSite.conditionalPublicationSite

def secondConditionalSite : ConditionalPublicationSite source.prog :=
  secondOpeningSite.conditionalPublicationSite

theorem first_publicly_validatable :
    firstConditionalSite.PubliclyValidatable source.fresh compilerInitial := by
  intro ref href
  left
  change ref ∈ ({({ field := 0, ty := .bool } : FieldRef simpleExpr)} :
    Finset (FieldRef simpleExpr)) at href
  change ref = ({ field := 0, ty := .bool } : FieldRef simpleExpr)
  simpa using href

theorem second_publicly_validatable :
    secondConditionalSite.PubliclyValidatable source.fresh compilerInitial := by
  intro ref href
  left
  change ref ∈ ({({ field := 1, ty := .bool } : FieldRef simpleExpr)} :
    Finset (FieldRef simpleExpr)) at href
  change ref = ({ field := 1, ty := .bool } : FieldRef simpleExpr)
  simpa using href

def applicationPlan : ApplicationPlan accounting source.fresh compilerInitial := by
  apply ApplicationPlan.binding
  · intro _ _
    rfl
  apply ApplicationPlan.binding
  · intro _ _
    rfl
  apply ApplicationPlan.conditional
  · exact first_publicly_validatable
  apply ApplicationPlan.conditional
  · exact second_publicly_validatable
  apply ApplicationPlan.ret

def image : ApplicationImage Player simpleExpr := applicationPlan.image (fun _ => 10)

abbrev compiled := compileCore source.prog source.fresh compilerInitial

def secondCode : BindingCode Player simpleExpr :=
  secondSite.bindingCode source.fresh compilerInitial 1

theorem image_lookup_second : image.lookup secondCode.node = some (.bind secondCode) := by
  change (applicationPlan.image (fun _ => 10)).lookup
    (ApplicationInstruction.bind secondCode).address = some (.bind secondCode)
  apply applicationPlan.image_lookup_of_mem (fun _ => 10)
  change _ ∈ [_, ApplicationInstruction.bind secondCode, _, _]
  simp

def initialNative : ApplicationImage.State Player simpleExpr :=
  ApplicationImage.State.initial (ApplicationImage.Memory.initial compiled.graph)

def initialExecution : image.application.State :=
  MessageApplication.State.initial image.application initialNative

def prepared : image.application.State :=
  { initialExecution with
    application := initialExecution.application.register 1 1 ⟨.bool, false⟩ }

def submitted : image.application.State :=
  { prepared with pool := (prepared.pool.submit 1 (.binding secondCode.node (1, 1))).2 }

def included : image.application.State :=
  image.application.includePending submitted (1, 0)

def actions : List image.application.Action :=
  [.privateCommand 1 (.register 1 ⟨.bool, false⟩),
    .submit 1 (.binding secondCode.node (1, 1)), .include (1, 0)]

/-- The actual shared runner accepts the later generated binding while the
earlier source binding remains unresolved. -/
theorem early_binding_run :
    image.application.run actions initialExecution = FinDist.pure included := by
  simp only [actions, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, FinDist.pure_bind]
  rfl

theorem early_binding_done_shape :
    included.receipts = [((1, 0), true)] ∧
      included.application.memory.done 0 = false ∧
      included.application.memory.done 1 = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- Completing node one without node zero is not a written-order prefix at
any cursor, not merely a mismatch with the initial cursor. -/
theorem early_binding_has_no_completed_prefix :
    ¬∃ bound : Nat, ∀ node : Fin compiled.graph.nodeCount,
      (included.application.memory.done node = true ↔ node.val < bound) := by
  rintro ⟨bound, hprefix⟩
  let first : Fin compiled.graph.nodeCount := ⟨0, by decide⟩
  let second : Fin compiled.graph.nodeCount := ⟨1, by decide⟩
  have hfirst : included.application.memory.done first = false := by rfl
  have hsecond : included.application.memory.done second = true := by rfl
  have hnotPositive : ¬0 < bound := by
    intro hpositive
    have hdone := (hprefix first).2 hpositive
    rw [hfirst] at hdone
    contradiction
  have hbound : bound = 0 := Nat.eq_zero_of_not_pos hnotPositive
  have hlt := (hprefix second).1 hsecond
  omega

end VegasTests.ApplicationEarlyBinding

/-- info: 'VegasTests.ApplicationEarlyBinding.early_binding_run' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationEarlyBinding.early_binding_run

/-- info:
'VegasTests.ApplicationEarlyBinding.early_binding_has_no_completed_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationEarlyBinding.early_binding_has_no_completed_prefix
