/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockIsolation
import Vegas.Compile.ApplicationDeadlineIndependence
import Vegas.Compile.PublicChoiceSourceCoupling

/-! # Native admission of a source-legal public choice -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A canonical source-legal public choice is accepted by the actual windowed
handler and its inclusion makes the publication instruction inactive. -/
theorem handle_source_publicChoice_and_include_inactive
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (state : State P L) (activation : Activation Nat) (serial : Nat)
    (value : L.Val
      ((PublicChoiceSite.atHead name publicName who guard tail).code fresh build).guard.ty)
    (timeout : Option (PublicFallbackCode L
      ((PublicChoiceSite.atHead name publicName who guard tail).code fresh build).guard.ty))
    (hrefines : state.base.Refines current.current.graph.1)
    (hlegal : evalGuard guard value ((current.current.source.toView who).eraseEnv) = true)
    (hactivation : state.active = some activation)
    (hactive : runtime.image.activeAddress? state.base.memory = some activation.key)
    (hcode : runtime.image.lookup activation.key = some (.publicChoice
      { (PublicChoiceSite.atHead name publicName who guard tail).code fresh build with
        timeout := timeout }))
    (pool : MessagePool P (ApplicationImage.Payload P L))
    (receipts : List (MessageId P × Bool))
    (hlookup : pool.lookup (who, serial) = some
      ⟨(who, serial), .choice activation.key ⟨_, value⟩⟩) :
    let site := PublicChoiceSite.atHead name publicName who guard tail
    let code : PublicChoiceCode P L := { site.code fresh build with timeout := timeout }
    let message : Message P (ApplicationImage.Payload P L) :=
      ⟨(who, serial), .choice activation.key ⟨_, value⟩⟩
    runtime.handle state message = some (runtime.advanceTo state (state.base.publish code value)) ∧
      runtime.image.activeAddress?
        (runtime.application.includePending ⟨state, pool, receipts⟩ (who, serial)
          ).application.base.memory ≠ some activation.key := by
  dsimp only
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let code : PublicChoiceCode P L := { site.code fresh build with timeout := timeout }
  let message : Message P (ApplicationImage.Payload P L) :=
    ⟨(who, serial), .choice activation.key ⟨_, value⟩⟩
  have hready := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
    state.base.memory.done hrefines.memory.completed
  have hresolve : code.endpoint.resolve? state.base.memory.done
      (code.guard.validate state.base.memory.store) ⟨(who, serial), value⟩ = some value := by
    apply (site.code_resolves_iff_source_legal fresh build current.current.graph.1.store
      state.base.memory.store current.current.source heligible current.current.agrees
      hrefines.memory.publicFields state.base.memory.done hready serial value).mpr
    exact hlegal
  have hplain : runtime.image.handle state.base message =
      some (state.base.publish code value) := by
    have hchoice := runtime.image.handle_choice state.base activation.key code hcode
      (who, serial) (show L.Val code.guard.ty from value)
    have hmapped : Option.map (state.base.publish code)
        (code.endpoint.resolve? state.base.memory.done
          (code.guard.validate state.base.memory.store) ⟨(who, serial), value⟩) =
          some (state.base.publish code value) := by simp [hresolve]
    simpa [message, code, site] using hchoice.trans hmapped
  have hordered : runtime.image.orderedApplication.handle state.base message =
      some (state.base.publish code value) := by
    rw [runtime.image.ordered_handle_eq state.base message activation.key]
    · exact hplain
    · rfl
    · exact hactive
  have hindependent : message.payload.DeadlineIndependent := by
    simp [message, ApplicationImage.Payload.DeadlineIndependent]
  have htimed : (runtime.atOrigin activation.since).orderedApplication.handle state.base message =
      some (state.base.publish code value) := by
    change (runtime.image.withDeadlines
      (fun address => activation.since + runtime.windowOf address)).orderedApplication.handle
        state.base message = _
    rw [runtime.image.ordered_handle_withDeadlines_eq _ state.base message hindependent]
    exact hordered
  have hhandle : runtime.handle state message =
      some (runtime.advanceTo state (state.base.publish code value)) := by
    simp only [WindowedApplication.handle, hactivation, Option.bind_eq_bind,
      Option.bind_some, hactive, if_pos, htimed, Option.pure_def]
  refine ⟨hhandle, ?_⟩
  have hincluded := runtime.application.includePending_accept
    (⟨state, pool, receipts⟩ : runtime.application.State) (who, serial) message
    (runtime.advanceTo state (state.base.publish code value)) hlookup hhandle
  rw [hincluded]
  obtain ⟨address, hbefore, _, hafter⟩ := runtime.handle_resolves_active state
    (runtime.advanceTo state (state.base.publish code value)) message hhandle
  have : address = activation.key := Option.some.inj (hbefore.symm.trans hactive)
  simpa [this] using hafter

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_source_publicChoice_and_include_inactive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_source_publicChoice_and_include_inactive
