/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockIsolation
import Vegas.Compile.ApplicationDeadlineIndependence
import Vegas.Compile.ConditionalSourceCoupling

/-! # Native admission of a source-legal conditional publication -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A disposition-appropriate canonical conditional request generated from a
legal source value is accepted by the windowed handler. Its inclusion makes
the conditional publication instruction inactive. -/
theorem handle_source_conditional_and_include_inactive
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (heligible : (ConditionalPublicationSite.atHead name publicName who guard tail
      spec).PubliclyValidatable fresh build)
    (state : State P L) (activation : Activation Nat) (serial : Nat)
    (hrefines : state.base.Refines current.current.graph.1)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
      fresh build sourceSlot deadline).binding? state.base.memory = some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who, sourceSlot))
    (chosen : L.Val ty)
    (hlegal : evalGuard guard chosen ((current.current.source.toView who).eraseEnv) = true)
    (hfrozen : ∀ handle value, disposition = .opaque handle →
      spec.encoding chosen = some value →
      (state.base.frozen (build.fieldOf spec.binding)).bind
        (fun typed => typed.as? spec.secretTy) = some value)
    (hactivation : state.active = some activation)
    (hactive : runtime.image.activeAddress? state.base.memory = some activation.key)
    (hcode : runtime.image.lookup activation.key = some (.conditional
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
        fresh build sourceSlot deadline)))
    (pool : MessagePool P (ApplicationImage.Payload P L))
    (receipts : List (MessageId P × Bool))
    (hlookup : pool.lookup (who, serial) = some ⟨(who, serial), .conditional activation.key
      ((ConditionalPublicationSite.atHead name publicName who guard tail
        spec).sourceRequestPayload fresh build sourceSlot deadline disposition
          (spec.encoding chosen))⟩) :
    let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
    let code := site.code fresh build sourceSlot deadline
    let result := spec.encoding chosen
    let payload := site.sourceRequestPayload fresh build sourceSlot deadline disposition result
    let message : Message P (ApplicationImage.Payload P L) :=
      ⟨(who, serial), .conditional activation.key payload⟩
    runtime.handle state message =
        some (runtime.advanceTo state (state.base.publishConditional code result)) ∧
      runtime.image.activeAddress?
        (runtime.application.includePending ⟨state, pool, receipts⟩ (who, serial)
          ).application.base.memory ≠ some activation.key := by
  dsimp only
  let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
  let code := site.code fresh build sourceSlot deadline
  let result := spec.encoding chosen
  let payload := site.sourceRequestPayload fresh build sourceSlot deadline disposition result
  let message : Message P (ApplicationImage.Payload P L) :=
    ⟨(who, serial), .conditional activation.key payload⟩
  change code.binding? state.base.memory = some disposition at hbinding
  have hdefault : ∀ value, disposition = .publicDefault value →
      value = current.current.source.get spec.binding := by
    intro value hdisposition
    subst disposition
    obtain ⟨typed, haccepted, htyped⟩ :=
      (code.binding?_publicDefault_iff state.base.memory value).1 hbinding
    obtain ⟨_fieldSpec, _hfield, _howner, _hty, hstored⟩ :=
      hrefines.bindings.publicDefault code.sourceField typed haccepted
    have hgraphValue : Store.getAs current.current.graph.1.store code.sourceField
        spec.secretTy = some value := by
      rw [Store.getAs, hstored]
      exact htyped
    have hsourceValue := current.current.agrees spec.binding
    change Store.getAs current.current.graph.1.store (build.fieldOf spec.binding)
      spec.secretTy = some (current.current.source.get spec.binding) at hsourceValue
    have hfield : code.sourceField = build.fieldOf spec.binding := rfl
    rw [hfield] at hgraphValue
    exact Option.some.inj (hgraphValue.symm.trans hsourceValue)
  have hready := ConditionalPublicationSite.readyDisposition_at_source_prefix
    guard tail spec fresh build sourceSlot deadline current state.base hrefines
      disposition hbinding hcanonical
  change code.endpoint.readyDisposition (code.binding? state.base.memory)
    state.base.memory.done = true at hready
  have hdecode : ∃ decoded, code.decode payload = some decoded ∧
      code.endpoint.resolveDisposition? state.base.memory.clock
        (state.base.verify code) (code.binding? state.base.memory)
        state.base.memory.done (code.canOpen state.base.memory.store)
        ⟨(who, serial), decoded⟩ = some result := by
    cases disposition with
    | «opaque» handle =>
        have hhandle := hcanonical handle rfl
        subst handle
        refine ⟨code.endpoint.requestPayload result, code.decode_requestPayload result, ?_⟩
        simp only [ConditionalPublication.resolveDisposition?, hbinding]
        have hopaqueReady : code.endpoint.ready (some (who, sourceSlot))
            state.base.memory.done = true := by
          simpa only [ConditionalPublication.readyDisposition, hbinding] using hready
        apply (code.endpoint.resolve_requestPayload state.base.memory.clock
          (state.base.verify code) (some (who, sourceSlot)) state.base.memory.done
          (code.canOpen state.base.memory.store) hopaqueReady serial result).2
        cases hresult : result with
        | none => trivial
        | some value =>
            constructor
            · simpa [ApplicationImage.State.verify, code, ConditionalPublicationSite.code,
                site, ConditionalPublicationSite.atHead,
                ConditionalPublicationSite.sourceField, PublicChoiceSite.siteState,
                PublicChoiceSite.atHead, decisionSiteState]
                using hfrozen (who, sourceSlot) value rfl hresult
            · change site.canOpen fresh build state.base.memory.store value = true
              have hvalue := spec.successful_value_eq_binding current.current.source
                chosen value hlegal hresult
              rw [site.canOpen_source fresh build current.current.graph.1.store
                state.base.memory.store current.current.source heligible
                current.current.agrees hrefines.memory.publicFields value hvalue]
              have hchosen : spec.encoding.symm (some value) = chosen := by
                rw [← hresult]
                exact spec.encoding.symm_apply_apply chosen
              change evalGuard guard (spec.encoding.symm (some value))
                ((current.current.source.toView who).eraseEnv) = true
              rw [hchosen]
              exact hlegal
    | publicDefault stored =>
        have hdefaultReady : code.endpoint.defaultReady state.base.memory.done = true := by
          simpa only [ConditionalPublication.readyDisposition, hbinding] using hready
        cases hresult : result with
        | none =>
            refine ⟨.decline, by
              simp [payload, ConditionalPublicationSite.sourceRequestPayload, result, hresult,
                ConditionalCode.decode], ?_⟩
            simp only [ConditionalPublication.resolveDisposition?, hbinding]
            exact (code.endpoint.resolveDefault_decline state.base.memory.clock stored
              state.base.memory.done (code.canOpen state.base.memory.store)
              (who, serial)).2 ⟨hdefaultReady, rfl⟩
        | some value =>
            refine ⟨.cleartext value, ?_, ?_⟩
            · simp only [payload, ConditionalPublicationSite.sourceRequestPayload,
                result, hresult]
              change code.decode (.cleartext ⟨code.secretTy, value⟩) =
                some (.cleartext value)
              simp [ConditionalCode.decode, TypedValue.as?]
            · simp only [ConditionalPublication.resolveDisposition?, hbinding]
              apply (code.endpoint.resolveDefault_cleartext state.base.memory.clock
                stored value state.base.memory.done (code.canOpen state.base.memory.store)
                (who, serial)).2
              have hvalue := spec.successful_value_eq_binding current.current.source
                chosen value hlegal hresult
              have hstored := hdefault stored rfl
              have heq : value = stored := hvalue.trans hstored.symm
              refine ⟨hdefaultReady, rfl, heq, ?_⟩
              change site.canOpen fresh build state.base.memory.store value = true
              rw [site.canOpen_source fresh build current.current.graph.1.store
                state.base.memory.store current.current.source heligible
                current.current.agrees hrefines.memory.publicFields value hvalue]
              have hchosen : spec.encoding.symm (some value) = chosen := by
                rw [← hresult]
                exact spec.encoding.symm_apply_apply chosen
              change evalGuard guard (spec.encoding.symm (some value))
                ((current.current.source.toView who).eraseEnv) = true
              rw [hchosen]
              exact hlegal
  obtain ⟨decoded, hdecode, hresolve⟩ := hdecode
  have hplain : runtime.image.handle state.base message =
      some (state.base.publishConditional code result) := by
    have hconditional := runtime.image.handle_conditional state.base activation.key code hcode
      (who, serial) payload decoded hdecode
    rw [hresolve, Option.map_some] at hconditional
    exact hconditional
  have hordered : runtime.image.orderedApplication.handle state.base message =
      some (state.base.publishConditional code result) := by
    rw [runtime.image.ordered_handle_eq state.base message activation.key]
    · exact hplain
    · rfl
    · exact hactive
  have hindependent : message.payload.DeadlineIndependent := by
    cases disposition <;> cases hresult : result <;>
      simp [message, payload, ConditionalPublicationSite.sourceRequestPayload,
        ConditionalCode.requestPayload, ApplicationImage.Payload.DeadlineIndependent, hresult]
  have htimed : (runtime.atOrigin activation.since).orderedApplication.handle state.base message =
      some (state.base.publishConditional code result) := by
    change (runtime.image.withDeadlines
      (fun address => activation.since + runtime.windowOf address)).orderedApplication.handle
        state.base message = _
    rw [runtime.image.ordered_handle_withDeadlines_eq _ state.base message hindependent]
    exact hordered
  have hhandle : runtime.handle state message =
      some (runtime.advanceTo state (state.base.publishConditional code result)) := by
    simp only [WindowedApplication.handle, hactivation, Option.bind_eq_bind,
      Option.bind_some, hactive, if_pos, htimed, Option.pure_def]
  refine ⟨hhandle, ?_⟩
  have hincluded := runtime.application.includePending_accept
    (⟨state, pool, receipts⟩ : runtime.application.State) (who, serial) message
    (runtime.advanceTo state (state.base.publishConditional code result)) hlookup hhandle
  rw [hincluded]
  obtain ⟨address, hbefore, _, hafter⟩ := runtime.handle_resolves_active state
    (runtime.advanceTo state (state.base.publishConditional code result)) message hhandle
  have : address = activation.key := Option.some.inj (hbefore.symm.trans hactive)
  simpa [this] using hafter

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_source_conditional_and_include_inactive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_source_conditional_and_include_inactive
