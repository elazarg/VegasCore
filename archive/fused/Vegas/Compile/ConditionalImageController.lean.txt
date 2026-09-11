/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalImage
import Vegas.Compile.ConditionalOpeningController

/-! # Source controllers for generated conditional-publication images

This module supplies the typed payload transport between a certified
conditional-publication occurrence and `ApplicationImage`. Choice readout is
still provided by application assembly because it includes the choosing
player's full source-visible information, not only public guard dependencies.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationImage

/-- Canonical dynamic image payload for a typed conditional-publication
request. Decoding checks the type of opening claims and rejects every other
image payload constructor. -/
def conditionalTransport (secretTy : L.Ty) :
    ChoiceEncoding
      (Nat × ConditionalPublication.Payload P (L.Val secretTy))
      (Payload P L) where
  encode
    | (address, .opening handle value) =>
        .conditional address (.opening handle ⟨secretTy, value⟩)
    | (address, .decline) => .conditional address .decline
    | (address, .expire) => .conditional address .expire
    | (address, .cleartext value) =>
        .conditional address (.cleartext ⟨secretTy, value⟩)
    | (address, .malformed) => .conditional address .malformed
  decode
    | .conditional address (.opening handle typed) =>
        (typed.as? secretTy).map fun value => (address, .opening handle value)
    | .conditional address .decline => some (address, .decline)
    | .conditional address .expire => some (address, .expire)
    | .conditional address (.cleartext typed) =>
        (typed.as? secretTy).map fun value => (address, .cleartext value)
    | .conditional address .malformed => some (address, .malformed)
    | _ => none
  decode_encode value := by
    rcases value with ⟨address, payload⟩
    cases payload <;> simp [TypedValue.as?]
  decode_sound wire value hdecode := by
    rcases value with ⟨address, payload⟩
    cases wire with
    | conditional actual raw =>
        cases raw with
        | opening handle typed =>
            simp only at hdecode
            rw [Option.map_eq_some_iff] at hdecode
            obtain ⟨decoded, htyped, heq⟩ := hdecode
            cases heq
            rw [typed.eq_mk_of_as?_eq_some secretTy decoded htyped]
        | decline => cases Option.some.inj hdecode; rfl
        | expire => cases Option.some.inj hdecode; rfl
        | cleartext typed =>
            simp only at hdecode
            rw [Option.map_eq_some_iff] at hdecode
            obtain ⟨decoded, htyped, heq⟩ := hdecode
            cases heq
            rw [typed.eq_mk_of_as?_eq_some secretTy decoded htyped]
        | malformed => cases Option.some.inj hdecode; rfl
    | _ => cases hdecode

end ApplicationImage

namespace ConditionalPublicationSite

variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- Encoding a source choice through the disposition-selected controller
transport produces the proof-side request used by source coupling. -/
theorem choiceEncodingFor_encode
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat)
    (disposition : BindingDisposition (CommitmentHandle P Nat)
      (L.Val site.specification.secretTy))
    (chosen : L.Val site.choice.ty) :
    (site.choiceEncodingFor fresh state sourceSlot deadline disposition
      (ApplicationImage.conditionalTransport site.specification.secretTy)).encode chosen =
      .conditional (site.runtimeSite fresh state sourceSlot deadline).publicationNode
        (site.sourceRequestPayload fresh state sourceSlot deadline disposition
          (site.specification.encoding chosen)) := by
  cases disposition <;> cases hresult : site.specification.encoding chosen <;>
    simp [choiceEncodingFor, ChoiceEncoding.trans, ChoiceEncoding.reindex,
      ChoiceEncoding.atEndpoint, ConditionalPublication.addressedChoiceEncoding,
      ConditionalPublication.choiceEncoding, ConditionalPublication.addressedDefaultChoiceEncoding,
      ConditionalPublication.defaultChoiceEncoding, ConditionalPublication.requestPayload,
      ApplicationImage.conditionalTransport, sourceRequestPayload, ConditionalCode.requestPayload,
      code, hresult]

/-- For a fixed accepted disposition, the canonical conditional request
payload uniquely determines its optional source result. -/
theorem sourceRequestPayload_injective
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat)
    (disposition : BindingDisposition (CommitmentHandle P Nat)
      (L.Val site.specification.secretTy)) :
    Function.Injective
      (site.sourceRequestPayload fresh state sourceSlot deadline disposition) := by
  intro left right heq
  have value_eq_of_typed {left right : L.Val site.specification.secretTy}
      (h : (⟨site.specification.secretTy, left⟩ : TypedValue L) =
        ⟨site.specification.secretTy, right⟩) : left = right := by
    injection h
  cases disposition <;> cases left <;> cases right <;>
    unfold sourceRequestPayload ConditionalCode.requestPayload at heq <;>
      injection heq
  all_goals try rfl
  all_goals
    apply congrArg some
    apply value_eq_of_typed
    assumption

/-- Install a conditional source decision with the payload, accepted-binding,
and completion projections used by the generated image handler. -/
def imageController (site : ConditionalPublicationSite prog)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (sourceSlot deadline : Nat) (image : ApplicationImage P L)
    (disposition : BindingDisposition (CommitmentHandle P Nat)
      (L.Val site.specification.secretTy))
    (readout? : List image.application.PlayerEntry → image.application.View →
      Option (site.ChoiceReads fresh state))
    (sourcePolicy :
      (visible : Env L.Val
        (eraseVCtx (viewVCtx site.choice.owner site.choice.context))) →
        FinDist { value : L.Val site.choice.ty //
          evalGuard site.choice.guard value visible = true })
    (retry : List image.application.PlayerEntry → image.application.View → Bool) :=
  site.controllerFor fresh state sourceSlot deadline disposition image.application
    (ApplicationImage.conditionalTransport site.specification.secretTy)
    (fun view => view.application.done) readout? sourcePolicy retry

/-- The executable policy selects one strict static controller from the typed
accepted disposition visible in application memory. -/
def imagePolicy (site : ConditionalPublicationSite prog)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (sourceSlot deadline : Nat) (image : ApplicationImage P L)
    (readout? : List image.application.PlayerEntry → image.application.View →
      Option (site.ChoiceReads fresh state))
    (sourcePolicy :
      (visible : Env L.Val
        (eraseVCtx (viewVCtx site.choice.owner site.choice.context))) →
        FinDist { value : L.Val site.choice.ty //
          evalGuard site.choice.guard value visible = true })
    (retry : List image.application.PlayerEntry → image.application.View → Bool) :
    image.application.PlayerPolicy := fun history view =>
  let code := site.code fresh state sourceSlot deadline
  match code.binding? view.application with
  | none => FinDist.pure .wait
  | some disposition =>
      (site.imageController fresh state sourceSlot deadline image disposition
        readout? sourcePolicy retry).policy image.application history view

/-- A first uncached, ready image-controller invocation has exactly the source
decision law and emits the canonical dynamically typed conditional payload. -/
theorem imagePolicy_first_submission_source_law
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat)
    (image : ApplicationImage P L)
    (disposition : BindingDisposition (CommitmentHandle P Nat)
      (L.Val site.specification.secretTy))
    (readout? : List image.application.PlayerEntry → image.application.View →
      Option (site.ChoiceReads fresh state))
    (sourcePolicy :
      (visible : Env L.Val
        (eraseVCtx (viewVCtx site.choice.owner site.choice.context))) →
        FinDist { value : L.Val site.choice.ty //
          evalGuard site.choice.guard value visible = true })
    (retry : List image.application.PlayerEntry → image.application.View → Bool)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (representedStore : Store L) (env : VEnv L site.choice.context)
    (reads : site.ChoiceReads fresh state)
    (hbinding : (site.code fresh state sourceSlot deadline).binding? view.application =
      some disposition)
    (hresolved : view.application.done
      (site.runtimeSite fresh state sourceSlot deadline).publicationNode = false)
    (hcache :
      ((site.choiceEncodingFor fresh state sourceSlot deadline disposition
        (ApplicationImage.conditionalTransport site.specification.secretTy)).submission
          image.application).cachedValue image.application history = none)
    (hready : (site.runtimeSite fresh state sourceSlot deadline).readyDisposition
      (some disposition) view.application.done = true)
    (hreadout : readout? history view = some reads)
    (hagrees : (site.choice.siteState fresh state).ViewAgrees
      site.choice.owner representedStore env)
    (hreads : ReadEnv.ofStore? representedStore
      (site.choice.compiledGuard fresh state).choiceReads = some reads) :
    site.imagePolicy fresh state sourceSlot deadline image readout? sourcePolicy retry
      history view =
      (sourcePolicy ((env.toView site.choice.owner).eraseEnv)).map fun choice =>
        .submit ((site.choiceEncodingFor fresh state sourceSlot deadline disposition
          (ApplicationImage.conditionalTransport site.specification.secretTy)).encode
            choice.1) := by
  let controller := site.imageController fresh state sourceSlot deadline image disposition
    readout? sourcePolicy retry
  simp only [imagePolicy, hbinding]
  calc
    controller.policy image.application history view =
        (controller.kernel reads).map controller.codec.encode :=
      controller.policy_of_uncached_ready image.application history view reads
        hresolved hcache hready hreadout
    _ = (sourcePolicy ((env.toView site.choice.owner).eraseEnv)).map fun choice =>
        .submit ((site.choiceEncodingFor fresh state sourceSlot deadline disposition
          (ApplicationImage.conditionalTransport site.specification.secretTy)).encode
            choice.1) := by
      have hlaw := compileSourceDecision_law
        (site.choice.siteState fresh state) site.choice.owner
        site.choice.guard sourcePolicy representedStore env hagrees reads hreads
      have hmapped := congrArg
        (FinDist.map (fun value : L.Val site.choice.ty =>
          (MessageInterface.PlayerCommand.submit
            ((site.choiceEncodingFor fresh state sourceSlot deadline disposition
              (ApplicationImage.conditionalTransport site.specification.secretTy)).encode value) :
                image.application.PlayerCommand)))
        hlaw
      simpa only [controller, imageController, controllerFor,
        ChoiceEncoding.submission, FinDist.map_comp, Function.comp_def] using hmapped

end ConditionalPublicationSite

end Vegas
