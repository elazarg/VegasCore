/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceResolution
import Vegas.Compile.WindowedApplicationDeadline

/-! # Source coupling for actual windowed public-choice resolution -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- An accepted ordinary typed choice at a generated windowed endpoint gives
the corresponding legal source successor. The public-validation certificate
is the compiler-side bridge between native guard reads and the source view. -/
theorem handle_publicChoice_source_coupling
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
    (state resolved : WindowedApplication.State P L)
    (activation : Activation Nat) (id : MessageId P) (address : Nat)
    (value : L.Val ty) (timeout : Option (PublicFallbackCode L ty))
    (hactive : state.active = some activation)
    (hcode : runtime.image.lookup address = some (.publicChoice
      { (PublicChoiceSite.atHead name publicName who guard tail).code fresh build with
        timeout := timeout }))
    (hrefines : state.base.Refines current.current.graph.1)
    (hhandle : runtime.handle state ⟨id, .choice address ⟨ty, value⟩⟩ = some resolved) :
    evalGuard guard value ((current.current.source.toView who).eraseEnv) = true ∧
      ∃ next : CoupledAt
          (compileCore (.commit name who guard (.reveal publicName who name .here tail))
            fresh build).graph
          (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
            publicName who .here fresh.2.1).1,
        next.current.source = (current.current.source.cons value).cons value ∧
          resolved.base.Refines next.current.graph.1 := by
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let timed : PublicChoiceCode P L := { site.code fresh build with timeout := timeout }
  obtain ⟨origin, base, horigin, _, hordered, hresolved⟩ :=
    runtime.handle_some state resolved ⟨id, .choice address ⟨ty, value⟩⟩ hhandle
  have horiginEq : origin = activation := by
    rw [hactive] at horigin
    exact Option.some.inj horigin.symm
  subst origin
  have hunderlying : (runtime.atOrigin activation.since).handle state.base
      ⟨id, .choice address ⟨ty, value⟩⟩ = some base :=
    (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment state.base base
      ⟨id, .choice address ⟨ty, value⟩⟩ hordered
  let retimed : PublicChoiceCode P L := { site.code fresh build with
    timeout := timeout.map fun fallback =>
      { fallback with deadline := activation.since +
          runtime.windowOf (site.code fresh build).endpoint.publicationNode } }
  have hlookup : (runtime.atOrigin activation.since).lookup address =
      some (.publicChoice retimed) := by
    rw [atOrigin, ApplicationImage.lookup_withDeadlines, hcode]
    rfl
  change (runtime.atOrigin activation.since).handle state.base
      ⟨id, .choice address ⟨retimed.guard.ty, value⟩⟩ = some base at hunderlying
  rw [(runtime.atOrigin activation.since).handle_choice state.base address retimed hlookup
    id value] at hunderlying
  cases hresolve : retimed.endpoint.resolve? state.base.memory.done
      (retimed.guard.validate state.base.memory.store) ⟨id, value⟩ with
  | none => simp [hresolve] at hunderlying
  | some accepted =>
      have haccepted := (PublicChoice.resolve_iff _ _ _ _ _).mp hresolve
      have hvalue : accepted = value := haccepted.2.2.2.symm
      subst accepted
      rw [hresolve] at hunderlying
      have hbase : base = state.base.publish retimed value := by
        exact Option.some.inj hunderlying.symm
      have hsender := haccepted.2.1
      change id.1 = who at hsender
      have hid : id = (who, id.2) := Prod.ext hsender rfl
      rw [hid] at hresolve
      have hsiteOwner : site.owner = who := rfl
      have hready := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
        state.base.memory.done hrefines.memory.completed
      have hcanonical : (site.code fresh build).endpoint.resolve?
          state.base.memory.done ((site.code fresh build).guard.validate
            state.base.memory.store) ⟨(site.owner, id.2), value⟩ = some value := by
        apply (PublicChoice.resolve_request _ _ _ _ _).mpr
        exact ⟨hready, by simpa [retimed, site] using haccepted.2.2.1⟩
      have hlegal : evalGuard guard value
          ((current.current.source.toView who).eraseEnv) = true := by
        apply (site.code_resolves_iff_source_legal fresh build
          current.current.graph.1.store state.base.memory.store current.current.source
          heligible current.current.agrees hrefines.memory.publicFields
          state.base.memory.done hready id.2 value).mp
        exact hcanonical
      obtain ⟨next, hsource, hgraph⟩ :=
        PublicChoiceSite.source_successor guard tail fresh build current value hlegal
      refine ⟨hlegal, next, hsource, ?_⟩
      rw [hresolved]
      change base.Refines next.current.graph.1
      rw [hbase]
      rw [hgraph]
      exact site.resolution_refines fresh build state.base current.current.graph.1 hrefines
        heligible ⟨(site.owner, id.2), value⟩ value hcanonical

/-- A successful permissionless expiry at the explicitly source-certified
fallback code supplies a legal adjacent source successor. Retiming changes
only the absolute deadline; the certified expression and validator remain. -/
theorem handle_expireChoice_source_coupling
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName who guard tail).decision)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (state resolved : WindowedApplication.State P L)
    (activation : Activation Nat) (id : MessageId P) (address : Nat)
    (hactive : state.active = some activation)
    (hcode : runtime.image.lookup address = some (.publicChoice
      ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
        fallback fresh build deadline)))
    (hrefines : state.base.Refines current.current.graph.1)
    (hhandle : runtime.handle state ⟨id, .expireChoice address⟩ = some resolved) :
    ∃ value : L.Val ty,
      value = L.eval fallback.expr current.current.source.erasePubEnv ∧
      evalGuard guard value ((current.current.source.toView who).eraseEnv) = true ∧
      ∃ next : CoupledAt
          (compileCore (.commit name who guard (.reveal publicName who name .here tail))
            fresh build).graph
          (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
            publicName who .here fresh.2.1).1,
        next.current.source = (current.current.source.cons value).cons value ∧
          resolved.base.Refines next.current.graph.1 := by
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let timed := site.timeoutCode fallback fresh build deadline
  obtain ⟨origin, base, horigin, _, hordered, hresolved⟩ :=
    runtime.handle_some state resolved ⟨id, .expireChoice address⟩ hhandle
  have horiginEq : origin = activation := by
    rw [hactive] at horigin
    exact Option.some.inj horigin.symm
  subst origin
  have hunderlying : (runtime.atOrigin activation.since).handle state.base
      ⟨id, .expireChoice address⟩ = some base :=
    (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment state.base base
      ⟨id, .expireChoice address⟩ hordered
  let retimed : PublicChoiceCode P L := { site.code fresh build with
    timeout := some (PublicFallbackCode.mk
      (activation.since + runtime.windowOf (site.code fresh build).endpoint.publicationNode)
      (fallback.compiled fresh build)) }
  have hlookup : (runtime.atOrigin activation.since).lookup address =
      some (.publicChoice retimed) := by
    rw [atOrigin, ApplicationImage.lookup_withDeadlines, hcode]
    rfl
  rw [(runtime.atOrigin activation.since).handle_expireChoice state.base address retimed
    hlookup id] at hunderlying
  obtain ⟨value, htimeout, hbase⟩ := Option.map_eq_some_iff.mp hunderlying
  have hcompiled := fallback.compiled_evalStore?_eq_source fresh build
    current.current.graph.1.store state.base.memory.store current.current.source
    current.current.agrees (fun ref href =>
      hrefines.memory.publicFields ref (fallback.compiled_reads_public fresh build ref href))
  obtain ⟨reads, hreads, heval⟩ := Option.map_eq_some_iff.mp hcompiled
  have hvalueEq : value = L.eval fallback.expr current.current.source.erasePubEnv := by
    unfold PublicChoiceCode.resolveTimeout? at htimeout
    simp only [retimed, Option.bind_eq_bind, Option.bind_some] at htimeout
    split at htimeout
    · rw [hreads] at htimeout
      simp only [Option.bind_some] at htimeout
      split at htimeout
      · exact (Option.some.inj htimeout).symm.trans heval
      · contradiction
    · contradiction
  have hvalid := retimed.resolveTimeout?_some state.base.memory value htimeout
  have hcanonical : (site.code fresh build).endpoint.resolve? state.base.memory.done
      ((site.code fresh build).guard.validate state.base.memory.store)
      ⟨(site.owner, 0), value⟩ = some value := by
    apply (PublicChoice.resolve_request _ _ _ _ _).mpr
    simpa [retimed, site] using hvalid
  have hlegal : evalGuard guard value
      ((current.current.source.toView who).eraseEnv) = true := by
    apply (site.code_resolves_iff_source_legal fresh build current.current.graph.1.store
      state.base.memory.store current.current.source heligible current.current.agrees
      hrefines.memory.publicFields state.base.memory.done hvalid.1 0 value).mp
    exact hcanonical
  obtain ⟨next, hsource, hgraph⟩ :=
    PublicChoiceSite.source_successor guard tail fresh build current value hlegal
  refine ⟨value, hvalueEq, hlegal, next, hsource, ?_⟩
  rw [hresolved]
  change base.Refines next.current.graph.1
  rw [← hbase, hgraph]
  exact site.resolution_refines fresh build state.base current.current.graph.1 hrefines
    heligible ⟨(site.owner, 0), value⟩ value hcanonical

/-- Every successful message at the active certified public-choice endpoint
is either an accepted typed choice or its permissionless certified expiry;
both branches supply the same shape of legal source successor. -/
theorem handle_publicChoice_or_expiry_source_coupling
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName who guard tail).decision)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (state resolved : WindowedApplication.State P L) (activation : Activation Nat)
    (address : Nat) (message : Message P (ApplicationImage.Payload P L))
    (hactive : state.active = some activation) (hkey : activation.key = address)
    (hcode : runtime.image.lookup address = some (.publicChoice
      ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
        fallback fresh build deadline)))
    (hrefines : state.base.Refines current.current.graph.1)
    (hhandle : runtime.handle state message = some resolved) :
    ∃ (value : L.Val ty)
      (next : CoupledAt
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1),
      evalGuard guard value ((current.current.source.toView who).eraseEnv) = true ∧
        next.current.source = (current.current.source.cons value).cons value ∧
        resolved.base.Refines next.current.graph.1 := by
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let timed := site.timeoutCode fallback fresh build deadline
  obtain ⟨origin, base, horigin, hcurrent, hordered, _⟩ :=
    runtime.handle_some state resolved message hhandle
  have horiginEq : origin = activation := by
    rw [hactive] at horigin
    exact Option.some.inj horigin.symm
  subst origin
  have hunderlying : (runtime.atOrigin activation.since).handle state.base message =
      some base :=
    (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment state.base base message hordered
  let retimed : PublicChoiceCode P L := { site.code fresh build with
    timeout := some (PublicFallbackCode.mk
      (activation.since + runtime.windowOf
        (site.code fresh build).endpoint.publicationNode)
      (fallback.compiled fresh build)) }
  have hlookup : (runtime.atOrigin activation.since).lookup address =
      some (.publicChoice retimed) := by
    rw [atOrigin, ApplicationImage.lookup_withDeadlines, hcode]
    rfl
  have hactiveAt : (runtime.atOrigin activation.since).activeAddress? state.base.memory =
      some address := by
    rw [hkey] at hcurrent
    simpa [atOrigin, ApplicationImage.activeAddress?, ApplicationImage.withDeadlines] using hcurrent
  have hadmitted : ∀ submittedAddress,
      message.payload.address? = some submittedAddress → submittedAddress = address := by
    intro submittedAddress hsubmitted
    by_contra hne
    have hrejected := (runtime.atOrigin activation.since).ordered_handle_reject state.base
      message submittedAddress hsubmitted (by
        rw [hactiveAt]
        exact fun heq => hne (Option.some.inj heq.symm))
    rw [hrejected] at hordered
    contradiction
  rcases message with ⟨id, payload⟩
  cases payload with
  | choice submittedAddress typed =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      rcases typed with ⟨actualTy, raw⟩
      by_cases hty : actualTy = ty
      · subst actualTy
        obtain ⟨hlegal, next, hsource, hnext⟩ :=
          runtime.handle_publicChoice_source_coupling guard tail fresh build current heligible
            state resolved activation id address raw (some
              ((PublicChoiceSite.atHead name publicName who guard tail).timeout
                fallback fresh build deadline)) hactive hcode hrefines hhandle
        exact ⟨raw, next, hlegal, hsource, hnext⟩
      · have hguardTy : retimed.guard.ty = ty := rfl
        have hne : actualTy ≠ retimed.guard.ty := fun heq => hty (heq.trans hguardTy)
        have has : (⟨actualTy, raw⟩ : TypedValue L).as? retimed.guard.ty = none := by
          simp [TypedValue.as?, hne]
        simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
          Option.bind_some] at hunderlying
        rw [has] at hunderlying
        contradiction
  | expireChoice submittedAddress =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      obtain ⟨value, _, hlegal, next, hsource, hnext⟩ :=
        runtime.handle_expireChoice_source_coupling guard tail fallback fresh build deadline
          current heligible state resolved activation id address hactive hcode hrefines hhandle
      exact ⟨value, next, hlegal, hsource, hnext⟩
  | malformed data =>
      simp [ApplicationImage.handle] at hunderlying
  | binding submittedAddress handle =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying
  | expireBinding submittedAddress =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying
  | conditional submittedAddress payload =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_publicChoice_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_publicChoice_source_coupling

/-- info: 'Vegas.WindowedApplication.handle_expireChoice_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_expireChoice_source_coupling

/-- info: 'Vegas.WindowedApplication.handle_publicChoice_or_expiry_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_publicChoice_or_expiry_source_coupling
