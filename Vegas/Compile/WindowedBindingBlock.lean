/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingSettlement
import Vegas.Compile.ApplicationGuardSoundness
import Vegas.Compile.WindowedApplicationDeadline

/-! # Source coupling for actual windowed binding resolution -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- An actually accepted ordinary binding at a ready source checkpoint chooses
its source value from the acceptance-time prepared snapshot. Missing or
ill-typed preparation chooses the supplied checkpoint-local fallback value.
The successful handler itself forces the authenticated canonical handle. -/
theorem handle_binding_source_coupling
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard)
    (state resolved : WindowedApplication.State P L)
    (activation : Activation Nat) (id : MessageId P)
    (address : Nat) (handle : CommitmentHandle P Nat)
    (timeout : Option (PublicFallbackCode L ty))
    (fallbackValue : L.Val ty)
    (hactive : state.active = some activation)
    (hcode : runtime.image.lookup address = some (.bind
      { ((.here guard tail : SourceDecisionSite who
        (.commit name who guard tail) Γ name ty guard).bindingCode fresh build
          ((.here guard tail : SourceDecisionSite who
            (.commit name who guard tail) Γ name ty guard).compiledField fresh build)) with
        timeout := timeout }))
    (hrefines : state.base.Refines current.current.graph.1)
    (hhandle : runtime.handle state ⟨id, .binding address handle⟩ = some resolved) :
    let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
      .here guard tail
    let chosen := ((state.base.prepared.lookup (who, site.compiledField fresh build)).bind
      (fun typed => typed.as? ty)).getD fallbackValue
    ∃ next : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1,
      next.current.source = current.current.source.cons chosen ∧
        resolved.base.Refines next.current.graph.1 := by
  dsimp only
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh build (site.compiledField fresh build)
  let timed : BindingCode P L := { code with timeout := timeout }
  obtain ⟨origin, base, horigin, _, hordered, hresolved⟩ :=
    runtime.handle_some state resolved ⟨id, .binding address handle⟩ hhandle
  have horiginEq : origin = activation := by
    rw [hactive] at horigin
    exact Option.some.inj horigin.symm
  subst origin
  have hunderlying : (runtime.atOrigin activation.since).handle state.base
      ⟨id, .binding address handle⟩ = some base :=
    (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment state.base base
      ⟨id, .binding address handle⟩ hordered
  let retimed : BindingCode P L := { timed with
    timeout := timed.timeout.map fun fallback =>
      { fallback with deadline := activation.since + runtime.windowOf timed.node } }
  have hlookup : (runtime.atOrigin activation.since).lookup address = some (.bind retimed) := by
    rw [atOrigin, ApplicationImage.lookup_withDeadlines, hcode]
    rfl
  rw [(runtime.atOrigin activation.since).handle_binding state.base address retimed hlookup
    id handle] at hunderlying
  split at hunderlying
  · rename_i haccept
    simp only [Option.some.injEq] at hunderlying
    obtain ⟨_, hcanonical, _, _, _⟩ := haccept
    change handle = (who, site.compiledField fresh build) at hcanonical
    obtain ⟨next, hsource, hnext⟩ :=
      SourceDecisionSite.bind_recoveredOr_source_coupling guard tail fresh build current
        state.base hrefines fallbackValue (fun value => unrestricted current.current.source value)
    refine ⟨next, hsource, ?_⟩
    rw [hresolved]
    change base.Refines next.current.graph.1
    rw [← hunderlying]
    simpa [hcanonical, ApplicationImage.State.bind, retimed, timed, code, site] using hnext
  · simp at hunderlying

/-- Before the active response window ends, every successful native handler at
a generated binding instruction is necessarily the authenticated ordinary
binding payload for that instruction. Expiry is not yet due, and every other
payload constructor conflicts with the active binding lookup. -/
theorem handle_before_window_binding_source_coupling
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard)
    (state resolved : WindowedApplication.State P L)
    (activation : Activation Nat) (address deadline : Nat)
    (message : Message P (ApplicationImage.Payload P L))
    (hactive : state.active = some activation)
    (hkey : activation.key = address)
    (hclock : state.base.memory.clock ≤ activation.since + runtime.windowOf address)
    (hcode : runtime.image.lookup address = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : state.base.Refines current.current.graph.1)
    (hhandle : runtime.handle state message = some resolved) :
    ∃ id,
      message = ⟨id, .binding address (who,
        (.here guard tail : SourceDecisionSite who
          (.commit name who guard tail) Γ name ty guard).compiledField fresh build)⟩ ∧
      let chosen := ((state.base.prepared.lookup (who,
        (.here guard tail : SourceDecisionSite who
          (.commit name who guard tail) Γ name ty guard).compiledField fresh build)).bind
            (fun typed => typed.as? ty)).getD
              (L.eval fallback.expr current.current.source.erasePubEnv)
      ∃ next : CoupledAt
          (compileCore (.commit name who guard tail) fresh build).graph
          (build.addCommitEvent name who guard fresh.1).1,
        next.current.source = current.current.source.cons chosen ∧
          resolved.base.Refines next.current.graph.1 := by
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let timed := fallback.bindingTimeoutCode fresh build deadline
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
  let retimed : BindingCode P L := { timed with
    timeout := timed.timeout.map fun timeout =>
      { timeout with deadline := activation.since + runtime.windowOf timed.node } }
  have hlookup : (runtime.atOrigin activation.since).lookup address = some (.bind retimed) := by
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
  | binding submittedAddress handle =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      rw [(runtime.atOrigin activation.since).handle_binding state.base address retimed
        hlookup id handle] at hunderlying
      split at hunderlying
      · rename_i haccept
        obtain ⟨_, hcanonical, _, _, _⟩ := haccept
        change handle = (who, site.compiledField fresh build) at hcanonical
        subst handle
        refine ⟨id, rfl, ?_⟩
        exact runtime.handle_binding_source_coupling guard tail fresh build current
          unrestricted state resolved activation id address
          (who, site.compiledField fresh build) (some ⟨deadline,
            fallback.compiled fresh build⟩)
          (L.eval fallback.expr current.current.source.erasePubEnv) hactive hcode
          hrefines hhandle
      · simp at hunderlying
  | expireBinding submittedAddress =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      have hrejected := runtime.handle_expireBinding_before_window state activation hactive
        address id hclock
      rw [hrejected] at hhandle
      contradiction
  | malformed data =>
      have hrejected := (runtime.atOrigin activation.since).ordered_handle_malformed
        state.base id data
      rw [hrejected] at hordered
      contradiction
  | choice submittedAddress value =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying
  | expireChoice submittedAddress =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying
  | conditional submittedAddress opening =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_binding_source_coupling

/-- info: 'Vegas.WindowedApplication.handle_before_window_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_before_window_binding_source_coupling
