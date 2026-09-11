/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingSettlement
import Vegas.Compile.ApplicationGuardSoundness
import Vegas.Compile.WindowedApplicationDeadline
import Vegas.Compile.WindowedActivationFreshness
import Vegas.Compile.WindowedBlockSourceCoupling

/-! # Source coupling for actual windowed binding resolution -/

noncomputable section

namespace Vegas.BindingCode

open Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Canonical extraction of a source value from a completed binding disposition.
The caller supplies the expected source type. Opaque bindings use their frozen
typed verifier when recoverable; absent or ill-typed verifiers select the
source-certified fallback. Public defaults use their recorded typed value,
with the same fallback for invalid runtime state. -/
def resolvedValue (code : BindingCode P L) {ty : L.Ty} (fallback : L.Val ty)
    (state : ApplicationImage.State P L) : L.Val ty :=
  match state.memory.accepted code.sourceField with
  | some (.opaque _) =>
      ((state.frozen code.sourceField).bind (fun typed => typed.as? ty)).getD fallback
  | some (.publicDefault typed) => (typed.as? ty).getD fallback
  | none => fallback

end Vegas.BindingCode

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

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
        resolved.base.Refines next.current.graph.1 ∧
        chosen = (site.bindingCode fresh build (site.compiledField fresh build)).resolvedValue
          fallbackValue resolved.base := by
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
    subst handle
    obtain ⟨next, hsource, hnext⟩ :=
      SourceDecisionSite.bind_recoveredOr_source_coupling guard tail fresh build current
        state.base hrefines fallbackValue (fun value => unrestricted current.current.source value)
    refine ⟨next, hsource, ?_, ?_⟩
    · rw [hresolved]
      change base.Refines next.current.graph.1
      rw [← hunderlying]
      simpa [ApplicationImage.State.bind, retimed, timed, code, site] using hnext
    · rw [hresolved]
      change ((state.base.prepared.lookup (who, site.compiledField fresh build)).bind
          (fun typed => typed.as? ty)).getD fallbackValue =
        code.resolvedValue fallbackValue base
      rw [← hunderlying]
      simp only [BindingCode.resolvedValue, ApplicationImage.State.bind]
      have hfield : code.sourceField = retimed.sourceField := rfl
      rw [if_pos hfield, if_pos hfield]
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
          resolved.base.Refines next.current.graph.1 ∧
          chosen = (fallback.bindingTimeoutCode fresh build deadline).resolvedValue
            (L.eval fallback.expr current.current.source.erasePubEnv) resolved.base := by
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

/-- Every successful message at an active generated binding instruction has a
source successor. Ordinary binding uses the acceptance-time snapshot (or the
fixed local fallback when unrecoverable); an accepted expiry uses the emitted
public fallback. This theorem needs no pre-window clock premise. -/
theorem handle_binding_or_expiry_source_coupling
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
    (hcode : runtime.image.lookup address = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : state.base.Refines current.current.graph.1)
    (hhandle : runtime.handle state message = some resolved) :
    ∃ (chosen : L.Val ty)
      (next : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1),
      next.current.source = current.current.source.cons chosen ∧
      resolved.base.Refines next.current.graph.1 ∧ resolved.FreshActivation ∧
      chosen = (fallback.bindingTimeoutCode fresh build deadline).resolvedValue
        (L.eval fallback.expr current.current.source.erasePubEnv) resolved.base := by
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let timed := fallback.bindingTimeoutCode fresh build deadline
  obtain ⟨origin, base, horigin, hcurrent, hordered, hresolved⟩ :=
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
      obtain ⟨next, hsource, hnext, hchosen⟩ :=
        runtime.handle_binding_source_coupling guard tail fresh build current unrestricted
          state resolved activation id address handle (some ⟨deadline,
            fallback.compiled fresh build⟩)
          (L.eval fallback.expr current.current.source.erasePubEnv) hactive hcode
          hrefines hhandle
      exact ⟨_, next, hsource, hnext, runtime.handle_freshActivation state resolved _ hhandle,
        hchosen⟩
  | expireBinding submittedAddress =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      rw [(runtime.atOrigin activation.since).handle_expireBinding state.base address retimed
        hlookup id] at hunderlying
      change (retimed.resolveTimeout? state.base.memory).map
        (fun value => state.base.defaultBind retimed ⟨retimed.ty, value⟩) =
          some (base : ApplicationImage.State P L) at hunderlying
      obtain ⟨value, hvalue, hbase⟩ := Option.map_eq_some_iff.mp hunderlying
      obtain ⟨_, _, _, timeout, htimeout, _, heval⟩ :=
        retimed.resolveTimeout?_some state.base.memory value hvalue
      have htimeout' : timeout = {
          deadline := activation.since + runtime.windowOf timed.node
          value := fallback.compiled fresh build } := by
        have := Option.some.inj htimeout.symm
        simpa [retimed, timed,
          SourceDecisionSite.PublicFallback.bindingTimeoutCode] using this
      subst timeout
      change L.Val ty at value
      change (fallback.compiled fresh build).evalStore? state.base.memory.store =
        some value at heval
      obtain ⟨hexpected, next, hsource, hnext⟩ :=
        fallback.defaultBind_source_coupling guard tail fresh build current state.base hrefines
      have hvalueEq : value = L.eval fallback.expr current.current.source.erasePubEnv := by
        rw [hexpected] at heval
        exact Option.some.inj heval.symm
      subst value
      refine ⟨_, next, hsource, ?_, runtime.handle_freshActivation state resolved _ hhandle, ?_⟩
      · rw [hresolved]
        change base.Refines next.current.graph.1
        rw [← hbase]
        have hdefault : state.base.defaultBind retimed
            ⟨retimed.ty, L.eval fallback.expr current.current.source.erasePubEnv⟩ =
            state.base.defaultBind (site.bindingCode fresh build
              (site.compiledField fresh build))
              ⟨ty, L.eval fallback.expr current.current.source.erasePubEnv⟩ := by
          rfl
        rw [hdefault]
        exact hnext
      · rw [hresolved]
        change L.eval fallback.expr current.current.source.erasePubEnv =
          timed.resolvedValue (L.eval fallback.expr current.current.source.erasePubEnv) base
        rw [← hbase]
        simp [BindingCode.resolvedValue, ApplicationImage.State.defaultBind, TypedValue.as?,
          retimed, timed]
        have hty : (fallback.bindingTimeoutCode fresh build deadline).ty = ty := rfl
        simp [hty]
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

/-- Resolving an active binding through an actual latest-submission environment
step carries the accepted message to its source successor. -/
theorem environment_latest_binding_source_coupling
    (runtime : WindowedApplication P L) (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (actor : P)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard) (deadline : Nat)
    (execution next : runtime.application.PolicyExecution)
    (activation : Activation Nat)
    (hpolicy : environment execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native) =
        FinDist.pure (runtime.liftEnvironmentCommand
          (runtime.image.application.latestSubmissionCommand actor
            (runtime.eraseEnvironmentView
              (MessageApplication.State.environmentView runtime.application execution.native)))))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = (fallback.bindingTimeoutCode fresh build deadline).node)
    (hcode : runtime.image.lookup (fallback.bindingTimeoutCode fresh build deadline).node =
      some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? next.native.application.base.memory ≠
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hnext : next ∈ (runtime.application.invoke players environment execution
      .environment).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      next.native.application.base.Refines sourceNext.current.graph.1 ∧
      next.native.application.FreshActivation ∧
      chosen = (fallback.bindingTimeoutCode fresh build deadline).resolvedValue
        (L.eval fallback.expr current.current.source.erasePubEnv)
        next.native.application.base := by
  let timed := fallback.bindingTimeoutCode fresh build deadline
  let Witness := { pair :
    L.Val ty × CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph
      (build.addCommitEvent name who guard fresh.1).1 //
    pair.2.current.source = current.current.source.cons pair.1 }
  let target : Witness → Config
      (compileCore (.commit name who guard tail) fresh build).graph :=
    fun witness => witness.1.2.current.graph.1
  let Certificate : WindowedApplication.State P L → Witness → Prop :=
    fun result witness => witness.1.1 = timed.resolvedValue
      (L.eval fallback.expr current.current.source.erasePubEnv) result.base
  obtain ⟨witness, hnextRefines, hnextFresh, hcertificate⟩ :=
    runtime.environment_latest_source_witness players environment actor execution next timed.node
      Witness target Certificate hpolicy hactive hinactive (by
        intro message resolved hhandle
        obtain ⟨chosen, sourceNext, hsource, hresolved, hfresh, hchosen⟩ :=
          runtime.handle_binding_or_expiry_source_coupling guard tail fallback fresh build
            current unrestricted execution.native.application resolved activation timed.node
            deadline message hactivation hkey hcode hrefines hhandle
        exact ⟨⟨(chosen, sourceNext), hsource⟩, hresolved, hfresh, hchosen⟩) hnext
  exact ⟨witness.1.1, witness.1.2, witness.2, hnextRefines, hnextFresh, hcertificate⟩

/-- If the ordinary environment slot of an active binding block resolves the
instruction, the actual included pending message supplies a source successor.
Waiting, a missing identifier, and a rejected handler all preserve the active
address and therefore cannot inhabit this branch. -/
theorem blockEnvironment_normal_binding_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard) (deadline : Nat)
    (execution next : runtime.application.PolicyExecution)
    (activation : Activation Nat)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some (.bind
        (fallback.bindingTimeoutCode fresh build deadline)))
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 0)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = (fallback.bindingTimeoutCode fresh build deadline).node)
    (hcode : runtime.image.lookup (fallback.bindingTimeoutCode fresh build deadline).node =
      some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? next.native.application.base.memory ≠
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hnext : next ∈ (runtime.application.invoke players
      (runtime.blockEnvironment roster) execution .environment).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      next.native.application.base.Refines sourceNext.current.graph.1 ∧
      next.native.application.FreshActivation ∧
      chosen = (fallback.bindingTimeoutCode fresh build deadline).resolvedValue
        (L.eval fallback.expr current.current.source.erasePubEnv)
        next.native.application.base := by
  let timed := fallback.bindingTimeoutCode fresh build deadline
  apply runtime.environment_latest_binding_source_coupling players
    (runtime.blockEnvironment roster) timed.owner guard tail fallback fresh build current
    unrestricted deadline execution next activation
  · exact runtime.blockEnvironment_normal roster execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native)
      (.bind timed) hindex hactive hslot |>.trans (by
        simp [ApplicationImage.serviceCommand])
  · exact hactive
  · exact hactivation
  · exact hkey
  · exact hcode
  · exact hrefines
  · exact hinactive
  · exact hnext

/-- The reserved relay environment slot has the same source-coupling law even
when the relay player's preceding command is unrestricted. -/
theorem blockEnvironment_relay_binding_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy) (actor : P) (rosterIndex : Nat)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard) (deadline : Nat)
    (execution next : runtime.application.PolicyExecution) (activation : Activation Nat)
    (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length % (roster.length + 2) = rosterIndex + 2)
    (hwho : roster[rosterIndex]? = some actor)
    (hinstruction : instruction = .bind (fallback.bindingTimeoutCode fresh build deadline))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = (fallback.bindingTimeoutCode fresh build deadline).node)
    (hcode : runtime.image.lookup (fallback.bindingTimeoutCode fresh build deadline).node =
      some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? next.native.application.base.memory ≠
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hnext : next ∈ (runtime.application.invoke players
      (runtime.blockEnvironment roster) execution .environment).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      next.native.application.base.Refines sourceNext.current.graph.1 ∧
      next.native.application.FreshActivation ∧
      chosen = (fallback.bindingTimeoutCode fresh build deadline).resolvedValue
        (L.eval fallback.expr current.current.source.erasePubEnv)
        next.native.application.base := by
  apply runtime.environment_latest_binding_source_coupling players
    (runtime.blockEnvironment roster) actor guard tail fallback fresh build current unrestricted
    deadline execution next activation
  · have hpolicy := runtime.blockEnvironment_relay roster execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native)
      instruction rosterIndex actor hindex (by
        rw [hinstruction]
        change runtime.image.activeAddress? execution.native.application.base.memory =
          some (fallback.bindingTimeoutCode fresh build deadline).node
        exact hactive) hslot hwho
    refine hpolicy.trans (congrArg FinDist.pure ?_)
    simp only [MessageApplication.latestSubmissionCommand, eraseEnvironmentView,
      MessageApplication.State.environmentView, WindowedApplication.application]
    cases hserial : execution.native.pool.nextSerial actor with
    | zero => rfl
    | succ serial =>
        simp only [liftEnvironmentCommand]
        split <;> rfl
  · exact hactive
  · exact hactivation
  · exact hkey
  · exact hcode
  · exact hrefines
  · exact hinactive
  · exact hnext

/-- A canonical relay reached through an actual clock-and-relay prefix carries
the concrete public fallback source successor through its complete relay pair.
Unlike the settlement-only theorem, this retains the witness supplied by the
accepted expiry handler. -/
theorem binding_relay_source_coupling_after_clock
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy) (relay sourceOwner : P)
    (base : runtime.application.PlayerPolicy)
    (hrelay : players relay = runtime.blockPlayer relay base)
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx sourceOwner Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed sourceOwner ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name sourceOwner guard tail))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name sourceOwner guard tail) fresh build).graph build)
    (instruction : ApplicationInstruction P L) (activation : Activation Nat)
    (execution middle after : runtime.application.PolicyExecution)
    (priorRelays : List (@Invocation P)) (rosterIndex : Nat)
    (hwho : roster[rosterIndex]? = some relay)
    (howner : instruction.submitter = some sourceOwner)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        (Invocation.environment :: priorRelays).countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 1)
    (hactive : runtime.image.activeAddress?
      execution.native.application.base.memory = some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hcode : runtime.image.lookup activation.key = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hconsistent : runtime.Consistent execution.native.application)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (hmiddleActive : runtime.image.activeAddress?
      middle.native.application.base.memory = some instruction.address)
    (hmiddle : middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (.environment :: priorRelays) execution).support)
    (hplayerIndex : runtime.image.instructions[(middle.principalHistory relay).length / 3]? =
      some instruction)
    (hplayerSlot : (middle.principalHistory relay).length % 3 = 2)
    (henvironmentIndex : runtime.image.instructions[middle.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (henvironmentSlot : middle.environmentHistory.length % (roster.length + 2) =
      rosterIndex + 2)
    (hafter : after ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) [.player relay, .environment] middle).support) :
    ∃ (chosen : L.Val ty)
      (next : CoupledAt
        (compileCore (.commit name sourceOwner guard tail) fresh build).graph
        (build.addCommitEvent name sourceOwner guard fresh.1).1),
      next.current.source = current.current.source.cons chosen ∧
      after.native.application.base.Refines next.current.graph.1 ∧
      after.native.application.FreshActivation ∧
      runtime.image.activeAddress? after.native.application.base.memory ≠
        some instruction.address := by
  obtain ⟨payload, resolved, hdue, hfresh, hhandle, next, hsource, hresolved⟩ :=
    runtime.binding_source_relay_eligibility_after_clock roster players guard tail fallback fresh
      build deadline current instruction activation execution middle priorRelays relay howner hindex
      hslot hactive hactivation hkey hcode hrefines hconsistent hserials hmiddleActive hmiddle
  have hlaw := runtime.block_relay_resolves_active roster players relay base hrelay middle
    instruction rosterIndex hplayerIndex hplayerSlot henvironmentIndex henvironmentSlot hwho
    hmiddleActive payload resolved hdue hfresh hhandle
  have happlication : after.native.application = resolved := by
    have hmem : after.native.application ∈
        ((runtime.application.runPolicies players (runtime.blockEnvironment roster)
          [.player relay, .environment] middle).map
            (fun result => result.native.application)).support := by
      rw [FinDist.support_map]
      exact ⟨after, hafter, rfl⟩
    rw [hlaw.1, FinDist.mem_support_pure] at hmem
    exact hmem
  refine ⟨_, next, hsource, ?_, ?_, ?_⟩
  · rwa [happlication]
  · rw [happlication]
    exact runtime.handle_freshActivation middle.native.application resolved _ hhandle
  · rw [happlication]
    exact hlaw.2

/-- If a sequence of reserved relay pairs takes an active generated binding
to an inactive state, the first resolving environment step supplies a legal
source successor. Earlier pairs may use arbitrary player policies; while the
address remains active they preserve the original source refinement, and the
inactive suffix preserves the resolved refinement and fresh activation. -/
theorem runPolicies_binding_relay_pairs_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (relays : List P) (rosterOffset : Nat)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard) (deadline : Nat)
    (execution final : runtime.application.PolicyExecution)
    (activation : Activation Nat)
    (hrelays : ∀ index actor, relays[index]? = some actor →
      roster[rosterOffset + index]? = some actor)
    (hbound : rosterOffset + relays.length ≤ roster.length)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + relays.length →
      runtime.image.instructions[index / (roster.length + 2)]? =
        some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hslot : execution.environmentHistory.length % (roster.length + 2) =
      rosterOffset + 2)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = (fallback.bindingTimeoutCode fresh build deadline).node)
    (hcode : runtime.image.lookup (fallback.bindingTimeoutCode fresh build deadline).node =
      some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? final.native.application.base.memory ≠
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster)
      (relays.flatMap fun actor => [Invocation.player actor, .environment])
      execution).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      final.native.application.base.Refines sourceNext.current.graph.1 ∧
      final.native.application.FreshActivation ∧
      chosen = (fallback.bindingTimeoutCode fresh build deadline).resolvedValue
        (L.eval fallback.expr current.current.source.erasePubEnv)
        final.native.application.base := by
  let Witness := { pair :
    L.Val ty × CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph
      (build.addCommitEvent name who guard fresh.1).1 //
    pair.2.current.source = current.current.source.cons pair.1 }
  let target : Witness → Config
      (compileCore (.commit name who guard tail) fresh build).graph :=
    fun witness => witness.1.2.current.graph.1
  let Certificate : WindowedApplication.State P L → Witness → Prop :=
    fun result witness => witness.1.1 =
      (fallback.bindingTimeoutCode fresh build deadline).resolvedValue
        (L.eval fallback.expr current.current.source.erasePubEnv)
        result.base
  obtain ⟨witness, hfinalRefines, hfinalFresh, hcertificate⟩ :=
    runtime.runPolicies_relay_pairs_source_witness roster players relays rosterOffset
      (.bind (fallback.bindingTimeoutCode fresh build deadline)) who
      current.current.graph.1 execution final activation Witness target Certificate hrelays hbound
      hindex hslot (by rfl) hactive hactivation hrefines hinactive (by
        intro actor index afterPlayer afterRelay hactor hrelayIndex hrelaySlot
          hplayerActive hplayerActivation hplayerRefines hafterInactive henvironment
        obtain ⟨chosen, sourceNext, hsource, hnextRefines, hnextFresh, hchosen⟩ :=
          runtime.blockEnvironment_relay_binding_source_coupling roster players actor index
            guard tail fallback fresh build current unrestricted deadline afterPlayer afterRelay
            activation (.bind (fallback.bindingTimeoutCode fresh build deadline)) hrelayIndex
            hrelaySlot hactor rfl hplayerActive hplayerActivation hkey hcode hplayerRefines
            hafterInactive henvironment
        exact ⟨⟨(chosen, sourceNext), hsource⟩, hnextRefines, hnextFresh, hchosen⟩) (by
        intro witness before after schedule hcertificate hschedule hinactive hafter
        have hinvariant := runtime.runPolicies_block_inactive_invariant roster players schedule
          before after (.bind (fallback.bindingTimeoutCode fresh build deadline)) hschedule
          (fun state => witness.1.1 =
            (fallback.bindingTimeoutCode fresh build deadline).resolvedValue
              (L.eval fallback.expr current.current.source.erasePubEnv) state.base ∧
            runtime.image.activeAddress? state.base.memory ≠
              some (fallback.bindingTimeoutCode fresh build deadline).node)
          (by
            intro state actor command hstate
            constructor
            · simpa [BindingCode.resolvedValue, WindowedApplication.application,
                ApplicationImage.State.register] using hstate.1
            · exact hstate.2)
          (fun _ hstate => hstate.2) ⟨hcertificate, hinactive⟩ hafter
        exact hinvariant.1) hfinal
  exact ⟨witness.1.1, witness.1.2, witness.2, hfinalRefines, hfinalFresh, hcertificate⟩

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_binding_source_coupling

/-- info: 'Vegas.WindowedApplication.handle_before_window_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_before_window_binding_source_coupling

/-- info: 'Vegas.WindowedApplication.handle_binding_or_expiry_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_binding_or_expiry_source_coupling

/-- info: 'Vegas.WindowedApplication.environment_latest_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.environment_latest_binding_source_coupling

/-- info: 'Vegas.WindowedApplication.blockEnvironment_normal_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.blockEnvironment_normal_binding_source_coupling

/-- info: 'Vegas.WindowedApplication.blockEnvironment_relay_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.blockEnvironment_relay_binding_source_coupling

/-- info: 'Vegas.WindowedApplication.binding_relay_source_coupling_after_clock'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.binding_relay_source_coupling_after_clock

/-- info: 'Vegas.WindowedApplication.runPolicies_binding_relay_pairs_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_binding_relay_pairs_source_coupling
