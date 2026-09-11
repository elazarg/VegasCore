/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalImage
import Vegas.Compile.ConditionalSourceCoupling
import Vegas.Compile.ApplicationResolvedBindings
import Vegas.Compile.WindowedRelayResolution
import Vegas.Compile.WindowedBlockSettlement
import Vegas.Compile.WindowedApplicationDeadline
import Vegas.Compile.WindowedBlockSourceCoupling

/-! # Source coupling for actual windowed conditional resolution -/

noncomputable section


namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every successful message at an active generated conditional endpoint
produces its exact legal source continuation.  A successful opaque opening
itself supplies the frozen value; refinement identifies that value with the
source field, so no owner-policy or private-readout hypothesis is needed. -/
theorem handle_conditional_source_coupling
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
    (heligible : (ConditionalPublicationSite.atHead name publicName who guard tail spec)
      |>.PubliclyValidatable fresh build)
    (state resolved : WindowedApplication.State P L)
    (activation : Activation Nat) (address : Nat)
    (message : Message P (ApplicationImage.Payload P L))
    (hactive : state.active = some activation) (hkey : activation.key = address)
    (hcode : runtime.image.lookup address = some (.conditional
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
        fresh build sourceSlot deadline)))
    (hrefines : state.base.Refines current.current.graph.1)
    (hhandle : runtime.handle state message = some resolved) :
    ∃ (result : Option (L.Val spec.secretTy))
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1),
      (result = none ∨ result = some (current.current.source.get spec.binding)) ∧
        evalGuard guard (spec.encoding.symm result)
          ((current.current.source.toView who).eraseEnv) = true ∧
        sourceNext.current.source =
          (current.current.source.cons (spec.encoding.symm result)).cons
            (spec.encoding.symm result) ∧
        resolved.base.Refines sourceNext.current.graph.1 := by
  let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
  let code := site.code fresh build sourceSlot deadline
  have hsiteSpecification : site.specification = spec := rfl
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
  let retimedEndpoint := { code.endpoint with
    deadline := activation.since + runtime.windowOf code.endpoint.publicationNode }
  let retimed : ConditionalCode P L := { code with endpoint := retimedEndpoint }
  have hlookup : (runtime.atOrigin activation.since).lookup address =
      some (.conditional retimed) := by
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
  | conditional submittedAddress payload =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      cases hdecode : retimed.decode payload with
      | none => simp [ApplicationImage.handle, hlookup, hdecode] at hunderlying
      | some decoded =>
          rw [(runtime.atOrigin activation.since).handle_conditional state.base address retimed
            hlookup id payload decoded hdecode] at hunderlying
          cases hresolve : retimed.endpoint.resolveDisposition? state.base.memory.clock
              (state.base.verify retimed) (retimed.binding? state.base.memory)
              state.base.memory.done (retimed.canOpen state.base.memory.store)
              ⟨id, decoded⟩ with
          | none => simp [hresolve] at hunderlying
          | some result =>
              change Option (L.Val spec.secretTy) at result
              change ConditionalPublication.Payload P (L.Val spec.secretTy) at decoded
              rw [hresolve] at hunderlying
              have hbase : base = state.base.publishConditional retimed result :=
                Option.some.inj hunderlying.symm
              have hdefault : ∀ value,
                  retimed.binding? state.base.memory = some (.publicDefault value) →
                    value = current.current.source.get spec.binding := by
                intro value hbinding
                obtain ⟨typed, haccepted, htyped⟩ :=
                  (retimed.binding?_publicDefault_iff state.base.memory value).1 hbinding
                obtain ⟨fieldSpec, hfield, _, hty, hstored⟩ :=
                  hrefines.bindings.publicDefault retimed.sourceField typed haccepted
                obtain ⟨compiledSpec, hcompiled, hsecret, _⟩ := site.compiledSourceField fresh build
                have hspec : fieldSpec = compiledSpec :=
                  Option.some.inj (hfield.symm.trans hcompiled)
                subst fieldSpec
                have htypedTy : typed.ty = spec.secretTy := hty.trans hsecret
                have hgraph : Store.getAs current.current.graph.1.store
                    (site.sourceField fresh build) spec.secretTy = some value := by
                  change current.current.graph.1.store (site.sourceField fresh build) =
                    some typed at hstored
                  rw [Store.getAs, hstored]
                  change typed.as? spec.secretTy = some value at htyped
                  exact htyped
                have hsource := current.current.agrees spec.binding
                change Store.getAs current.current.graph.1.store
                    (site.sourceField fresh build) spec.secretTy =
                      some (current.current.source.get spec.binding) at hsource
                exact Option.some.inj (hgraph.symm.trans hsource)
              have hsource :
                  (result = none ∨ result = some
                    (current.current.source.get spec.binding)) ∧
                  evalGuard guard (spec.encoding.symm result)
                    ((current.current.source.toView who).eraseEnv) = true := by
                cases result with
                | none => exact ⟨Or.inl rfl, spec.decline_legal current.current.source⟩
                | some value =>
                    have hevidence := retimed.endpoint.resolveDisposition_some_evidence
                      state.base.memory.clock (state.base.verify retimed)
                      (retimed.binding? state.base.memory) state.base.memory.done
                      (retimed.canOpen state.base.memory.store) ⟨id, decoded⟩ value hresolve
                    have hvalue : value = current.current.source.get spec.binding := by
                      rcases hevidence.2 with hopaque | hpublic
                      · have hsnapshot :
                            (state.base.frozen (site.sourceField fresh build)).bind
                                (fun typed => typed.as? spec.secretTy) = some value := by
                          simpa [ApplicationImage.State.verify, retimed, retimedEndpoint,
                            code, site, ConditionalPublicationSite.code,
                            ConditionalPublicationSite.atHead,
                            hsiteSpecification] using hopaque.2
                        have hopaqueBinding := hopaque.1
                        change retimed.binding? state.base.memory =
                          some (.opaque (who, sourceSlot)) at hopaqueBinding
                        obtain ⟨fieldSpec, stored, hfield, _, hstored, heq⟩ :=
                          hrefines.bindings.opaqueBinding (site.sourceField fresh build)
                            (who, sourceSlot)
                            ((retimed.binding?_opaque_iff state.base.memory _).1 hopaqueBinding)
                        obtain ⟨compiledSpec, hcompiled, hty, _⟩ :=
                          site.compiledSourceField fresh build
                        have hspec : fieldSpec = compiledSpec :=
                          Option.some.inj (hfield.symm.trans hcompiled)
                        subst fieldSpec
                        rcases compiledSpec with ⟨actualTy, actualOwner, actualSource⟩
                        change actualTy = site.specification.secretTy at hty
                        rw [hsiteSpecification] at hty
                        subst actualTy
                        have hstored' : Store.getAs current.current.graph.1.store
                            (site.sourceField fresh build) spec.secretTy = some stored := by
                          exact hstored
                        have hsource := current.current.agrees spec.binding
                        change Store.getAs current.current.graph.1.store
                            (site.sourceField fresh build) spec.secretTy =
                              some (current.current.source.get spec.binding) at hsource
                        exact (heq value hsnapshot).trans
                          (Option.some.inj (hstored'.symm.trans hsource))
                      · exact hdefault value hpublic
                    refine ⟨Or.inr (congrArg some hvalue), ?_⟩
                    have hcanOpen := retimed.endpoint.resolveDisposition_some_canOpen
                      state.base.memory.clock (state.base.verify retimed)
                      (retimed.binding? state.base.memory) state.base.memory.done
                      (retimed.canOpen state.base.memory.store) ⟨id, decoded⟩ value hresolve
                    change site.canOpen fresh build state.base.memory.store value = true
                      at hcanOpen
                    rw [site.canOpen_source fresh build current.current.graph.1.store
                      state.base.memory.store current.current.source heligible
                      current.current.agrees hrefines.memory.publicFields value hvalue]
                      at hcanOpen
                    exact hcanOpen
              obtain ⟨sourceNext, hsourceNext, hgraph⟩ :=
                PublicChoiceSite.source_successor guard tail fresh build current
                  (spec.encoding.symm result) hsource.2
              have hpublic := PublicChoiceSite.ready_at_source_prefix guard tail fresh build
                current state.base.memory.done hrefines.memory.completed
              have hnodes :=
                (compileCore (.commit name who guard
                  (.reveal publicName who name .here tail)) fresh build).graph.publicChoice_ready
                    current.current.graph.1 who (site.choice.choiceNode fresh build)
                    (site.choice.publicationNode fresh build) state.base.memory.done
                    hrefines.memory.completed hpublic
              have hmemory := state.base.publishConditional_represents
                current.current.graph.1 hrefines.memory retimed
                (site.choice.choiceNode fresh build) (site.choice.publicationNode fresh build)
                rfl rfl rfl rfl result
              have hbindings := hrefines.bindings.completePair hrefines.reachable
                (site.choice.choiceNode fresh build) (site.choice.publicationNode fresh build)
                ⟨ty, spec.encoding.symm result⟩ hnodes.1.1 hnodes.2.1
              have hnext : (state.base.publishConditional retimed result).Refines
                  sourceNext.current.graph.1 := by
                refine ⟨?_, sourceNext.current.graph.2, ?_⟩
                · rw [hgraph]
                  exact hmemory
                · rw [hgraph]
                  constructor
                  · intro field handle haccepted
                    exact hbindings.opaqueBinding field handle (by
                      simpa only [ApplicationImage.State.publishConditional] using haccepted)
                  · intro field typed haccepted
                    exact hbindings.publicDefault field typed (by
                      simpa only [ApplicationImage.State.publishConditional] using haccepted)
              refine ⟨result, sourceNext, hsource.1, hsource.2, hsourceNext, ?_⟩
              rw [hresolved]
              exact hbase ▸ hnext
  | malformed data => simp [ApplicationImage.handle] at hunderlying
  | binding submittedAddress handle =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying
  | expireBinding submittedAddress =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying
  | choice submittedAddress typed =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying
  | expireChoice submittedAddress =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_conditional_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_conditional_source_coupling
