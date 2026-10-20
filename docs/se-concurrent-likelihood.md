# Concurrent qualified likelihood and causal payoff

This document gives a candidate mathematical route to the exact
`PhaseProposalQualifiedBinding.QualifiedBindingLaw` proposition. Independent
agent reviews and a root-agent model audit reviewed the argument. These are
not human reviews or a Lean proof. The global reconstruction remains open in
mathematics: the direct ordinary source law and observable compatibility reader
must cover all compatible source histories, independently of a selected native
history's conditional fiber. Existing local identities do not establish that
coverage. The proposition is type-checked; its transport theorem and full
sequential-equilibrium preservation remain unproved in Lean. Exact-rational
normalized experiments are falsification checks, not verification of the full
raw-action likelihood argument below.

The scope is the actual reserved implementation in mode `.concurrent`, with
its existing `Operational` hypotheses. Binding types are finite. The initial
source law mu is an arbitrary finite-support JOINT law. The service tape has
one unconditional whole-execution prior, independent of that initial draw;
its coordinates may be correlated across players and time. The argument does
not cover replacement block priors selected from an observed public prefix. Observation is exactly `completePendingObservation`, not an arbitrary
handle-sensitive leak kernel. The compiled order is `barrierOrder`: different
owners' private bindings can overlap, but a ready public event has its exact source prefix complete. Samples are singleton phases. The separate
`.concurrentReveals` mode is outside this contract.

Fix one finite index of the prescribed native/source assessments, with strict
positive flag rates below one and the full-support ordinary table D. Source
prescription is needed only at genuine running histories. Fix a native ready,
UNSENT binding information I for focal owner i. The clean case has neither
saved nor current own binding debt. The public saved-exclusion readout is the
retired failure union plus the current failure footprint BELOW saved-low.
If current exclusion differs from this readout, the all-admitted gate is
impossible. These are observable case classifiers, not added model hypotheses.
Earlier accepted BAD in canceled attempts remains in full recall and is allowed.

## The exact aggregate statement

Write r_N(h) and r_S(g) for the actual initialized history reach weights, and
Z_N(I) for native informationMass. There is no additional occupation factor.
For a legal literal proper SEND c encoding typed value v, use the existing
`currentStep` and `stoppedFinish`: force c once, run the ACTUAL zero-flag native
policy until the first exit from the original attempt, and finish from that
same history. The zero-flag policy is the BASE class law, not the totalized ReferencePolicy instantiated with a point-mass table.

Let GN(h) mean no foreign generated unusable binding in the ENTIRE original
past. Let beta(h,stop) be `originalAdmissionGate`: the actual original closing
trace extension has a raw drained image in which every ENTRY-ACTIVE binding
event has an accepted handle. It is admission, not guard success or typed
properness. Inherited excluded rows are automatic. Define reach submeasures

    U_c(y) = sum_[h at I] r_N(h)
               Pr[GN(h), beta, some(nativeGrossPayoff)=y | h,c],
    T_c = sum_y U_c(y),
    S_J = sum_[g at J, sourceForeignGood(g)] r_S(g),
    V_J,v(y) = sum_[g at J, sourceForeignGood(g)] r_S(g)
                 Pr[some(sourcePayoff)=y | g, force v once, then source0].

The desired zero-safe identity is S_J U_c(y)=T_c V_J,v(y). It must construct
ONE full source information J, a faithful legal typed encoder at J and the
ordinary source0 baseline pushforward, before quantifying over c or utilities.
The source experiment is exactly `sourceCausalPayoff`: actual source belief
filtered on sourceForeignGood, one literal intervention, then the original
zero-flag continuation at UPDATED queries. No baseline future is conditioned
on v. A positive branch also proves S_J>0 and one common T_c across every
proper value, serial and raw encoding. The zero branch requires no source J.

## Original initializer, tape, and source factors

Retain the complete initial draw theta with its literal atom mu(theta). The native initializer is injective on theta: initial_invariant preserves
inputs, initial_agrees identifies the original cells, and decodeState?_eq_some
recovers theta from the initialized native store. Thus pmf_map_apply_of_injective
preserves mu exactly, including arbitrary correlations. No product of marginal type priors occurs anywhere.

For an ORIGINAL full native trace p, let rho(p) be its chronological environment
input/command word. Define w_tau(p) by its actual path product, replacing ONLY
the behavioral scheduler command atoms by the fixed family's atoms at tau.
Keep the original initializer, player policy atoms and physical result atoms. Then, pointwise on this same trace,

    prior(tau) w_tau(p) = r_N(p) posterior(rho(p))(tau).

Initially the posterior is prior. A response preserves environment recall.
At an environment constructor, command_disintegrate/posterior_snoc gives
P(tau) family(tau)(command)=scheduler(command) P_new(tau); multiply by the
same physical result atom. Protocol init is None; its first step initializes
Some, and all later states remain Some, including terminal remaining zero.
No fallback posterior at None is used. This scalar induction retains the
WHOLE original trace, so any same-trace witness annotation can be attached
before summation. A physical-state marginal alone would not justify that.

On source foreign-good histories, the checked source class factorization is

    r_S(g)=mu(theta(g)) P(g) O_i(g) C_-(g) D_-(g) R_-(g).

P contains public Nature atoms, excluding initialization. O_i is the entire
source own-action product, including canceled BAD. C_- contains foreign class
normalizers; D_- contains proper foreign binding atoms; R_- contains the
conditional foreign publication causes. Full source information J fixes P,
O_i and C_-. Public Nature operands and completed guard operands are public.
The native focal RAW product N_i(I) and source O_i(J) are separately retained: their historical getters need not agree after focal BAD.

## The exposed-prefix joint and its invariant

First work at an UNCONDITIONED native physical depth t. Choose the source
witness by initialization and the SAME parent's response/environment witness
constructors. Its qbar(p) is the CLOSED current phase-entry source prefix,
lifted with `nativeArchiveLabels` of the actual submitted proposal archive.
This retains failed-but-submitted proposals. Do not independently choose a
new witness at each prefix or derive it from a coarse mechanical projection.

Let K_p(q) be the ACTUAL finite-source run from that literal initialized theta
to qbar's depth, conditioned on its full focal source information, ENTIRE chronological foreign cause-read word and foreign-good bit. Only hidden
foreign publication causes vary. No future row enters this conditioning.
Let Q_q(z) be the existing ordinary FOREIGN owner-word product at that entry
in a BIND phase, and the unit law otherwise. Conditional on the full entry,
source own-view locality and `prefixLaw_entry_word_kernels` prove this product:
a foreign binding changes no other owner's private cells or own history.
Current NoMiss controls, static addresses and archive determine each key.

E_p(z) tests only ACTUALLY emitted declarations, indexed by full attempt and
event, retaining message provenance. Set Z_p(q)=Q_q(E_p). An unissued event
has no test and no atom charged to native reach. A latent complete ordinary
word is an annotation; it is not a prospective source past or an early filter.

Let m retain the chronological public/environment projections, opaque packets,
receipts, handles, occupancy and ALL crossed focal raw recall, beforeviews and
catalogue. It erases foreign meanings, source W/K/read words and hidden causes. Define the actual joint extension, zero on zero cylinders,

    Lambda_t(m,q,z)=sum_[pi(p,tau)=m] r_N(p) posterior(rho(p))(tau)
      * 1[GN(p), focalAlive(p)] * K_p(q) * Q_q(z)1[E_p(z)]/Z_p(q).

Its native marginal is the CURRENT good/alive submeasure. There is no test of
future reachability of I. Indices below restrict m to that current projection
image, and q to closed sourceForeignGood histories with focal owner alive.
Bad registration or focal expiry removes a child from both retained sides.

Define chi(m,q) by initial public/focal cells; closed public/control/archive
and decoded focal own words; closed attempt/rank masks; public/focal-own saved
and current projections. During PUB, current means the closed-entry compiled
cells plus the LIVE completed-public-prefix overlay: typed public results,
registry/proposal metadata, exclusion and cursor. Barriers/AutomaticReady make
that completed set a static prefix. Saved entry stays fixed; no hidden T/F
cause is selected. Each live OPEN plaintext also attaches to its accepted
binding occurrence. Foreign stores are RECONSTRUCTED from q,z and immutable
registration, not assumed equal. Query equality, replay existence and a supported source cursor are not fields of chi.

Let N_t(m) be crossed focal RAW probability atoms, O_closed(q) the closed
source own product, C(q) its closed foreign class product, and o_t(q,m) the
auxiliary source NoMiss calibration for already-issued current focal bindings.
It depends only on source own entry/prefix, not unissued foreign values.
Pending calibration is not an admitted source action. Let O_t=O_closed o_t.
B_t(m) is the original tape atom times crossed family command atoms and
foreign mechanical coefficients: WAIT, proper-BIND/no-BAD/fresh-slot and PUB
SEND/WAIT. Exact foreign raw-history normalization sums their alias fibers;
focal raw aliases remain literal in N. Matched mu/Nature atoms stay in r_S. The
intended finite induction must establish the weighted identity

    O_t C(q) Lambda_t(m,q,z)
      = N_t(m) B_t(m) chi(m,q) r_S(q) Q_q(z) o_t(q,m).              (F)

## Initialization and every successor

At init both trace masses are one. Its first transition multiplies the SAME
mu(theta), with the original tape atom in B. Initial K is pure and Q has mass
one. Every compatible target initializer has its unique encoded preimage.

At a foreign proper BIND SEND, accepted/issued own-prefix readback, filled-view
erasure and NoMiss controls/address/archive DERIVE the actual D key. Surviving
foreign-GN cells are proper, so virtual repair is inert. NoMiss erases ALL new
current-attempt exclusion signals, including a static-earlier miss whose
physical expiry occurs later; retired signals remain. No unissued foreign
value enters the getter. The actual class atom is b D(key)(v), where b is
the waiting/no-BAD/fresh-slot coefficient; D(v) means its typed pushforward. The cylinder law gives Z'=Z D(v).
Before summing native value children, Lambda'_v=b Lambda 1[z_next=v]; afterwards
sum_v 1[z_next=v]=1, giving B'=bB. This is the AGGREGATE identity (F); a per-native-prefix equation must retain the indicator. Zero atoms use the
unnormalized cylinder equation, not division by a target atom. Foreign WAIT
changes B by its actual coefficient, forced WAIT by one; BAD is outside GN.

For focal pre-I raw atom a, Lambda'=a Lambda and N'=aN. If it issues BIND,
multiply o and its corresponding right-side calibration by the SAME source
own atom s. No historical focal getter comparison is made. WAIT adds no source
row. Focal expiry permanently excludes it and kills the surviving submeasure.

A foreign PUB SEND exposes plaintext w before source-row emission. The actual
opening policy and counted menu fix stored success w, its accepted handle and
truthful certificate; raw class projection preserves mass. Let A_w(q) test that newly public attached bound value. Then Lambda'=b Lambda A_w,
chi'=chi A_w, B'=bB, with q,C,K unchanged. There is no D draw. Available SEND
has coefficient 1-waiting, WAIT has waiting, forced WAIT one; guard rejection
is allowed. This is a public exposure constraint, not arbitrary hidden-store
equality. Both lookup=openable(w) AND binding.get?=success(w) are preserved.

Public inclusion updates the live overlay using the fixed checks' public
operands. For two reveals A then B, rejecting OPEN(A,x) has the SAME overlay
failure/proposal x/E+{A} for truthful and failed-disclosure causes. B's guard
reads that public prefix. If B=A it is automatic NONE; otherwise its old
accepted binding and lookup persist. This also preserves focal beforeviews.

Source PUB rows advance only at WHOLE phase close. For a virtual foreign row,
the actual source atom is c R. For rejecting guard with proposed value,
c=(1-omission)+omission*delivery; R assigns the two causes their individual
weights divided by this SAME c. Whole-key truncation gives a unique predecessor;
the publication cause/history laws exhaust its alternatives. Class constancy makes c common on hidden refinements. For actual key masses H_x,H_y,

    H_y K_y(q')=H_x K_x(q)cR,       H_y=H_x c.

Positive cancellation gives K_y=K_xR; zero fibers keep the weighted equality.
The actual retained source fiber is positive by full mixing and the constructed
legal source path. Telescope the BLOCK: K gains product R, C product c, O_closed the focal source atoms, and r_S all those factors. Native Lambda
gains its actual phase atoms and product R; N/B gain only their raw/mechanical
atoms. No (F) is asserted at intermediate virtual source rows. Ambiguous
foreign publishers are permanently excluded; surviving OTHER owners' queries
are unchanged. Do not claim the failed author's own private query is unchanged.

Environment activation/complete observation, wait/clock, rejected or stale
inclusion, and disallowed application commands keep the field attachment and
multiply B by their actual command atom. Successful binding inclusion writes
the lookup's typed value; expiry writes failure and excludes. A sample phase
is singleton, so native/source Nature atoms and source advancement coincide.
The full-trace tape identity applies to every command, including stutters.

## Historical close, restore, and exhaustive coverage

At Finished, scan the raw accepted table in STATIC order from entry exclusions:
inherited exclusion gives automatic NONE; active absent gives missing and
excludes its owner; active present gives a nonmissing row. Final-row source
close preserves the exclusion set across retry or exhaustion. The accepted
table is retained in the failed attempt's retired public record or in the clean
saved frontier; matching only final E or physical expiry order would be wrong.

For ANY compatible target source child, cut its FULL trace at this same saved
occurrence and apply the earlier-depth induction identity there. Assign each
admitted foreign value to the registration named by the actual accepted handle.
Keep every focal raw preparation literal. Replay the fixed mechanical segment.
Immutable registration supplies BOTH the lookup and typed-store value in
current, saved and retired states. The derived own-prefix getter gives the
correct D atom at each SEND; freshness, eligibility and inclusion depend on
the retained namespace, headers, public cut and clocks, not hidden meanings.

Every focal beforeview is reconstructed: public application view from the
overlay; private live cells from its own word/attachment; ENTIRE catalogue
from its own initializer and raw registrations, including dead BAD slots;
network knowledge from retained packets and complete observation; recall by
appending the literal raw actions with these computed views. Thus raw menus
and raw probability atoms equal those in m. Final-I equality is not an extra unexplained filter. This establishes the target's native preimages.

Conversely deleting the segment recovers its predecessor and admitted draws.
Per foreign owner, UNSENT and owned readiness give an admitted prefix and at
most one emitted unaccepted leaf. Finished forces that leaf's admission or
permanent exclusion. Only in the latter case sum its actual conditional D and
any untouched Q tail to one, tail first. With no SEND, sum only the untouched
tail. Pending values and admitted canceled values are NEVER integrated away.
The lost mean is never stored, counted binding wire/evidence does not reveal
it, permanent exclusion suppresses later own callbacks, and ownership prevents
another actor opening it. Hence these are exactly the free weighted preimages.

Close moves admitted values into source reach, with matching O/class factors;
the cylinder equations and these complete inverse fibers push (F) forward.
Renew Q only at the real next entry. Clean normalization saves the drained
state. Retry archives it, copies saved config AND accepted handles, retains
catalogue/clock/E, refreshes activation and increments generation. Exhaustion
archives then advances; automatic excluded rows have probability one. Restored
cells are not synthesized attempted actions. These deterministic maps preserve the inverse and the full chronological canceled word.

Whole-history native GN implies closed sourceForeignGood independently of
this density. Each NEW nonmissing decoded source BAD has an accepted handle
with bindingResult failure. Actual stamp, provenance and count correctness give
its fresh prepared raw recall entry; immutable recorded-material readback makes
that preparation unusable. Initialization has no such BAD, responses stutter
the source, PUB/Nature add no binding, and normalize/retry retain old origins.
Automatic/exhausted source rows cannot create a new nonmissing BAD. Current
state properness alone would not establish this whole-history implication.

## The forced current action and retained causal focal tail

Only after the unconditioned induction restrict to the native antichain I.
For each anchor h, unique PER descendant path, use the ACTUAL spliced prefix
weight r_I^c(h,p,tau): r_N(h) times currentStep's forced atom and subsequent
source0 native transition atoms until first original exit, with the same tape.
Do not use finite-n r_N on these descendants. Freeze K at h's closed entry,
N at I and the earlier focal calibration o_I. Ready/UNSENT gives precisely all
earlier own rows admitted and no later own row issued, so o_I=O_<v.

Let H^v_{q,u}(eta) be the ACTUAL source0 remaining-current-BIND focal-word law
after earlier own word u and forced v. A proper source prefix exists internally
by fullValues on the literal rows; source own-view locality makes this law
independent of the chosen foreign fill. Its keys update with u,v,eta_<j.
There is no D(v), finite-n flag or later-block draw in H. Let E^i_p test actual
post-v focal issued preparations, Z_i=H(E^i_p), initially one. Retain the JOINT

    Lambda^1(m,q,z,eta)=sum_[pi^1(h,p,tau)=m] r_I^c(h,p,tau)
       * 1[GN(h), focalAlive(p)] K_h(q)
       * Q_q(z)1[E^F_p(z)]/Z_F * H^v(eta)1[E^i_p(eta)]/Z_i.

At future focal SEND j, ready/alive and immutable readback derive its UPDATED
source0 key; clean saved/current cells make repair inert. Its typed head law
is D_j, the ordinary domain law mapped by the actual typed preparation readout. For d=D_j(w), the zero-safe cylinder identity is

    Z_i d H_Enew(eta)=Z_i H_Eold(eta)1[eta_j=w]=H(eta)1[Enew].

Actual encoder preimages have class mass one, then the value-child sum selects
eta_j. WAIT consumes nothing; a pending focal miss kills this alive branch.
Stage1 erases post-I focal private means from m: NEW focal stores/catalogue
are reconstructed from forced v and eta, not tested against deleted m data.
Thus the stage1 density is (F) with its right side additionally multiplied by
H^v(eta). This proves the actual joint marginal, not a payoff law inferred from
an already averaged eta. At the all-admitted close both cylinders pin the
actual word. After this close the terminal kernel is UNFILTERED, including later focal publication failure and its floor payoff.

## Static cut, common site, payoff attachment, and Bayes

Let g end immediately BEFORE the selected STATIC rank and G at whole close.
Source prefix splitting gives Q_q(z)H^v(eta)=d_<v(g)P0_g,v(G), whereas r_S(g)=r_S(q)O_<v C_<v d_<v. Since O_J=O_closed o_I and C_J=C_closed C_<v,
multiply the density by C_<v. Finite-n reach stops at g; forced v has no atom.
Early-issued static-later values stay in P0; late-issued static-earlier values enter g only now. Eta remains under the actual payoff map.

Full J fixes initial public/own cells, every prior mask/control/address,
disclosed proposal plaintext and own history. All earlier PUB phases are
closed; the current qualified masks are entryE. A proposal label is only a
Boolean: recoveryProposal reads plaintext from the actual stored binding,
even when proposed=true accompanies a withheld semantic reveal. Thus J's
proposal w also enforces the earlier live bound-value attachment A_w. The inverse therefore
constructs preimages for EVERY good g at this SAME J and mechanical domain:
chi leaves no extra hidden-theta or unrevealed-foreign-value restriction.
Canonical-cut information uniqueness is used AFTER construction to choose
one J, not to assume reverse coverage. Getter readback gives its faithful
typed encoder and the exact source0 ordinary-D pushforward.

Completed-binding history, the BindingWord congruence and commit-window
uniqueness identify the WHOLE semantic G from the SAME old prefix. Silent BIND
proposal delta and retained old archive labels give erased-history equality.
Fresh normalization and the per-tape fresh payoff law identify source0 terminal
payoff at the literal stopped clock and original horizon. Later PUB/Nature
stay in this causal kernel. Apply that map BEFORE summing eta.

Finite sums now give S_J U_c(y)=T_c V_J,v(y), with both submeasures zero at
none and totals T_c,S_J. If no proper value exists, the zero branch is vacuous;
zero qualification gives pure none without J. Positive qualification constructs a
good source g, hence 0<S_J<infinity. Native admission-word symmetry on the SAME
original posterior makes T_c common across all proper encodings, after sums.
J and encoder precede utilities/choices. Bayes gives U/Z_N and source-good
V/S_J; a=T_c/Z_N lies in (0,1]. Complement mass is 1-a on none. This is exactly
the qualifiedPayoff/sourceCausalPayoff mixture in QualifiedBindingLaw.

## Signed gain consequence

For each proper c(v), the final source override is mix a (pure (encode v))
with the ACTUAL prescribed source.strategy at J. BAD/WAIT map to its identity
override, using the actual WAIT/floor/reset comparisons. Binding this affine
map over a native lottery of proper mass p and typed pushforward L yields
lambda=(1-a*p)*source.strategy(J)+a*p*encode_*L. Its signed source gain has
coefficient a*p; no finite-index source-gain nonnegativity is assumed. The
D-based lottery is only an intermediate source0 comparison. Its current
ordinary-D versus actual noisy-baseline TV error and future same-override TV
error must both be paid before asserting the prescribed-source gain bound.
If q is native-good posterior mass and s the returned source-bad posterior,
absolute payoff bound B gives native-bad error 2B(1-q) and source conditioning
error 4Bs. With native current/future flag error e_N and per-experiment source
ordinary-versus-prescribed TV error e_S, including CURRENT flags,

    nativeGain <= sourceGain(lambda)+2B(1-q)+4Bs+e_N+4B e_S.

The shared sequence makes these errors vanish; e_S is bounded by the source
horizon times its one-step flag bound. Zero qualified mass uses the source
identity/error-only branch without positive J. This consequence still needs
its complete Lean consumer; it asserts neither proved preservation nor human verification.
