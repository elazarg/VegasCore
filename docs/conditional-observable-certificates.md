# Conditional observable certificates

[PrivateTranscriptWeights](../GameTheoryExtensions/Analysis/PrivateTranscriptWeights.lean)
relates the existing adaptive private-strategy runner to observation-filtered
operator words. For a complete input/output transcript its actual unnormalized
moment factors into a policy coefficient and a kernel moment. Both factors
are positive when the transcript is supported. The actual Bayes posterior
therefore has the normalized kernel-word expectation. The proof uses the
policy's actual remembered transcript at every choice; it requires no blind
policy or likelihood-factorization hypothesis.

[ConditionalObservableTensor](../GameTheoryExtensions/Analysis/ConditionalObservableTensor.lean)
constructs the tensor of the two actual observation/action kernels. The signed
terminal observable computes the cross-product of their conditional numerators
and observation masses. Closure and zero initial moments on a supplied finite
spanning family force this cross-product to vanish for every word. Thus the
actual conditional expectations agree whenever that complete transcript is
supported in both models. Its probabilities may differ, and each model may
use a separately chosen adaptive policy. Hidden states are finite; inputs and
outputs need not be finite.

[The concrete client](../GameTheoryExtensionsTests/ConditionalObservableTensor.lean)
checks a three-column certificate on a sixteen-state product. The visible bit
has a variable prior independent of a hidden reward bit of probability 3/4.
A response either retains or flips that reward bit. Every observation/action
label preserves the supplied span, and its initial moments vanish for all
source and target priors. The resulting posterior comparison covers every
adaptive policy and supported complete transcript.

For the common approximation index n, the actual selected transcript masses
are 1/[2(n+2)] and 1/[4(n+2)]. Both are positive, unequal and tend to zero.
The retained and flipped responses have conditional values 3/4 and 1/4 in
both models at every index. The conditional incentive gap remains 1/2 despite
the different vanishing normalizers. The same symbolic closure certificate
works throughout the family.

These results transport selected conditional expectations. Full hidden-law
equality, native action legality, sequential consistency and the initialized
joint readout/payoff law remain separate obligations for an SE application.
The tensor is a proof device; no product game is added to the executor.
