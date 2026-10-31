# Formalization report

## Publication-copy context (31 October 2026)

The maintainer authorized public release and official full mechanical preflight
on 31 October 2026. The clean project is public and the development archive
remains private and read-only. Official full-preflight outcomes must be read
from the exact-commit mechanical report; service intake and registration have
not been requested. Earlier private-preparation status statements below are
historical records.

The active project is `igor-kortchemski/height-infection-tree`, formerly the
clean publication candidate `height-infection-tree-palomar`. The original
development repository is retained privately, read-only, as
`height-infection-tree-archive`. Its complete Git history and manuscript files
were backed up and independently read back before the rename. This publication
project retains its clean history and the complete 31-result coverage record.

This coverage record is retained from the development archive. The publication
copy contains the complete Lean sources from verified baseline commit
`7f56d1daf0ba8d2d621b6da715f1fdb7c44e4961`, with no mathematical edits.
`publication/source-files.sha256` records their byte identity. The selected
Palomar record consists of the two main theorems and the following uniformity
paragraph; the broader 31-result inventory below remains intact.

The source audits used the supplied revised manuscript with SHA-256
`c247d8b4479bf300e3529ed35701a07b00277584d2d66d4587f39a0e8d2c1626`.
Historical mentions of the TeX, blue manuscript, proof companion, roadmaps,
skills, local folders and milestone tags describe that archive. Those materials
and its Git history are not part of this clean publication copy. Source line
numbers refer to that supplied revision. The public bibliographic reference is
[arXiv:2504.03526v1](https://arxiv.org/abs/2504.03526v1); it is not asserted to
be byte-identical to the supplied source or newly audited against every
certificate. The corrections and proof-route disclosures below remain the
applicable mathematical account.

Baseline Linux CI and private Comparator both passed for the source commit
above, including Lean and NanoDa acceptance. Their inspected reports are
archived in `verification/source-baseline/`. They are historical evidence, not
reports for a later publication-copy commit. Fresh verification of this copy
is recorded by its own CI and Comparator reports. No official full Palomar
preflight, intake or registration has occurred.

## Status and scope

This is the full-article continuation in `height-paper-full`, created on
2026-10-29 from the preserved sibling `height-paper`. The inherited milestone
is Git tag `main-height-theorem`, commit
`db724b5d7a0cbe0fe0561843ee01e247e17b4ad4`, available in both repositories.
The setup added no proofs. Subsequent work now formalizes additional parts of
the paper's own Lambert, complex-normalizer, martingale, urn, and uniform
stochastic-control route. The existing inventory remains the coverage record
for the full article. New work
is distinguished from the inherited main-theorem proof below.

**`thm:main` is proved.** `HeightPaper.mainTheorem` in
`HeightPaper/MainTheorem.lean` proves the unchanged `MainTheoremStatement`,
including every nonnegative rate sequence with $n\lambda_n\to\lambda>1$.
`main_limit_of_asymptotic` exposes the source hypothesis
$\lambda_n\sim\lambda/n$ directly. No stochastic estimate remains an
assumption of these exports. The authorized corrected coupling is also proved;
retained unlabelled and numerical claims are listed separately below.

The source is *The height of the infection tree*,
`height_of_epidemic_tree_revised.tex`. Both main theorems, `thm:main` and
`thm:profil`, are proved. The inventory below retains the other article claims
as separate obligations.
The five technical stochastic-control lemmas at lines 1625–1659 and the finite
and local random complex-normalizer asymptotics are proved. The fixed-parameter
strong profile theorem and its additional parameter-uniform strengthening are
proved in `StrongProfileTheorem.lean` and `UniformStrongProfileTheorem.lean`.

Current coverage after the statement audit and its completed repair,
2026-10-30: **all 31 numbered results have certificates matching the source
statement or an explicitly recorded correction/convention.** There are 25
source statements and 6 corrected statements or endpoint conventions. The
previously missing full-time almost-sure compact-uniform convergence in
`proposition cv unif martingale` is now proved by
`localProfile_ae_canonical_complex_compact_limit_ae_physical`. Its exact source
correspondence has been independently reviewed. The earlier audit correctly
withdrew an overstrong completion claim; the missing bridge is now supplied
without weakening the paper's conclusion. The printed coupling remains false
and is covered by its separately stated authorized correction.

Fresh complete integration: `lake build` passed with **4383 jobs**. The final
batched axiom check covers 21 declarations, including the new full-time
certificate, its dependencies, the main theorems, the corrected coupling and
the four frozen exports. Only `propext`, `Classical.choice`, and `Quot.sound`
occur. An exact-type example of the source full-time assertion compiled.
The toolchain, dependency pins, and frozen main-theorem source files remain
unchanged. The all-results audit below retains the six explicit corrections
and distinguishes proof changes from changes to statements.

For the unlabelled improved fluid lemma, the source survival-indicator comparison was checked directly on the coupled uniform space. The unabsorbed fluid estimate was proved by an alternate active-padding construction, exact harmonic-clock identity, stopped martingale variance estimate, and a common finite time grid. The manuscript's appeal to its earlier distributional fluid limit and the cited external equation were not checked as part of this new proof.

For `prop: convergence vers M infini`, the coupled-law proof compares
the finite profile at each complex tilt directly with the local limit at the
fixed real center. It combines the finite small-tilt moment and real-center
finite-to-local moment by a conditional triangle inequality. This bypasses the
paper's four-term intermediate-time decomposition; that decomposition has not
been checked. The complete nonnegative parent integral is measurable for the
sigma algebra of the two full signed walks and satisfies the defining
set-integral identity of their extended conditional expectation. A uniform
higher-moment bound makes it finite on a high-probability survival event and
identifies it with the ordinary integral there. The resulting convergence is
uniform over all shrinking compact complex tilt sets and compact rates. The
local-survival version is stronger than the source's version with finite
survival and safe-cutoff indicators.

- Lean: `leanprover/lean4:v4.35.0`.
- Mathlib: `v4.35.0`, revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- The exact transitive pins are in `lake-manifest.json`.
- Git records the milestone and subsequent work. `AGENTS.md` preserves the
  inherited main-theorem exports; no separate frozen export manifest is present.
- The TeX source was corrected at `lem:eventE`, its use in `lem:dangling`,
  an algebraic sign in the proof of `lemme z n proche de z`, and the missing
  preterminal bound $A_n\le\lfloor nt\rfloor$ in that lemma. The finite
  coupled conditional-moment result, its full event-word conditional
  expectation bridge, and finite-horizon original-path probability transport
  are proved. The source-hypothesis and full binary-word identifications
  are now checked for the small-tilt lemma. The toolchain, Lake
  configuration, and dependency pins are unchanged.

## Proved mathematics and model

The finite SIR model is an actual probability kernel on rooted infection trees,
with active vertices and a susceptible count. Each infection attaches a child
to a uniformly chosen active vertex; each recovery removes an active vertex.
The infection probability is $rH/(1+rH)$, and the recovery probability is
$1/(1+rH)$. The count projection is proved to satisfy `eq:transitions`.
Population is preserved, and the process is absorbed by step $2n+1$.
`heightLaw` is the terminal tree-height law, not an unspecified random variable.

Every supported terminal state is attained by a supported path. Along such a
path the first extinction time is exactly $2|T|-1$. The terminal-state event
`sourceSurvivalEvent` is therefore the paper's event

$$
E_{n,\delta}=\{\tau'_n\geq\lfloor(1-\delta)t_\lambda n\rfloor\}.
$$

Its complement is the strict early-extinction event. For a positive cutoff
$K$, survival to $K$ means activity at $K-1$, including the case of extinction
exactly at $K$. Both the cutoff bound and eventual positivity are proved.
`SourceCutoffState.lean` proves that the source survival event is exactly
determined by the state at the floored cutoff on every supported full path,
including extinction exactly at that cutoff.
`LateRecoveryEndpoint.lean` proves that the all-late-times recovery-probability
event of `lem:eventE` is exactly determined by the cutoff and terminal
susceptible counts on each such path. It also proves
`not_lateRecoveryEvent_of_large_eta`: for $\eta>1+m_\lambda$, the printed
late-recovery event is impossible on every supported path.
`LateConditionalGoodStates.lean` disintegrates the path-level late-recovery
error over the genuine cutoff-state law. A square-root threshold produces
good cutoff states with uniformly vanishing continuation error; their
conditional probability given exact source survival tends to one. The
continuation success probability on each good state is at least one minus
that threshold. The supported good-state set is eventually nonempty, has the
same conditional mass, and consists of states attained by the actual cutoff
law. The infimum of its continuation success probabilities tends to one.
`ConditionalContinuationGoodStates.lean` makes the same finite-law extraction
available for arbitrary continuation events. `SourceConditionalOutgrowth.lean`
and `SourceConditionalOutgrowthGeneral.lean` apply the actual real-Laplace
root-count profile, upper and lower geometric comparisons, terminal pressure
barrier, and exact source survival probability to all three dangling-tree
height clauses. The selected good cutoff states lie in the actual support and
inside the non-strict source survival event. Their conditional mass tends to
one, their continuation height-error probabilities vanish uniformly, and
`source_dangling_all_probability` gives the paper's conditional convergence in
probability for finite, infinite-tail, and low-depth bins.

The tree model also proves the disjoint partition into fresh outgrowths rooted
at the first old ancestor. Along a supported history, a root of a nontrivial
fresh outgrowth was active at the cutoff. Frozen cutoff roots have singleton
components. Consequently the exact final-height maximum in the main proof is
proved in `SupportedPath.height_eq_max_active_outgrowths`.

The analytic definitions are characterized on the entire domain $\lambda>1$:
$z_\lambda$ is the unique positive zero of $f_\lambda$, and $m_\lambda$ is the
unique element of $(0,1)$ satisfying
$m_\lambda e^{-m_\lambda}=\lambda e^{-\lambda}$. Principal-branch range and
inverse-equation proofs identify these with the paper's Lambert expressions.
The critical parameter exists uniquely, has the correct crossing orientation,
and both branches of $\kappa$ equal the variational maximum. This proves all
three parts of `prop:lc`. The roots and coefficient are continuous on
$(1,\infty)$, including the critical parameter, by
`continuousOn_mainCoefficient` and its companion root theorems.

The deterministic fluid curve satisfies $g_\lambda(0)=1$ and the stated ODE.
The final-size fixed point is unique in $(0,1)$; its extinction time is the
unique strictly positive zero of $2-2g_\lambda(t)-t$. The untruncated infectious curve is
strictly concave, positive before extinction, and negative
after it. The identity $\lambda g_\lambda(t_\lambda)=m_\lambda$ proves `lem:mt`.
These deterministic identities alone are not a stochastic fluid-limit theorem;
the finite-kernel stochastic results are described below.
The entire late fluid interval has pressure arbitrarily close to
$m_\lambda$, and explicit small-perturbation bounds put the associated recovery
probabilities strictly between one half and one (`Analysis/LatePhase.lean`).

The actual prescribed-event history law now proves the conditional expectation
identity of `lem:Mk is a martingale` on the full-history filtration, the exact
expectation product, and both unshifted and shifted complex martingales. The
shifted theorem retains the random prefix and requires nonvanishing only after
the chosen cutoff. These results use the paper's uniform attachment/freezing
argument. `pathLaw_filter_eventCylinder` now identifies this law exactly
with the actual epidemic conditioned on any possible positive finite event word.
Its probability is the product of count-dependent event probabilities. The
full infinite tree coupling and parameter-uniform complex martingale limits
remain separate obligations. The actual count coupling and its uniform
stochastic controls are now proved, as recorded below.

New finite-kernel estimates prove the harmonic invariant
$F=I+H-r^{-1}\sum_{j=1}^{H}j^{-1}$ has zero drift before susceptible depletion,
with exact one-step variance $1/(rH)$. Stopping at a positive susceptible
threshold gives mean-square and probability bounds. A positive final-size
barrier removes the stop. `evolve_finalSizeInvariant_normalized_concentration`
and `evolve_active_infectious_concentration` now prove invariant concentration
and the fixed-time fluid location of surviving epidemics for arbitrary allowed
rate sequences. Geometric test functions and the fluid clock give
`evolve_extinction_tendsto_reciprocal`: extinction probability tends to
$1/\lambda$ at each strictly intermediate fluid time. The exact terminal cutoff
probability is proved by `sourceSurvivalEvent_probability_tendsto`.
A killed geometric potential also proves a geometric bound on late extinction
within the early supercritical phase. This gives
`sourceExtinction_height_div_log_tendsto_zero`, the logarithmic height
negligibility needed for the main mixture. The source-survival versus cutoff-active distinction has vanishing probability
(`sourceSurvival_cutoff_inactive_tendsto_zero`). Terminal event count and susceptible
fraction concentrate at their fluid extinction values on survival, by
`sourceSurvival_eventCount_concentration` and
`sourceSurvival_finalSusceptible_concentration`. The unscaled early-height
conditional law is proved later in this continuation. Monotonicity of the susceptible count
then gives uniform pressure and recovery-probability control after every
sufficiently late fixed cutoff, with the corrected small-$\eta$ range.
A deterministic susceptible threshold strictly below the final fluid value
has vanishing failure probability and supplies the lower outgrowth barrier.

Actual selected fresh outgrowths satisfy finite upper and lower height bounds,
proved by a bounded product of geometric extinction probabilities on active
vertices. The potential remembers previous height exceedances after recovery.
Its terminal value is the height-distribution indicator. This yields
`continuation_freshHeight_tail_le_geometric` and
`continuation_freshHeight_cdf_le_geometric_exp`; the latter has one explicit
terminal susceptible-barrier error. The independent geometric generation and
forest laws, their exact height tails, and the correspondence to the model's
fresh outgrowth heights are also proved. The actual maximum outgrowth height divided by $\log n$ is proved to
concentrate at $f/(-\log m)$ from explicit deterministic root-count and pressure
limits; lower susceptible barriers need only approach $m$ from below.
A joint cutoff/final-state law with exact marginals now gives averaged
upper and lower outgrowth bounds, and finite-bin union bounds. It is proved to
be the two-coordinate marginal of the actual epidemic history. Probabilistic
logarithmic root-count concentration supplies the polynomial counts and
geometric scale internally in `RandomOutgrowthProfile.lean`. Root-count
asymptotics are supplied by the proved real Laplace profile. The finite mesh,
pressure, and source-survival transfers discharge the final height comparison.

The real and complex finite martingale moment inequalities are derived from
an explicit scalar power remainder, rather than assumed from an external
citation. Reachable-state and averaged-increment versions are distinguished;
the random profile in the one-step bound is replaced by its exact expectation
only after integration. The real normalizer logarithm has an explicit
quadratic error bound, and the profile exponent supplies a moment order with
summable polynomial decay. The actual epidemic normalizer asymptotics are now proved by
`path_observedNormalizer_log_concentration`. The real lower profile asymptotics
are also proved; the stronger complex nonvanishing limit remains open.
`Model/RealNormalizer.lean` identifies the real product exactly and
`Model/BirthHarmonic.lean` relates its birth-reciprocal sum to the harmonic
boundary term and total reciprocal-count sum, with quadratic error.
`Model/TotalProfile.lean` proves the full-tree generating-function expectation
and a first-moment height-tail bound from the final product.

The active population has a uniform positive linear lower bound on each
compact interval strictly between zero and fluid extinction, on survival to
the horizon. This follows from fixed-time concentration and finite grids, not
an assumed functional limit. The early killed geometric potential supplies
whole-path lower-count probability bounds and reciprocal-square tail control.
The late reciprocal sum divided by $\log n$ and the complete reciprocal-square
sum divided by $\log n$ tend to zero on endpoint activity. Sharp early-count
upper and lower geometric estimates admit slopes arbitrarily close to
$(\lambda-1)/(\lambda+1)$. Harmonic squeezing now proves the full reciprocal
coefficient $(\lambda+1)/(\lambda-1)$, and hence the normalizer coefficient
$\gamma(w-1)$, for every fixed $w\geq1$ at every strictly intermediate
macroscopic horizon. No additional stochastic hypothesis remains in this result.
This route uses the finite count kernels and does not verify the manuscript's
stronger cited functional fluid theorem.

`pathMeasure_positive_eventWord_bound` averages arbitrary uniform conditional
bounds over the finite observed event-word partition. Applying it to the exact
positive-profile expectation proves `path_normalizedLaplace_log_upper`.
Applying it to the total tree profile, including recovered vertices, proves
`path_height_div_log_upper`: on endpoint activity, pre-cutoff height has upper
coefficient $\gamma e^{z_\lambda}$. Both estimates concern the actual epidemic
path law. The finite mesh upper/lower comparisons, interior mesh selection,
and root-count transfers from real Laplace asymptotics are also proved.

The real lower-profile proof is complete. A fixed-fraction cutoff shortcut
was investigated and rejected because it leaves a fixed exponent loss. The
successful route uses uniform polynomial normalizer bounds, finite moment
tails, Jensen comparison between nearby positive tilts, and the growing cutoff
$\lfloor\log N\rfloor$. Its logarithm is negligible relative to $\log N$.
A finite tilt induction proves the lower estimate uniformly over good positive
event words; finite partition averaging supplies the actual epidemic law.
The initial cutoff and all product constants are fixed before the population
limit. The resulting `evolve_activeWeight_log_concentration` has only the source
rate scaling and the stated interior time/tilt restrictions as hypotheses.
This proof does not assert the stronger complex nonvanishing theorem or
validate the source's local-profile and urn arguments.

## Paper-route work in the continuation

The new work supplements the preserved main-theorem proof rather than replacing
its exports. `Analysis/LambertBounds.lean` proves the two explicit principal-branch
bounds. `Analysis/LambertCritical.lean` then proves the appendix's curvature,
convexity, boundary, existence, uniqueness, and crossing argument. The proof
changes for the second bound and the negative near-one value are recorded below.
`Analysis/PhaseRegularity.lean` proves that the preserved coefficient is $C^1$
on $(1,\infty)$ and is not $C^2$ at the critical parameter. The two first
derivatives match there; their second derivatives differ by an explicit positive
multiple of the squared difference between the two optimizing tilt derivatives.
Strict convexity of the critical gap proves that this difference is nonzero.

`Model/Urn.lean`, `Probability/UrnProducts.lean`, and `Probability/UrnLimits.lean`
construct the actual general two-colour urn and prove `prop urnes` by the paper's
bounded-martingale and second-moment route. Integer increments at least $-1$ may
vary arbitrarily subject to positive totals. Both colours must initially be
present for the equivalences. The ordered product limit exists even when its
squared-ratio series diverges; reaching total one is handled explicitly. The
Bernoulli law has exactly the initial red fraction as its parameter.
`Probability/UrnDraws.lean` records the draw colour as well as the red count,
proves that projecting the kernel gives the original urn update, and proves
both convergences of `lem:convergence proportion urn` to one measurable limit.
This also handles zero increments, when the colour cannot be recovered from
the count history. `Probability/MartingaleStrongLaw.lean` supplies a proved
strong law for bounded martingale differences: reciprocal weighted sums have
bounded second moments and converge almost surely, then summation by parts
and Cesàro convergence remove the weights. This replaces the source's cited
conditional Borel–Cantelli ratio argument.

`Analysis/ComplexNormalizer.lean` proves the complex logarithm remainder bound,
finite product identity, uniform summability on a common disk, and analyticity
of the limit. `Model/ComplexNormalizer.lean` applies these to the actual prescribed
count-word factors, including the physical cutoff and a safe cutoff common to
all tilts in a compact set. This proves the deterministic analytic part of the
paper's normalizer argument. Centered reciprocal-sum convergence, reciprocal
square summability, and count divergence are explicit hypotheses where used;
their random count-word versions and weak uniformity in the epidemic parameter
are not claimed proved.

`Model/ComplexProfileMoments.lean` proves the finite complex moment comparisons
on the complete prescribed-history law, with an arbitrary starting cutoff and
its random prefix. `Analysis/ComplexMomentExponent.lean` selects one moment
order, complex radius, and strict summability margin for every parameter above
a fixed lower endpoint. These results implement the deterministic part of the
complex increment/comparison route. They do not establish the random cutoff
tightness or common stochastic bounds in the corresponding numbered statements.

`Probability/KernelTrajectory.lean` constructs the genuine infinite process by
Ionescu--Tulcea, proves its finite-time laws, its full-history conditional
expectations, and martingale identities. A deterministic shift of the filtration
retains the original random prefix. No infinite process or convergence law is
postulated. `Model/KernelTrajectoryPrefix.lean` proves that the whole finite
prefix has the existing finite-history law, including the joint law of two
comparison times.

`Model/InfiniteProfile.lean` constructs the infinite shifted complex martingale
for a fixed prescribed word and proves almost-sure convergence to a measurable
limit from summability of the explicit increment bounds. Count/product power
bounds with exponent below $-1$ are sufficient. The polynomial specialization
uses $1\leq\lVert w\rVert$; the summability formulation allows arbitrary
complex $w$. These are conditional, pointwise results on the actual infinite
tree-history law, preserving the random prefix. They do not establish the
stochastic count-word hypotheses or uniform convergence in tilt or parameter.
`Model/InfiniteProfileLp.lean` uses the full-prefix marginal to transfer the
finite two-time moment bound to this infinite law. Fatou's lemma gives
$L^p$ convergence to the same measurable almost-sure limit, with polynomial
sufficient conditions as a corollary. The summation is over all one-step
increment bounds directly, replacing the paper's dyadic-block step; its
Fatou mechanism is retained.

`Probability/SourceWeakProfile.lean` closes the standalone weak-profile result
for arbitrary permitted source times and rates, with finite or infinite upper
endpoint and the exact non-strict survival event. It also proves the vanishing
empty-bin probability and the surviving preterminal-height coefficient. These
closures use the inherited real-Laplace proof. The stronger local Fourier
profile theorem is proved later in this continuation; the joint unscaled
early-height limit is proved in cylinder-event form, with functional weak-limit
packaging still open.

## Main theorem: completed integration

The final exports are:

- `HeightPaper.mainTheorem : HeightPaper.MainTheoremStatement`.
- `HeightPaper.main_limit`, for every rate sequence with the scaled limit.
- `HeightPaper.main_limit_of_asymptotic`, using the paper's asymptotic equivalence.

The actual Laplace-profile limit supplies the bin, tail, and low-bin root counts.
The fresh-outgrowth estimates and interior finite meshes prove the
surviving-height estimate. The source-cutoff transfer accounts for activity at
$K-1$ versus $K$, retaining the source quantifier order: for each tolerance,
every sufficiently late fixed cutoff works. The resulting statement is

$$
\mathbb P\left(E_{n,\delta}\cap\left\{\left|\frac{\operatorname{Height}(T_n)}{\log n}-\kappa(\lambda)\right|\geq\varepsilon\right\}\right)\longrightarrow0.
$$

The cutoff may depend on the tolerance but not on $n$. The proved survival
probability and early-extinction height negligibility then give the Bernoulli
mixture. The stronger unscaled early-height limit is proved separately in
`EarlyHeightConditionalLaw.lean`; it is not needed for this main-theorem proof.
No estimate is supplied by an
axiom, an unproved assumption bundle, or an isolated conditional reduction.

## Corrected coupling, distinct from the printed lemma

**The authorized corrected coupling is proved and integrated.** The exports are
`HeightPaper.CorrectedCouplingStatement`, `HeightPaper.correctedCouplingTheorem`,
and `HeightPaper.correctedCoupling_canonical` in
`HeightPaper/CorrectedCouplingTheorem.lean`. `CorrectedCouplingForSource` exposes
all the conclusions, rather than bundling an assumed stochastic estimate.

For $N\geq1$, put $S_0=N$ and $S_j=N+\sum_{i=1}^{j}X_i$. The corrected event is

$$
\mathcal E^\star=
\left\{\forall k\geq1,\quad
\left(\forall\,0\leq j<k,\ S_j>0\right)
\Longrightarrow p\leq r_k(X_1,\ldots,X_{k-1})\leq q\right\}.
$$

The bounds include the terminal recovery when extinction occurs, and impose
nothing after extinction. This strengthens the printed hypothesis. The
printed lemma remains false, as certified by
`CouplingEndpointCounterexample.lean`; its statement in the TeX has not been
changed for this correction.

For every $1/2<p\leq q<1$, one constant $C=C(p,q)>0$ is chosen **before** the
root count, root index, source law, recovery-rate version, and height. On the
common paired-uniform probability space, the theorem constructs measurable
variables for the complete binary word, the countable middle forest, and
two families of finite ordered tree shapes. It proves:

- the exact **joint** law of the word and middle limit forest equals the
  source word with the Algorithm 1 forest driven by independent parent
  uniforms; `correctedCouplingMiddle_source_joint_law` additionally identifies
  the entire chronological finite-state trajectory jointly with the word;
- the lower and upper tree families have the respective product laws of
  genuine geometric($q$) and geometric($p$) Bienaymé trees, with independence
  within each family; independence between the two families is not claimed;
- the middle is almost surely a rooted forest: its roots are distinct, every
  nonroot has a unique parent, all vertices are reachable from roots, and
  directed cycles are excluded; infinite degree and infinite components are
  permitted outside $\mathcal E^\star$;
- almost surely on $\mathcal E^\star$, root-preserving injective maps preserve
  all parent edges from the lower forest into the middle and from the middle
  into the upper forest. `RootedForest.Embedding.mapsTo_component` makes these
  embeddings explicitly componentwise for the same indexed roots;
- with root height zero, for every component and every real $h\geq0$,

$$
\frac1C(1/q-1)^h\leq
\mathbb P(\operatorname{Height}(\underline T^i)\geq h)
\leq\mathbb P(\operatorname{Height}(\overline T^i)\geq h)
\leq C(1/p-1)^h.
$$

Recovery-rate hypotheses in the general export are precisely the cylinder
identities defining conditional recovery probabilities. They do not require
independence of the source word. `correctedCoupling_canonical` discharges
these hypotheses for **every** binary source probability measure using
`sourceRecoveryRate`; null prefixes are totalized by zero. The corrected event
is almost surely unchanged when an admissible rate version is changed on
null prefixes.

The implemented proof has the following checked parts.

| Part | Main modules and exports |
| --- | --- |
| Source law and corrected event | `CorrectedCouplingSourceEvent`, `CorrectedCouplingEmittedLaw`; canonical conditional cylinder ratios and the full emitted-word law |
| Causal construction and rejection | `CorrectedCouplingFiniteState`, `CorrectedCouplingClock`, `CorrectedCouplingPastAcceptance`, `CorrectedCouplingPastUpper`, `CorrectedCouplingAcceptedPairLaw`; exact countable coding, fresh-coordinate independence, and rejection weighted by a full past event |
| Complete middle law | `CorrectedCouplingLogicalKernel`, `CorrectedCouplingJointHistory`, `CorrectedCouplingJointKernel`, `CorrectedCouplingReferenceHistory`, `CorrectedCouplingTokenLaw`, `CorrectedCouplingMiddleLaw`; all three next-event branches and uniqueness of complete joint cylinder laws |
| Finite ordered shapes | `CorrectedCouplingAddresses`, `CorrectedCouplingPlaneValidity`, `CorrectedCouplingAddressUpdates`, `CorrectedCouplingPlaneUpdates`, `CorrectedCouplingPlaneFreeze`, `FinitePlaneShape`; injective addresses and exact updates, excluding root parent totalization values from child sets |
| Complete bounding-tree laws | `PlaneCompletionCompatibility`, `PlaneCompletionPotential`, `CorrectedCouplingForestPotential`, `FreshBinaryIntegral`, `CorrectedCouplingPotentialExpectation`, `CorrectedCouplingTerminalMass`, `CorrectedCouplingShapeLaw`, `CorrectedCouplingShapeBranching`, `CorrectedCouplingBoundingTreeLaw` |
| Height tails | `FiniteShapeHeight`, `CorrectedCouplingHeightTail`, `CorrectedCouplingHeightComparison`; actual tree-height tails, integer thresholds and real-threshold extension |
| Limits and embeddings | `CorrectedCouplingStableRanks`, `CorrectedCouplingLimitCode`, `CorrectedCouplingChronologicalEmbedding`, `CorrectedCouplingPlaneEmbedding`, `CorrectedCouplingRootedSandwich`, `CorrectedCouplingForestValidity` |

The completion-potential argument proves the mass of every entire finite
ordered forest, not merely its cardinality or height. If component $t_i$ has
$|t_i|$ vertices, the mass at recovery parameter $a$ is

$$
\prod_{i<N}a^{|t_i|}(1-a)^{|t_i|-1}.
$$

Normalization comes from the actual terminating construction. This mass
factorization proves the product law of the components. The first-child
fixed point then proves the full conditional joint branching law and its
identity with the concrete iid potential-offspring construction. Generic
plane-tree and Bienaymé utilities were adapted from the local `freezing1`
project into `HeightPaper/Combinatorics/`, with the same pinned environment
and no new package dependency. Global birth labels are used only for the
coupling embeddings; their component laws are not asserted to be iid.

**Proof correspondence and departures.** The shared-threshold construction,
active-set sandwich, rejection after the full observed history, clock
divergence after upper extinction, and time-changed joint-law induction are
checked. The argument is developed directly for all $N$, whereas the paper
spells out $N=1$. The general fresh-coordinate and weighted-cylinder proofs
replace informal conditional-probability manipulations and supply the
continuation after extinction. In the branch outside the bounds, the middle
and upper parent ranks use the same fresh uniform; the manuscript chooses an
additional independent parent draw. Their required laws are nevertheless
proved on the complete probability space before imposing the favorable event.

The completion potential replaces the paper's appeal to Theorem 2 of
`BBKK23+` to identify uniform attachment with freezing as a Bienaymé law;
that external theorem's proof has **not** been checked. Upper extinction is
proved first by a strong law, then used for the potential's bounded-convergence
argument. The height-tail bridge uses the empty-level recursion from the
first-child fixed point instead of identifying every generation-count
marginal. This supplies the same exact height tail used in the comparison.
Stable chronological ranks, cofinal event times, and explicit inverse
embeddings transport the shared-label inclusions to the source middle
limit. No inclusion of canonical sibling-address sets is assumed.

The two clauses of the corrected target have no remaining proof obligation.
This does not certify the false printed event. Statement correspondence was
**self-reviewed** against the TeX statement and proof, including the terminal
step, arbitrary $N$, full joint law, internal family independence, finite and
infinite carriers, rooted edges, and the order of the constant's quantifiers.
At that completion stage no independent reviewer or Palomar deposit checker
was invoked. The later all-results audit below adds an independent statement
review of this coupling certificate.

Current complete integration: `lake build` passed with **4378 jobs**. Earlier
coherent batches also checked accepted-pair kernels, the complete middle law,
terminal masses, genuine branching laws, height comparisons, and the frozen
exports with only `propext`, `Classical.choice`, and `Quot.sound`. The final
export and frozen-export axiom batch is recorded in the validation section.

## Statement audit of all 31 numbered results, 2026-10-30

The current TeX was independently inventoried and compared with its original
tracked version where corrections were relevant. There are exactly 31 numbered
result environments, including the lemma without a label at line 1435. The
existing inventory below remains the single result-by-result coverage record;
its statuses now reflect this audit.

Three delegated reviewers reconstructed the premises, conclusions, standing
assumptions, and quantifier order from the TeX, then inspected the Lean types
and their semantic definitions. Their groups covered the early/fluid results,
the stochastic controls and finite moments, and the analytic/urn results. The
early-results reviewer also independently checked both main theorems and the
corrected coupling. The coordinator separately checked these main interfaces,
the source probability conventions, and the convergence discrepancy below.
This is a fresh independent source review, not reuse of the earlier self-audit.

**Current verdict after repair: 25 entries match the source statements and
6 match explicit statement corrections or endpoint conventions. No numbered
entry remains partial.** The initial audit found 24 source matches, the same
6 corrections/conventions, and the full-time convergence gap described below;
that gap has now been closed. Differences only in
proof strategy, such as a completion potential or a real-Laplace argument, do
not count as statement corrections. Likewise, fixing a formula in the proof of
a true statement does not make the statement itself a corrected theorem.

### Completed repair of full-time almost-sure uniform convergence

The source `proposition cv unif martingale`, lines 2451–2463, explicitly asks
for almost-sure convergence uniformly on each compact subset of
$\mathcal V(\lambda)$ for the entire time sequence. The convention at line 1363
adds this almost-sure assertion to $o_{\mathbb P}(1)$. On survival, the target is

$$
\sup_{z\in K}|M_k(z)-M_\infty(z)|\longrightarrow0
\quad\text{almost surely as }k\longrightarrow\infty.
$$

The initial audit correctly identified that full-time conditional convergence
in probability, almost-sure dyadic uniform convergence, and pointwise
almost-sure convergence did not by themselves certify this conclusion. The
former Complete verdict was withdrawn at that point.

`Probability/LocalProfileAlmostSureCompact.lean:92` now proves
`localProfile_ae_canonical_complex_compact_limit_ae_physical` with the exact
full-time almost-sure compact-uniform conclusion. Its only premises are
$\lambda>1$, compactness, and inclusion in the existing full complex moment
domain. The same `localAnalyticProfileLimit`, prescribed trajectory measure,
source count-word survival event, and normalizer cutoff are retained. One
parent-trajectory null set works for all tilts in the fixed compact and the
whole physical time sequence. The empty compact is included.

The implemented repair follows `MARTINGALE_AS_ROADMAP.md`:

| Part | Proved exports |
| --- | --- |
| Subsequence and scalar-distance upgrade | `Probability/MartingaleSubsequence.lean`: `tendsto_of_subsequence_of_dist_limits`, `ae_tendsto_of_subsequence_of_dist_limits`, `martingale_ae_exists_norm_sub_initial_limit` |
| Function-valued profile martingale | `Model/ContinuousProfileMartingale.lean`: `continuousPrescribedProfile_martingale`, `continuousMap_tendsto_iff_uniformlyOn` |
| Boundary estimates and full-time upgrade | `Model/AnalyticProfileAlmostSure.lean`: `continuousProfile_integral_norm_sub_le`, `prescribedTrajectory_ae_full_time_of_dyadic` |
| Actual local windows and compact cover | `Probability/LocalProfileAlmostSureCompact.lean`: `localProfile_ae_canonical_complex_disk_limit_ae`, `localProfile_ae_canonical_complex_compact_limit_ae_physical` |

For a fixed surrounding moment window, the actual profile restricted to an
inner closed disk is a martingale with values in its continuous-function
space. Its one-step means follow by continuous linear evaluation from the
existing source-kernel identity. Finite-prefix laws and the circle integral
estimate turn the existing $p$th-moment difference bound into a uniform $L^1$
bound for each fixed dyadic anchor. The real-valued norm distance from that
anchor is a nonnegative submartingale, so its almost-sure convergence follows
from the scalar martingale convergence theorem. A countable intersection over
anchors is taken before the candidate limit. The existing dyadic uniform
convergence identifies each scalar limit; an epsilon/triangle argument then
gives full-time norm convergence to the same canonical limit. A finite disk
cover supplies every fixed compact, and the finite cutoff shift is removed.

No general Banach-valued martingale convergence theorem, Radon–Nikodym
hypothesis, maximal estimate, or Borel–Cantelli argument is assumed. All
helper premises are discharged by the actual count-word and tree construction.
The denominator still starts at $J$ when the martingale starts at an anchor
$j\geq J$; the random pre-cutoff tree is preserved.

An independent reviewer read the new four modules against the source statement
and its probability convention. The review checked all physical times, the
complete complex domain, the canonical limit, both almost-sure quantifier
levels, the random prefix, the denominator cutoff, and the empty compact, and
found no missing hypothesis or source discrepancy. The coordinator separately
checked the assembled type and current axiom dependencies.

This is an alternative proof of the source assertion. The paper invokes
Proposition 3.6 and Lemma A.3 of `Sen21`; the proof of those external results
has not been formalized by this repair. Existing probability-convergence and
main-theorem exports remain available, with no additional hypotheses.

### Explicit corrections and conventions in the six relevant entries

1. **`lem:couplage` (537):** the corrected event includes the terminal
   recovery. The printed event remains false. `CorrectedCouplingTheorem.lean:63`
   proves both clauses, including the joint source word/forest law, complete
   iid Bienaymé laws, rooted edge embeddings, and one height constant before
   the root count, source law and real height. The TeX was not amended here.
2. **`lem:dangling` (961):** the certified components are fresh outgrowths,
   obtained by deleting edges already present at the cutoff. The literal
   all-descendants definition at TeX 945–949 is incompatible with the claim
   that those descendants are all born after the cutoff. This correction was
   already stated in this report and the recommendations, but the inventory
   now labels it explicitly. The TeX definition still needs this amendment.
3. **`lem:eventE` (1012):** the range is
   $0<\eta<\min(m_\lambda,1-m_\lambda)$, in place of the original unrestricted
   $\eta>0$. The current TeX already contains this correction. The certified
   good cutoff states are supported, eventually nonempty, have conditional
   mass tending to one, and satisfy a uniform success-probability bound.
4. **`lem:sum 1/Sni is gamma log k` (1649):** the formula agrees literally
   for $1\leq k\leq\lfloor nt\rfloor$. At $k=0$, Lean defines the centered
   empty sum as zero through its totalized logarithm. The paper includes zero
   but does not define $\log0$; use the positive-time range, or explicitly use
   $\log\max(1,k)$. This convention was previously recorded and is now visible
   in the inventory status.
5. **`proposition majoration increments Mn` (2063):** the certified range is
   $k<\lfloor nt\rfloor$, since the next increment needs positivity at $k+1$.
   The current TeX still includes the endpoint. The previous inventory claim
   that the TeX had already been corrected was erroneous; only the formal
   statement and the recorded correction use the valid range.
6. **`lemme z n proche de z` (2159):** the condition
   $A_n\leq\lfloor nt\rfloor$ has already been added to the current TeX and is
   in the certificate. The simultaneous conditional moment, one moment order
   chosen before all tolerances, and weak parameter uniformity were checked.
   The sign repair in its proof is a separate proof correction.

The changes to the limiting constant in `lemme majoration C`, to the reciprocal
sum proof's Euler–Mascheroni/survival terms, to a critical power-sum estimate,
and to an urn indexing display are **proof corrections**. Their theorem
statements are preserved. In particular, the reciprocal-sum random limit and
its stochastic uniformity are now proved; the old remark that the random-walk
lemma remained unformalized was obsolete and has been corrected.

### All-results audit evidence before the repair

- `lake build` succeeded with **4378 jobs**, including the entry point and all
  affected consumers. Its output contains existing linter/style warnings,
  not proof errors.
- A combined temporary probe checked **90 distinct declarations** covering all
  31 entries and their semantic bridges. Every axiom closure is contained in
  `propext`, `Classical.choice`, and `Quot.sound`; one declaration is axiom-free.
- A separate probe compiled the literal asymptotic-rate main theorem and the
  expanded strong-profile bad-event statement, including its exact lattice
  equation, zero-mass case, logarithmic correction and non-strict survival
  event. Its 15 axiom queries bring the combined total to **95 distinct
  declarations**, all within the same permitted foundations.
- No Lean source, TeX source, configuration or pinned dependency was edited by
  the initial audit. The later repair adds the four proof modules listed above. The documentation changes correct coverage and preserve the
  substantive differences from the paper's arguments. Temporary probes are
  removed after their evidence is recorded.

The audit checks statement correspondence and current Lean proof evidence. It
does not certify every argument of the paper: the alternative routes and
unverified external arguments listed below remain explicitly distinguished.
No Palomar deposit verification or independent kernel replay was performed.
The numerical approximation to the critical parameter and other non-numbered
claims retain their separately stated coverage; they are not added to the 31.

## Private Palomar-compatible interface (31 October 2026)

The preparation selects `thm:main`, `thm:profil`, and the parameter-uniform
paragraph immediately after `thm:profil`. `Challenge.lean` is a 293-line,
Lean-core/Mathlib interface with concrete definitions and exactly three deliberate
theorem proof holes. `Solution.lean` re-exports `mainTheorem`,
`strongProfileTheorem`, and `uniformStrongProfileTheorem` unchanged. Frozen
exports, mathematical objects, source manuscript and dependency pins are
preserved. Two proof-valued constructor arguments (the PMF normalization in
`eventChoice` and the index bound in `FinitePath.eval`) use explicit Mathlib
terms so the Challenge does not inherit module-specific tactic auxiliaries.
Kernel-checked `rfl` examples establish definitional equality with the former
objects. Auxiliary-proof cache resets reproduce original module boundaries in
the standalone Challenge. These are representation changes, not new premises
or changes to the epidemic law.
All 31 numbered-result obligations retain their existing completed status.

The extracted definitions and statements received a separate AI semantic review
against the implementation and blue manuscript; no discrepancy was found. Local
compilation of Challenge and Solution passed. The repository includes a fresh
build/axiom-audit workflow and a manually dispatched private Linux Comparator
workflow, with independent Challenge compilation, Lean/NanoDa replay and
positive/negative controls. Run-specific mechanical claims require their actual
exact-commit reports; merely preparing these workflows is not a passing run.
See `publication/PALOMAR.md` for the protocol and retained scope limitations.

The maintainer selected Apache-2.0 for the formalization. Manuscript and
third-party terms remain separate in `NOTICE`. The repository stays private;
no official full Palomar preflight, intake or registration has been performed.

## Numbered result inventory

The source contains 31 numbered result environments: 2 theorems, 8 propositions,
20 lemmas, and 1 corollary. **All 31 have completed certificates: 25 match the
source statements and six use the explicit corrections or endpoint conventions
listed above.** Line numbers refer to the supplied revised TeX source retained
in the private archive. “Complete” refers to the mathematical result under the
stated correction or convention; the proof correspondence section distinguishes
alternative proofs. The proposed Palomar comparison selects the two main
theorems and the following parameter-uniform strengthening.

| TeX label or location | Line | Coverage | Lean certificate and statement correspondence |
| --- | --- | --- | --- |
| `thm:main` | 240 | Complete; source statement audited | `mainTheorem : MainTheoremStatement`, `main_limit`, `main_limit_of_asymptotic`; all stochastic inputs discharged. |
| `thm:profil` | 382 | Complete; source statement audited | `strongProfileTheorem : StrongProfileStatement` proves the fixed-parameter source theorem, including exact lattice equality, zero-profile failure, the $-\frac12\log\log n$ correction, uniformity over every compact admissible tilt set, and non-strict source survival. `uniformStrongProfileTheorem : UniformStrongProfileStatement` also proves the separately stated weak compact-parameter uniformity. |
| `lem:couplage` | 537 | Complete; audited corrected terminal event | `HeightPaper.correctedCouplingTheorem : CorrectedCouplingStatement` proves both clauses with $\mathcal E^\star$, including the terminal recovery. `correctedCoupling_canonical` applies to every binary source probability measure. The middle has the exact joint source word/forest law; the actual bounding families have full iid geometric Bienaymé laws; root-preserving parent-edge embeddings hold componentwise almost surely on the corrected event; the same $C(p,q)$ covers arbitrary $N$, source law, root, and nonnegative real height. `CouplingEndpointCounterexample.lean` certifies the printed endpoint obstruction. The paper's time-changed construction is checked, with the explicit shared-parent-rank change outside the bounds; the completion potential replaces the cited external tree-law theorem. |
| `lem:limflu` | 771 | Complete; source statement audited | Final joint certificate: `sourceLocalFluidJoint_tendstoInDistribution` in `Probability/LocalFluidDistribution.lean:99`. Actual cutoff survival probability, fixed-time active count location, terminal size on survival, and early-height logarithmic negligibility proved. The surviving preterminal-height coefficient is proved by `sourceCutoff_height_log_concentration`. `FunctionalFluid.lean` proves uniform preterminal infectious and susceptible fluid convergence under endpoint activity and both exact-source-survival mixtures. `TerminalEventMixture.lean` proves the terminal event-count and susceptible-fraction mixtures and a joint probability estimate for the two floor-time trajectories: infectious uniformly on every compact interval, susceptible uniformly on $[0,t_\lambda]$, for every fixed source cutoff $\delta\in(0,1)$. `EarlyBranchLocalLaw.lean` proves fixed-prefix tree coupling and the explicit local survival weight $1-1/\lambda$ for arbitrary asymptotic rates. `EarlyBranchJointLaw.lean` proves joint common-space convergence in probability of the finite first-extinction time and height, clipped to zero on survival through a fixed floored preterminal horizon, and transfers this to setwise convergence of the corresponding genuine event-count and height pair under the original epidemic path law. `EarlyBranchJointLaw.lean` also identifies the source cutoff survival event with the local infinite-survival event up to vanishing probability. `EarlyFluidJointLaw.lean` transfers the two-coordinate compact-time fluid concentration to the local event on the common uniform space and proves simultaneous convergence with the stopped early time-height pair. On the original full epidemic path, it proves setwise convergence of the intermediate early pair, asymptotic agreement of its survival coordinate with the source cutoff event, compact-time concentration of both fluid coordinates selected by that early coordinate, and joint cylinder-event probabilities for every set of early pairs. `EarlyBranchJointLaw.lean` and `EarlyFluidJointLaw.lean` also prove that extinction exactly at the floored horizon has vanishing probability. `EarlyRealThresholdLaw.lean` identifies the TeX real-threshold clipped extinction time exactly on supported full paths, proves setwise convergence of the real-threshold time/survival pair with Bernoulli weight $1-1/\lambda$, and proves joint convergence of that pair and the strict-cutoff early height under the original path law. `EarlyHeightJointLaw.lean` assembles the surviving and extinct logarithmic preterminal-height estimates and gives joint cylinder-event probabilities with both compact-time fluid trajectories, all three early coordinates, and the logarithmic height, using the paper's real-threshold indicator. `GeometricBranching.lean` now proves that the supercritical geometric generation-extinction CDF, normalized by its eventual extinction probability $1/\lambda$, equals the subcritical reciprocal-mean CDF at every generation. `EarlyLocalHeightPotential.lean` identifies the local tree-height event with the terminal value of the geometric potential, its initial value with that CDF, and verifies its exact one-step harmonicity at the local birth probability. `HeightPotentialBounds.lean` supplies the exact upper CDF estimate restricted to paths that stay above a susceptible barrier, for a finite-epidemic approximation of the local process. `EarlyLocalTreeKernel.lean` proves the local birth/parent kernel law on the actual two-uniform space, exact constant expectation of the height potential at every finite time, vanishing of the potential on infinite-survival paths by the strong-law active-count bound, and its terminal indicator on finite extinction. Dominated convergence identifies the local early-height CDF on extinction with the supercritical geometric generation-extinction CDF; dividing by the proved extinction mass $1/\lambda$ yields the exact subcritical reciprocal-mean Bienaymé height CDF asserted in the manuscript. `EarlyHeightConditionalLaw.lean` transfers this to the original epidemic path law and proves convergence of the conditional strict-cutoff early-height CDF on the exact source early-extinction event, for every integer threshold and arbitrary admissible rate sequence. It also gives setwise convergence of the joint early extinction-time/height pair under that conditioning. `EarlyJointDistribution.lean` proves genuine weak convergence in distribution of the early time/survival/height triple on the countable discrete product space. `EarlyHeightJointDistribution.lean` also proves the joint CDF of that triple and the normalized cutoff height for every discrete-triple event and every threshold below zero, strictly between the extinct and surviving height values, or above the surviving height value. `EarlyHeightMarginalDistribution.lean` upgrades the normalized cutoff-height coordinate to genuine weak convergence to its two-atom limit, using the real-threshold survival indicator under the original full-path law. `VaryingSourceStability.lean` proves small-perturbation stability for random variables on changing probability spaces; `EarlyHeightFullJointDistribution.lean` applies it to prove genuine weak convergence of the early time/survival/height triple jointly with normalized cutoff height in the original product space. `EarlyFluidFiniteJointDistribution.lean` adds genuine weak convergence at arbitrary fixed infectious and susceptible observation times jointly with that triple and height. `EarlyFluidVectorJointDistribution.lean` extends this to every finite vector of observation times. `CompactFluidDistribution.lean` proves the full joint functional result under the original finite epidemic law for every compact infectious horizon $C\geq0$. `CountableProductInMeasure.lean` and `LocalFluidDistribution.lean` package those horizons into a single joint random element with the topology of uniform convergence on compact infectious intervals, together with the susceptible path uniformly on $[0,t_\lambda]$, the early triple, and normalized cutoff height. Convergence is proved in measure on the exact common birth-parent coupling and transferred to weak convergence under the original path law. |
| `prop:lc` (i)–(iii) | 837 | Complete; source statement audited | `existsUnique_criticalParameter`, crossing inequalities, `mainCoefficient_eq_sup`, branch formulas, `growthFactor_mul_exp_profileRoot_le_mainCoefficient`. |
| `lem:Lambert` (i)–(ii) | 860 | Complete; source statement audited | `principalLambert_lower_bound` and `principalLambert_parameter_lower_bound` in `Analysis/LambertBounds.lean`; exact principal-branch range and both endpoints included. Part (ii) uses a stronger reciprocal bound. |
| `prop: profil faible` | 901 | Complete; source statement audited | `source_weakProfile_bin`, `source_weakProfile_tail`: arbitrary source time and asymptotic rates, exact non-strict survival cutoff, arbitrary finite upper endpoint and infinity. Empty bins have vanishing probability. Proof uses the alternative real-Laplace route. |
| `lem:dangling` | 961 | Complete; audited corrected fresh-outgrowth definition | Audit: fresh outgrowths exclude old cutoff edges; this explicitly corrected definition is used in `Model/Outgrowth.lean` and the exports below. `source_dangling_all_conditional` and `source_dangling_all_probability` prove the finite-bin, infinite-tail, and low-depth clauses under the actual cutoff-state law, with the exact non-strict source survival event, arbitrary asymptotic rates, all sufficiently small fixed cutoffs, and every positive height tolerance. Good cutoff states are in the actual support and source survival set, have conditional mass tending to one, and give a uniform vanishing bound on the conditional height deviation. The proof uses the real-Laplace root-count profile and direct geometric outgrowth bounds in place of the whole-tree sandwich used by the source; the corrected coupling is now certified separately. |
| `lem:mt` | 980 | Complete; source statement audited | `parameter_mul_fluidSusceptible_extinction` and the root/branch characterizations. |
| `lem:eventE` | 1012 | Complete; audited corrected eta range in current TeX | The TeX definition, statement, and uses now take $0<\eta<\min(m_\lambda,1-m_\lambda)$. `eventually_sourceSurvival_lateRecovery` proves the path probability estimate for every sufficiently small $\delta$. `eventually_lateRecoverySupportedGoodCutoffStates_conditional` gives nonempty sets of genuinely reachable good cutoff states, conditional mass tending to one, a threshold tending to zero, and continuation success probability at least one minus that threshold for every good state. `eventually_lateRecoverySupportedGoodSuccessInf_tendsto_one` verifies the infimum formulation of the source's minimum. Exact cutoff-state and endpoint reductions link these events to the paper's path law. |
| Unlabelled lemma, `eq: limite fluide en proba` | 1435 | Complete; source statement audited | `paper_improved_fluid_lemma` combines the already proved weakly uniform survival-indicator comparison with the full unabsorbed finite-walk fluid limit, uniformly over real times in any compact nonnegative interval and weakly uniformly over compact supercritical rate sets. `GhostBudgetStart.lean` through `GhostBudgetClockLimit.lean` realize the continued susceptible budget as the marginal of an active-padded epidemic, prove its positive susceptible barrier, identify its exact harmonic clock with the stopped invariant, and transfer stopped martingale concentration. `FiniteBudgetFluidLocation.lean` proves fixed-rate pointwise location; `FiniteBudgetFunctionalFluid.lean` proves fixed-rate functional convergence. `FiniteBudgetCompactClock.lean`, `FiniteBudgetCompactFluidLocation.lean`, and `FiniteBudgetCompactFunctionalFluid.lean` make the bounds common to all rates between the compact endpoints, upgrade to uniform time, transfer to the raw infectious walk, and account for real-time flooring. The proof uses a padded epidemic and common variance bound in place of the manuscript's cited distributional fluid-limit route. |
| `lem:Mk is a martingale` | 1508 | Complete; source statement audited | `prescribedPath_normalized_condExp`, `prescribedPath_normalized_integral`, `prescribedPath_profile_martingale`, `prescribedPath_shifted_profile_martingale`. Finite event-word conditioning is also proved by `pathLaw_filter_eventCylinder`; full-word conditional-law bridges are checked in the moment entries below. |
| `lem:tension de M lambda` | 1625 | Complete; source statement audited | `positiveReciprocal_uniform_tight`, together with its almost-sure common finite envelope, proves the equivalent supremum-event formulation on the actual iid uniform space, uniformly for every parameter above a supercritical lower endpoint. |
| `lem:convergence sum 1/Sk - c log k towards rv` | 1629 | Complete; source statement audited | `ae_tendsto_finiteLocalCenteredReciprocal`, `finiteLocalCenteredReciprocal_uniform_convergence`, and `localBirthReciprocalLimit_uniform_tight` use the same explicitly defined measurable limit. Almost-sure convergence holds for each parameter; convergence in probability and limit tightness are uniform over every supercritical half-line bounded away from one. |
| `lem:control on the Si` | 1639 | Complete; source statement audited | `coupled_count_ratio_uniform_tight` and `walkGap_uniform_tight` prove both controls on the actual common uniform space. Time is inside probability; for each admissible compact parameter set and time horizon, the constants are chosen before the population and individual parameter. |
| `lem:sum 1/Sni is gamma log k` | 1649 | Complete; audited with explicit time-zero convention | Audit: the literal formula is certified for $k>0$; the empty sum at $k=0$ is assigned zero, as explicitly recorded. `finiteCenteredReciprocal_uniform_tight` proves the unscaled centered estimate on the actual common uniform space, with full-horizon survival, all prefixes simultaneously, exact rate $\lambda/n$, and weak compact-parameter uniformity. |
| `lem:JnJ` | 1659 | Complete; source statement audited | Exact measurable source cutoffs and their uniform survival-clipped tightness are proved. `safeCutoff_survival_disagreement_uniform` proves equality of the clipped cutoffs with probability tending to one, weakly uniformly in the parameter. |
| `lemme majoration moment martingale` | 1968 | Complete; source statement audited | `finiteProfileMoment_uniform_bound` proves the random-word Jensen bound with one tight multiplier before all times, bounded complex weights, moment orders, populations, and rates. `finiteShiftedRankProfile_moment_condExp_eventWord_eq` identifies the prescribed moment almost everywhere with conditional expectation given the full infinite binary event word. `conditioned_profile_moment_eq` identifies conditioning on each positive finite count cylinder under the original epidemic law. `finiteProfileMoment_uniform_bound_original` transfers the uniform bad-moment probability to the original path law using the observed event word. The theorem covers every compact source tilt set by a bound on $\|e^z\|$; it proves the inequality in the source's nonzero-normalizer domain. |
| `lem:asymptotics Cnkz` | 1999 | Complete; source statement audited | `finiteNormalizer_errors_uniform_tight`, `finiteNormalizerLogError_uniform_tight`, and `finiteNormalizerMomentLogError_uniform_tight`: exact safe products, post-event counts, canonical complex logarithms, and one error bound before time, tilt, moment order, population, and individual parameter. |
| `proposition majoration increments Mn` | 2063 | Complete; audited corrected endpoint, TeX still unchanged | `finiteProfileIncrementMoment_uniform_exp` proves the same-history finite-tree moment with exact $\log k$, jointly in time, tilt and moment order, weakly uniformly in the parameter. The valid range is $k<H$, because the increment uses the count at $k+1$; this correction is in the formal statement and report, while the current TeX still includes the endpoint. `finiteProfileDifferenceMoment_condExp_eventWord_eq` identifies the moment with full binary-event-word conditional expectation. `finiteProfileIncrementMoment_uniform_exp_original` transfers the bad-moment probability to the original epidemic path through its observed event word. The proved range $0\le\Re z\le2z_\lambda$ covers the printed compact $K\subset\{0<\Re z<z_\lambda\}$. |
| `corollaire M nt proche de M An` | 2126 | Complete; source statement audited | `finiteProfileDifferenceMoment_shrinking_tilts` supplies one moment order before all tolerances and the vanishing random conditional same-history moment on shrinking compact tilt sets. `finiteProfileDifferenceMoment_condExp_eventWord_eq` identifies conditioning on the full binary word, and `finiteProfileDifferenceMoment_shrinking_tilts_original` transfers the uniform tail probability to the original epidemic path. Its $p\in(1,2)$ is stronger than the source's $p\in(1,2]$. |
| `lemme z n proche de z` | 2159 | Complete; audited corrected horizon in current TeX | `FiniteLocalProfileMovingTime.lean` proves convergence in probability of the coupled finite unshifted profile at diverging preterminal times. `FiniteNormalizerPrefixModulus.lean` transfers its modulus through the random cutoff. `FiniteShiftedProfileMovingModulus.lean` proves the shifted profile difference tends to zero in joint probability over shrinking complex compact sets, identifies exact parent-uniform moments with the prescribed-word kernel, and bounds all higher two-tilt conditional moments in a strict-decay window. `ConditionalMomentTransfer.lean` proves truncation, Fubini, and Markov transfer simultaneously over an uncountable tilt set. `FiniteShiftedProfileConditionalMoment.lean` chooses one $p\in(1,2]$ before error thresholds and proves the random conditional $p$th moment of the shifted **difference** tends to zero uniformly over compact rates and all compact $K_n$ with diameter tending to zero, on survival and $J^n\le A_n$. `ConditionalParentExpectation.lean` and `FiniteShiftedProfileConditionalExpectation.lean` establish global integrability and, by the tower property, identify each fixed-tilt parent integral almost everywhere with conditional expectation given the **full binary event word**. `FiniteShiftedProfileConditionalExpectation.lean` identifies the moment with conditioning the original epidemic path law on a positive finite count cylinder. `FiniteEventWordCoupledLaw.lean` transfers every finite birth-word event jointly with survival to the observed event word on the original path. `FiniteShiftedProfileOriginalMoment.lean` proves the uniform bad-moment probability bound under the original epidemic path law. `FiniteShiftedProfileSourceBridge.lean` proves that the manuscript's compact-parameter and little-o diameter hypotheses imply the uniform original-path theorem, with one moment order before all error thresholds. The finite cylinder formula and the almost-everywhere full binary-word conditional-expectation identity identify the source conditional moment; the simultaneous bad-moment event supplies a common version over the compact tilt set. This is an alternate proof and does not validate the manuscript's two-term expectation estimates. The TeX statement now explicitly requires $A_n\le\lfloor nt\rfloor$ to define the preterminal profile; its normalization decomposition was corrected for a reversed profile difference. |
| `lemme majoration C` | 2314 | Complete; source statement audited | Audit: the lemma statement is preserved; the missing factor in the source proof is a proof correction. `localNormalizer_ae_source_asymptotic`, `localNormalizer_compact_uniform_convergence`, and `localNormalizerCorrection_compact_uniform_tight` use the same jointly measurable analytic correction for the actual iid event word. Exact products and weak parameter uniformity are proved on the larger safe half-plane. |
| `lemme majoration M` | 2388 | Complete; source statement audited | `localComplexGrowthPowerBad_uniform_tight` proves both conditional moment bounds on the actual random count word, simultaneously for every initial profile size, all $p\in[1,2]$, all $k\ge J$, and every complex $z$ with $\Re z<z_\lambda$, weakly uniformly over $\lambda\ge\lambda_0>1$. The dyadic difference has the exact power $k^{\alpha+1}$; the full profile moment has $k^{\max(\alpha+1,0)+\eta}$ for every $\eta>0$, which certifies the printed $o_\mathbb P(1)$ exponent slack. The bad event is measurable. The endpoint $p=1$ uses an ordinary triangle sum; a harmonic majorant retains the critical logarithm before the power slack absorbs it. $\alpha=\gamma(e^{p\Re z}-1-p(\Re(e^z)-1))-p$. |
| `proposition cv unif martingale` | 2451 | Complete; full-time almost-sure source statement audited | `localProfile_ae_canonical_complex_compact_limit_ae_physical` in `Probability/LocalProfileAlmostSureCompact.lean:92` proves almost-sure convergence uniformly on every fixed compact of the full complex moment domain for all physical times, to the same canonical analytic limit. The real norm-distance submartingales at countably many dyadic anchors converge under the proved boundary moment bounds; the existing dyadic uniform limit identifies the full limit. A finite cover gives arbitrary compacts. The former gap identified by the all-results audit is closed; independent statement review found no discrepancy. This replaces the source appeal to the external analytic-convergence lemma, whose proof was not checked. |
| `prop cv lp martingale` | 2469 | Complete; source statement audited | `localProfile_ae_complex_compact_uniform_lp` proves that every fixed compact $K\subset\mathcal{V}(\lambda)$ has one common order $q>1$ for which the conditional $q$th moment of the canonical-limit difference tends to zero uniformly over $K$, on almost every surviving count word. `localComplexCompactLpBad_uniform_tendsto` makes the probability of failure tend to zero uniformly over parameters $\lambda\ge\lambda_0>1$ and all initial profile sizes, with the local cutoff bounded by the comparison time. The proof chooses local moment orders on finitely many disks and takes their minimum using $L^p$-to-$L^q$ interpolation; the uniform multiplier follows from common count-word controls. Batched axiom queries report only `propext`, `Classical.choice`, and `Quot.sound`. |
| `prop: convergence vers M infini` | 2496 | Complete; source statement audited | `FiniteShiftedLocalIdentity.lean` proves the exact finite/local shifted-profile identity when the count-word prefix and safe cutoff agree. `FiniteShiftedLocalPrefix.lean` proves that agreement through the random local cutoff with uniformly vanishing error on joint survival. `FiniteShiftedLocalJointProbability.lean` combines these with the moving-time unshifted comparison to prove joint convergence in probability of the finite shifted profile at every diverging preterminal time to the canonical local analytic limit at each admissible positive real tilt, uniformly over compact rates. `ProfileLimitMomentBound.lean`, `LocalProfileLimitMoment.lean`, and `LocalProfileLimitParentMoment.lean` pass the finite conditional moment-tail envelope to that canonical limit and prove a uniform higher conditional moment under the actual parent-draw law. `FiniteLocalShiftedMomentUniform.lean` and `FiniteLocalShiftedConditionalMoment.lean` prove conditional moment convergence at each fixed admissible positive real tilt, uniformly over compact rates and diverging preterminal times, with one moment order fixed before all error and probability tolerances. `FiniteLocalShiftedComplexConditionalMoment.lean` combines this with the finite analytic modulus at one shared moment order and proves simultaneous conditional moment convergence over every shrinking compact complex tilt family at the exact observation horizon. `FiniteLocalShiftedPairWord.lean` and `FiniteLocalShiftedWalkConditioning.lean` identify the sigma algebra of the two complete signed walks with that of the two birth words, and identify every bounded truncation with ordinary conditional expectation. `FiniteLocalShiftedExtendedConditionalMoment.lean` proves the measurability and defining set-integral identity of the complete nonnegative conditional moment. `FiniteLocalShiftedExtendedConvergence.lean` makes this moment finite with high probability and proves its uniform convergence on local survival, which implies the source's indicator-weighted claim. The proof compares directly to the fixed real-center local limit, bypassing the source's four-term intermediate-time decomposition. |
| `lemme limite martingale non nulle z fixe` | 2553 | Complete; source statement audited | `localAnalyticProfileLimit_ae_pos_all_real` proves strictly positive conditional values at every fixed real tilt, with one outer almost-sure count-word event. The exact positive prefix mean and singleton tail zero–one law are proved. The stronger simultaneous no-zero result also gives the countability conclusion. |
| `prop: M infini ne s'annule pas` | 2566 | Complete; source statement audited | `localAnalyticProfileLimit_ae_nonzero_all_real`: one outer almost-sure surviving count word, then one inner almost-sure parent sample before all real tilts. The concrete parent sampler has the exact full prescribed trajectory law. Compact zero-hit events are tail events; a random-closed-set argument replaces subtree independence and random-zero enumeration. |
| `lem:convergence proportion urn` | 3118 | Complete; source statement audited | `ae_convergence_proportion_and_draws`: both the count fraction and empirical recorded-draw fraction converge almost surely to one measurable $[0,1]$-valued limit. Zero increments are retained. Draw-frequency proof uses a proved bounded martingale-difference strong law. |
| `prop urnes` | 3146 | Complete; source statement audited | `hasLaw_limit_bernoulli_iff` and `interior_probability_pos_iff` for arbitrary admissible integer increments, including removals and visits to total one. Exact Bernoulli parameter is the initial red fraction. |

Other retained claims are the coupling identities at `eq couplage freezing` and
in Section 4, the stronger parameter-uniform martingale statement after line 2467, total-size
scaling, and the phase-transition claim that the coefficient is $C^1$ but not
$C^2$ at the critical parameter. The differentiability claim is now proved by
`contDiffOn_one_mainCoefficient` and
`not_contDiffAt_two_mainCoefficient_critical`; the stronger assertion that the
derivative is not differentiable at the critical parameter is also proved.
The numerical approximation $\lambda_c\simeq1.8038$ is not certified. Maximum degree is stated as
future work, not a claimed theorem.

## Proof correspondence and substantive departures

1. **Lambert representation.** The installed Mathlib has no general Lambert
   function used here. The roots are defined by their inverse equations and
   their required ranges; existence and uniqueness are proved. The exported
   principal-branch bridges justify the paper's specific values. A total global
   Lambert function is not defined. The new `LambertBounds.lean` proves both
   inequalities for every principal-branch inverse pair in their stated ranges.
   Part (i) follows the inverse-exponential comparison, with a simpler derivative
   factorization. Part (ii) first proves the stronger estimate
   $W(-\lambda e^{-\lambda})\geq-1/\lambda$ and derives the printed bound;
   the paper's Taylor-polynomial proof of that inequality is not certified.
2. **Critical parameter.** The inherited proof studies
   $q(z)=ze^{-z}+(1-z)\log(1-z)$ on $(0,1)$, proves its unique interior zero
   using derivative monotonicity and Rolle's theorem, then transfers it through
   $\lambda=e^{-z}/(1-z)$. This proves `prop:lc` without the appendix's Lambert
   bound. The new `LambertCritical.lean` also checks the appendix's two
   curvature formulas, their convexity signs, boundary continuity, strict
   convexity, and the crossing argument. Its
   `existsUnique_criticalParameter_from_lambert` is independent of the inherited
   $q$-proof. A rigorous negative value at $5/4$ replaces the paper's near-one
   asymptotic calculation. The preserved critical parameter is identified with
   the zero of this new proof. The subsequent regularity proof differentiates
   both actual branch formulas, glues their equal first derivatives, and proves
   a strictly positive jump of the second derivatives. It verifies the retained
   $C^1$ but not $C^2$ claim without relying on a numerical critical value.
3. **Fluid curve.** The positive inverse clock is used to prove the ODE and
   extinction identities directly. The result of `lem:mt` is checked, but the
   manuscript's displayed Lambert-composition shortcut is not the formal proof.
   `FunctionalFluid.lean` obtains preterminal uniform convergence from the
   proved one-time state concentrations, the one-event count bound, and a finite
   grid. Early-extinction event-count tightness supplies the zero branch, and
   the exact cutoff-activity comparison transfers the resulting mixture to the
   manuscript's terminal-tree survival event. `TerminalEventMixture.lean`
   extends the infectious estimate to every event time and the susceptible
   estimate through $t_\lambda$ by bounding the late path between cutoff and
   terminal values. Uniform continuity converts these to the manuscript's
   floor-time processes, uniformly on every compact real-time interval for the
   infectious coordinate and on $[0,t_\lambda]$ for the susceptible coordinate.
   It proves both process estimates for every fixed source cutoff by showing that
   two cutoff classifications disagree with probability tending to zero. It also
   proves the macroscopic two-branch terminal event-count and final susceptible-fraction
   limits. `EarlyBranchLocalLaw.lean` proves fixed-prefix event-word and tree-shape
   agreement on the common birth and parent uniform space for arbitrary rate
   sequences satisfying the paper's scaling. `EarlyBranchJointLaw.lean` assembles
   the early time-height pair and its setwise path-law limit. `EarlyFluidJointLaw.lean`
   proves simultaneous common-space early-pair/fluid control and joint cylinder
   probabilities under the original epidemic law. `EarlyRealThresholdLaw.lean`
   checks the real-threshold early time and survival indicator against the
   supported path argument, proves their setwise limit and the paper's Bernoulli
   weight, and combines them with the strict-cutoff early height and both
   real-threshold-selected fluid estimates. `EarlyHeightJointLaw.lean` adds the
   logarithmic preterminal-height coordinate to the same joint cylinder-and-tube
   estimate. The local early-height variable is explicit. `EarlyLocalTreeKernel.lean`
   proves its exact conditional CDF: given finite extinction, it equals the
   height CDF of a subcritical geometric Bienaymé tree with mean $1/\lambda$.
   The proof identifies the actual two-uniform local process with a
   constant-rate tree kernel, derives the geometric potential identity at
   each finite time, and uses the strong-law active count and dominated
   convergence at the extinction limit. This establishes the paper's
   geometric-law assertion by an alternative argument. `EarlyHeightConditionalLaw.lean`
   transfers that exact CDF to the genuine finite epidemic under the paper's
   source survival event: the conditional strict-cutoff early-height CDF
   converges to the subcritical geometric Bienaymé CDF for each integer
   threshold and every scaled-rate sequence. The full early time/height pair
   also converges setwise under conditioning on that exact extinction event.
   `EarlyJointDistribution.lean`
   packages the three unscaled early coordinates as genuine weak convergence
   of random elements on their countable product space. The external
   theorem invoked in the manuscript was not independently checked.
   `CompactFluidDistribution.lean` now packages the joint functional limit
   with both trajectories on every compact horizon under the original law.
4. **Alternative weak-profile route.** Real exponential tilting gives finite
   upper and lower bin-mass inequalities in `Probability/ProfileBounds.lean`.
   `ProfileAsymptotics.lean` transfers assumed real Laplace limits into
   exponential bin bounds; `ProfileConvergence.lean` proves deterministic
   logarithmic bin and tail convergence for a differentiable rate with strictly increasing
   derivative, including bins with infinite upper endpoint. The exponential-rate specialization gives precisely the exponent
   $f_\lambda(x)$ when the total-mass exponent is one. The lower bound uses a
   narrower bin approaching the requested lower endpoint. This can avoid the
   stronger complex Fourier local-profile theorem when proving only
   `prop: profil faible`. Transfer to convergence in probability is now proved for varying finite
   measures, including restriction to survival. `Model/WeakProfile.lean`
   applies it to actual active-bin and tail counts. `Model/LowProfile.lean`
   combines the tail exponent below one with proved linear active population
   to derive exponent one for low bins. The epidemic
   real Laplace asymptotics are now proved by finite tilt induction and word
   averaging. This completes the main theorem's profile input. It does not
   cover `thm:profil`, validate its Fourier argument, or prove its complex
   nonvanishing claim. `SourceWeakProfile.lean` now exports the standalone
   source proposition and transfers the empty-bin conclusion to exact survival.
   Interior bins approaching the profile edge also give the surviving
   preterminal-height coefficient, without asserting the full joint limit.
5. **Final proof.** The main proof's initial tightness/mixture reduction and
   deterministic mesh approximation are checked. The fresh-outgrowth maximum
   is proved for supported histories. Actual fluid/count, real profile, and
   fresh-component tail estimates now discharge the entire main proof.
   Their alternative routes are distinguished below from the source
   functional fluid, complex profile, and full tree-coupling arguments. The
   endpoint and notation corrections are retained explicitly.
6. **Stochastic fluid route.** The harmonic-invariant variance and barrier
   argument, geometric infectious-count test functions, and inverse-clock
   compactness prove the fixed-time count and survival results directly from
   the finite epidemic kernel. This bypasses the cited BBKK23+ proof and does
   not validate its full functional/joint convergence theorem. The continuation
   proves compact-time probability tubes for both fluid coordinates under the
   original path law, then uses a bounded-Lipschitz stability argument for
   changing path spaces to prove weak convergence of the early triple, cutoff
   height, and every finite vector of fluid observations. The new
   `CompactFluidDistribution.lean` uses the exact common-uniform realization
   and the compact-time probability tubes to prove convergence in measure of
   all these coordinates together, with the two trajectories in uniform
   topologies on $[0,C]$ and $[0,t_\lambda]$ for every $C\geq0$. It transfers
   this to weak convergence under the original finite epidemic law. The
   countable family of compact horizons represents the source's locally
   uniform topology. This does not check the BBKK23+ argument cited in TeX.
7. **Outgrowth probability route.** A bounded height-CDF potential on actual
   selected fresh components replaces the full branching-tree coupling for
   finite tail estimates. The construction of the paper's infinite coupled
   trees and their independence is not checked by this alternative.
8. **Moment inequality.** A scalar power remainder and real/imaginary
   decomposition prove finite martingale moment inequalities with explicit
   harmless constants. This replaces the cited inequality. Polynomial
   finite-word moment tails and their use in the real lower-profile induction
   are also proved. The new complex finite-word difference estimates retain the
   random prefix at an arbitrary normalizer cutoff. Their deterministic
   exponent is summable with one common choice of moment, radius, and margin.
   The infinite-history construction and full-prefix identity now transfer
   these bounds to an actual infinite martingale. Real and imaginary
   martingale convergence supplies its almost-sure limit. Direct summation of
   the two-time tails and Fatou gives same-$p$ convergence, replacing the
   dyadic-block summation in the source. These results remain conditional on
   explicit deterministic word bounds; uniform complex martingale convergence
   is not claimed.
9. **Urn appendix.** The new concrete two-colour chain follows exactly the
   stated draw/update rule for integer increments at least $-1$. Its bounded
   martingale converges on a constructed infinite trajectory. Bounded
   convergence transfers the finite second-moment identity to the limit, and
   the infinite-product argument proves both criteria of `prop urnes`. This
   checks the paper's route for that proposition. The first part of the
   preceding convergence lemma is also checked.
10. **Model representation.** Infection-order labels and a finite probability
   kernel implement the paper's embedded chain and attachment rule. No
   exponential-clock/Poisson-contact process has been constructed, so a formal
   continuous-time SIR equivalence theorem is not claimed.

The cited source `BBKK23+` was identified as *Uniform attachment with freezing*,
Annals of Applied Probability (2025), particularly Theorems 2–4 and 23–24;
[the authors' primary PDF](https://igor-kortchemski.perso.math.cnrs.fr/articles/AAP2190.pdf)
was consulted for dependency identification. None of its stochastic theorems is
imported as an axiom or treated as a formalized result.

## Source issues relevant to coverage

- The first main-proof bin starts at height zero, but its displayed lower bound
  includes the positive base contribution $\gamma\log n$. That lower bound does
  not follow from the stated low-height dangling estimate. Interior bins can
  supply the lower bound; the low bin needs only an upper bound.
- If $1/\eta$ is integral, the last mesh point is $z_\lambda$, outside the strict
  domain required by `lem:dangling`. Interior meshes avoid this endpoint. The
  formal proof uses these interior meshes and supplies their stochastic
  bin estimates from the proved real Laplace profile.
- Fresh outgrowths must exclude old edges. Full descendant subtrees can overlap
  when two cutoff vertices are ancestors of one another. The formal components
  use the first old ancestor and are proved disjoint.
- The notation table uses a nonnegative-time infimum for extinction, which
  would select zero. The formal definition follows the strictly positive-time
  infimum in the main fluid section.
- Real-threshold and floored-threshold versions of `lem:limflu` require a
  boundary/rounding argument. They are not treated as definitionally identical.
- The original `lem:eventE` quantified every $\eta>0$, but the denominator
  $1+m_\lambda-\eta$ may vanish or be negative. The Lean theorem
  `not_lateRecoveryEvent_of_large_eta` proves that the stated event is empty
  when $\eta>1+m_\lambda$. The TeX definition, lemma, and dangling-tree proof
  have been corrected to use $0<\eta<\min(m_\lambda,1-m_\lambda)$, the range
  used by the certified proof.
- The geometric-tail formula at line 729 equals one at index zero, so it
  describes height at least that index for root depth zero; the displayed
  strict inequality has an apparent integer shift. Formal tails use
  height $\geq h$ and CDFs height $<h$. Logarithmic height scaling is unaffected.
- For empty profile bins, Lean's real logarithm is totalized by
  $\log 0=0$. At the interior tilts used here the target bin exponent is
  positive, so the proved convergence forces the probability of an empty bin
  on activity to vanish. The standalone source-profile wrapper now also proves
  this characterization on the exact cutoff-survival event.
- Maxima over empty active bins need a convention. Natural-valued height
  suprema in the formal model use zero for the empty set. Equality at the
  extinction cutoff can make this relevant even on the non-strict survival event.

- In the proof of `lemme majoration C` (line 2346), the centered limit
  $Z(\lambda)$ is independent of $z$. The limiting constant must contain
  $(e^z-1)Z(\lambda)$, not $Z(\lambda)$. The formal analytic correction retains
  this factor, including the finite-prefix subtraction.
- The reciprocal-sum proof's final definition of $Z$ (line 1777) omits
  the earlier Euler–Mascheroni constant and the survival indicator multiplying
  $Z'$. With the printed definition of $Z''$, consistent bookkeeping is
  $Z=\mathbf{1}_{\{S_i>0\ \forall i\}}(Z'+\gamma\gamma^{\mathrm{EM}})+Z''$.
  The same proof's display for the fluctuation variable $Y$ (line 1750) has
  $\mathbb P(Y\geq A)$ where the following event is $Y\leq A$. These are
  source-proof corrections. `LocalReciprocalLimit.lean` now constructs the
  measurable stochastic limit and proves its almost-sure convergence, uniform
  probability convergence, and uniform tightness. The downstream normalizer
  is supplied with this proved limit and does not use the erroneous display.
- The urn conditional-mean display at line 3129 uses $X_k$ once where its
  denominator and the update rule require $X_{k+1}$. The formal kernel uses
  the increment for the next step consistently.
- The proof of `lemme majoration M` states a power-sum estimate for every
  real exponent which misses logarithmic growth at exponent $-1$. Its
  displayed small exponent slack can absorb that logarithm. The formal proof
  retains the factor $1+\log k$ at the boundary and proves its absorption
  into $k^\eta$ for every $\eta>0$.
- The event in `lem:couplage` checks $p\le r_k\le q$ only for
  $1\le k\le\tau_N-1$. For $N=1$, choose a process whose first step is
  certainly a recovery. Then $\tau_1=1$ and the event is certain, but the
  middle tree has only its root. A geometric offspring law with $q<1$ gives
  the lower tree a positive chance of having a child, so its claimed inclusion
  is impossible. `no_geometric_offspring_of_ae_childless` certifies the
  offspring-law obstruction. The source statement needs the terminal-step
  condition. Its authorized correction is now certified separately by
  `correctedCouplingTheorem`; the printed statement remains false.
- In the increment proposition at line 2063, the printed range includes
  $k=\lfloor nt\rfloor$, although positivity is assumed only through that
  time and the next increment needs time $k+1$. The formal finite sum uses
  $k<N$, exactly the range needed for the subsequent comparison corollary.

See `MANUSCRIPT_RECOMMENDATIONS.md` for suggested exposition changes. The TeX
source has not been edited for this coupling issue.

## Validation and review

### Full-time almost-sure profile convergence: final verification, 2026-10-30

- Focused builds passed for the generic subsequence bridge, the
  continuous-function-valued martingale, the boundary integral/full-time
  bridge, and the local-window/compact assembly. The public entry point
  imports all four modules.
- Full `lake build` passed with **4383 jobs**, including affected consumers.
  New modules have no linter warnings; remaining messages are replayed
  pre-existing style and unused-argument warnings.
- A fresh probe importing `HeightPaper` compiled the exact full-time
  compact-uniform statement with the two ordered almost-sure quantifiers and
  the existing canonical limit. Its grouped axiom queries checked **21
  declarations**: new helpers, both new local/compact results, the existing
  compact probability and conditional-moment results, nonvanishing, both
  strong-profile exports, the corrected coupling and its canonical form,
  and the four frozen main-theorem exports. Every dependency is among
  `propext`, `Classical.choice`, and `Quot.sound`. An earlier coherent batch
  for lots 1–3 checked seven helpers with the same permitted dependencies.
- Independent statement review found no new premise, domain restriction,
  loss of almost-sure uniformity, or substitution of the limit. The only
  suggested wording fix was to describe the estimates as uniform L1 bounds;
  this was applied to the module documentation.
- Toolchain, Lake configuration, dependency pins, TeX, and frozen export
  source files were preserved. Whitespace checks include the new untracked
  modules. Temporary probes are removed after recording their evidence.

This closes the last obligation in the existing 31-entry numbered inventory.
It does not assert that all originally printed statements are true: the six
explicit corrections/conventions remain distinguished, including the false
printed coupling and its separately certified replacement. No Palomar deposit
check or independent kernel replay was performed.

### Corrected coupling: final verification, 2026-10-30

- The focused `lake build HeightPaper.CorrectedCouplingTheorem` succeeded,
  followed by a full `lake build` with **4378 jobs**, including the public
  entry point and affected consumers. All completed coupling modules are
  imported through `HeightPaper.lean`.
- A fresh Lean probe importing `HeightPaper` compiled an exact-type example
  of `correctedCouplingTheorem : CorrectedCouplingStatement` and the canonical
  arbitrary-source specialization. The latter explicitly keeps the constant
  before the root count and source probability measure.
- One final grouped `#print axioms` audit checked both corrected exports and
  their statement definitions, the complete middle joint laws, full bounding
  Bienaymé product law and independence, rooted sandwich, source and coupled
  middle validity, real-height comparison, and all four frozen main-theorem
  exports. Every dependency was among `propext`, `Classical.choice`, and
  `Quot.sound`. `RootedForest.Embedding.mapsTo_component` needed no axioms.
- Statement correspondence was self-reviewed against the TeX statement and
  construction, including the terminal recovery, arbitrary root count,
  source dependence, full tree laws, finite and infinite carriers,
  componentwise rooted parent edges, and uniform constant. This is distinct
  from the axiom audit. No independent reviewer or Palomar deposit checker
  was invoked for this coupling certificate.
- Final whitespace and proof-hole scans passed. Lean/Mathlib pins and Lake
  configuration have no changes; the four frozen export source files were
  not edited by this work. Temporary audit probes were removed after the
  evidence was recorded.

The two clauses of the authorized corrected coupling are complete. The
printed `lem:couplage` remains false; this certificate is explicitly for the
strengthened event stated above. The older verification sections below are
historical milestones, not current coupling obligations.

Inherited milestone verification of the requested main theorem, 2026-10-29:

- `lake env lean --version` reports Lean **4.35.0**.
- `lake build` succeeded with **3353 jobs**, including cached dependencies,
  after the final theorem, every maintained module, and affected consumers
  were integrated through `HeightPaper.lean`.
- A separate exact-type example with the source asymptotic-equivalence
  hypothesis compiled against `main_limit_of_asymptotic`.
- A temporary probe ran `Lean.collectAxioms` on **1598** accessible public and
  project-private declarations in the entry-point closure. Every axiom closure
  was contained in `propext`, `Classical.choice`, and `Quot.sound`.
- The same batch printed the axiom dependencies of the main theorem, its direct
  and asymptotic forms, actual upper/lower Laplace limits, uniform lower-profile
  induction, good-word controls, source-survival transfer, and height/mixture
  reductions. All used only the three permitted foundational axioms.
- A source scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, or
  `bv_decide` in maintained Lean code. Every maintained Lean module belongs to
  the entry-point import closure.
- SHA-256 comparisons with the setup baseline confirm the TeX, toolchain,
  `lakefile.toml`, and `lake-manifest.json` are unchanged.

These checks establish the implemented main theorem in the pinned Lean
project. They do not claim completion of the paper's other inventoried results.

Independent source review covered the exact main statement and final exports,
analytic constants and critical formula, deterministic fluid parameters/ODE,
finite kernel and path/cutoff semantics, full fresh-outgrowth decomposition,
parameter continuity, and normalized finite profile identities. Reviewers
checked the upper-profile and pre-cutoff height proofs for total-tree semantics,
logarithm positivity, and the extra time-horizon factor; checked uniform
normalizer constants for dependence on the word and horizon; and checked the
lower-profile induction, fixed initial cutoff, exact prefix law, finite tilt
grid, and final slope squeeze. The main exports preserve arbitrary allowed
rate sequences, the literal asymptotic-rate formulation, and the full Bernoulli
mixture. No unresolved main-theorem issue was found.

The real-profile route is a substantive alternative to the source's complex
martingale nonvanishing and urn proof. Infinite path-space conditioning,
complex local-uniform convergence, the full tree sandwich, and the other
listed obligations are not certified by the completed main theorem. No Palomar
deposit or separate external kernel-replay check has been performed.

## Continuation setup verification

Fresh checks in `height-paper-full`, 2026-10-29:

- `lake env lean --version` reports Lean **4.35.0**.
- `lake build` succeeded with **3353 jobs** using the copied dependency cache.
- A fresh temporary Lean probe imported `HeightPaper` and compiled examples
  checking `mainTheorem : MainTheoremStatement` and the exact asymptotic-rate
  statement of `main_limit_of_asymptotic`. Batched axiom queries for
  `mainTheorem`, `main_limit`, and `main_limit_of_asymptotic` each returned only
  `propext`, `Classical.choice`, and `Quot.sound`.
- All nine dependency checkouts match the revisions in `lake-manifest.json`.
- SHA-256 comparisons before and after the copy/build confirm that all 176
  original source, documentation, and skill files remain unchanged. All Lean
  files, the TeX source, toolchain, Lake configuration, dependency pins, and
  skill contents in the new project are identical to the milestone. Only
  `README.md`, `AGENTS.md`, this report, and `.agents/README.md` were adapted.
- Both independent Git repositories retain tag `main-height-theorem` at the
  inherited commit. The new project's dependency cache is a separate filesystem
  copy, with no link back to the milestone's mutable cache.

These are historical setup checks. Subsequent proof development and its
current verification are recorded separately below.


## First paper-route pass: verification and remaining obligations

Historical verification for commit `43e3f64`, before the stochastic-control
additions below, 2026-10-29:

- The full `lake build` succeeded with **3443 jobs**, including cached
  dependencies, after all new modules were integrated through `HeightPaper.lean`.
- A fresh probe imported the completed entry point and ran `Lean.collectAxioms`
  on **2765** accessible public and project-private declarations. Every
  transitive axiom closure was contained in `propext`, `Classical.choice`, and
  `Quot.sound`. The same batch printed the main exports, Lambert/critical and
  regularity results, complex normalizer and moment results, infinite prefix
  law, almost-sure/$L^p$ limits, both urn results, bounded-difference strong law,
  and exact source weak-profile/height statements; all used only those axioms.
- Exact-type examples compiled for the unchanged main theorem and its literal
  source rate-asymptotic hypothesis, the $C^1$ and non-$C^2$ assertions, and
  both urn convergences to the same measurable limit with the source indexing.
  An independent urn probe also checked the precise Bernoulli parameter and
  the literal product/summability equivalences.
- All **164** maintained Lean files belong to the entry-point import closure.
  The complete inventory of **31** numbered paper results is retained;
  **8** are marked complete. The additional unnumbered $C^1$ but not $C^2$
  claim is also proved.
- Focused checks and dependency builds cover the Lambert/critical/regularity
  chain, both complex-normalizer modules, finite complex moments, infinite
  trajectories and complete prefix marginals, almost-sure and $L^p$ profile
  limits, all urn modules, the bounded-difference strong law, and the exact
  source weak-profile/preterminal-height exports.
- Independent source review checked exact Lambert endpoints and inverse
  ranges; curvature and critical crossing; coefficient branch matching and
  the positive curvature jump; the urn kernel, product criterion, draw
  filtration and zero increments; the complete trajectory prefix law;
  cutoff and normalizer indices; random-prefix retention; uniform exponent
  quantifiers; the fixed-word Fatou argument; and the exact source cutoff
  and finite/infinite profile bins. No remaining defect was found in those
  implemented statements.
- Source scans found no `sorry`, `admit`, custom `axiom`, `native_decide`, or
  `bv_decide` in maintained Lean code. The TeX, toolchain, Lake configuration,
  dependency manifest, frozen exports, and their existing implementation files
  are unchanged from `main-height-theorem`. All nine dependency checkouts match
  the manifest revisions. The sibling `height-paper`
  repository remains clean.
- Markdown mathematics and the retained source inventory were checked. The
  manuscript observations are advisory; the TeX has not been edited.

Development first connected finite laws to infinite trajectories, then proved
the complete-prefix identity needed by two-time moment comparisons. This
avoids treating correct one-time marginals as a substitute for a joint law.
The draw-frequency proof was changed to a proved weighted-martingale strong law
when the available conditional Borel–Cantelli API did not provide the needed
ratio theorem. Zero increments required explicit recorded draws. Underconstrained
function/event inference caused elaboration timeouts; supplying explicit types
resolved them without raising heartbeat limits.

At that stage, the main missing input to the paper's profile route was the
stochastic, parameter-uniform control of count words, reciprocal sums, and safe
cutoffs. The following pass proves those controls. The subsequent analytic and
local-profile steps remain open, as detailed below.

## Uniform stochastic controls for the strong profile theorem

This pass completes all five technical lemmas at TeX lines 1625–1659. The
numbered inventory now records **13 complete results out of 31**. These are
unconditional estimates for the constructed stochastic processes; no count,
concentration, reciprocal, or cutoff hypothesis is left as an assumed input
to the five final results.

The construction uses one infinite sequence of independent uniform random
variables. `UniformWalk.lean` and `CountCoupling.lean` define the local walk and
the finite susceptible budget, prove parameter monotonicity and the walk
sandwich, and identify the absorbed counts with the stopped signed walk.
`CountCouplingLaw.lean`
proves equality of the **whole finite count-history law** with the epidemic
law at rate $\lambda/n$. This includes fresh-coordinate independence from the
entire past, not just matching one-time count marginals. The guarded birth rule
agrees almost surely with the source rule; its only endpoint distinction is
the null event that a uniform draw equals zero after susceptible depletion.

The completed results are:

- **Local reciprocal tightness.** `positiveReciprocal_ae_uniform_bounded` and
  `positiveReciprocal_uniform_tight` prove an almost-sure finite common bound
  and the equivalent supremum-tail formulation for $M(\lambda)$, uniformly for
  every $\lambda\geq\lambda_0>1$.
- **Local centered reciprocal limit.** `LocalReciprocalLimit.lean` chooses one
  measurable family `localBirthReciprocalLimit`. The finite-survival-gated sum
  converges to it almost surely for each fixed parameter and in probability
  uniformly for $\lambda\geq\lambda_0>1$. The same limiting family is uniformly
  tight. Its definition includes the survival indicator and Euler–Mascheroni
  correction omitted from the source proof's final expression.
- **Finite count and walk-gap controls.** `coupled_count_ratio_uniform_tight`
  proves the surviving count-ratio estimate. `walkGap_uniform_tight` proves
  tightness of $(S_k-S_k^n)/(1+k^2/n)$ simultaneously over all event times,
  uniformly over bounded nonnegative parameters and all $n\geq1$. The latter
  strengthens the paper's restricted time range.
- **Finite centered reciprocal sums.** `finiteCenteredReciprocal_uniform_tight`
  gives the unscaled $O_{\mathbb P}(1)$ bound with the exact coefficient
  $\lambda/(\lambda-1)$, survival through the full horizon, and all prefixes
  inside the probability. Constants are chosen before $n$ and the individual
  parameter in the prescribed compact set.
- **Safe cutoffs.** `SafeCutoff.lean` and `FiniteSafeCutoff.lean` define the exact
  measurable source cutoffs and prove their safety and survival-clipped
  tightness. `safeCutoff_survival_disagreement_uniform` proves that the clipped
  finite and local cutoffs are equal with probability tending uniformly to
  one. Since these are integer-valued, this implies the stated convergence in
  probability. No tightness claim is made for the unclipped finite cutoff.

Additional controls include uniform early count barriers, vanishing
reciprocal-square tails on surviving histories, the local $k^{3/4}$ deviation
bound, exact short-prefix agreement, and weakly uniform survival-indicator
agreement (`uniform_survival_disagreement`). This last result proves the
survival component of the unlabelled fluid lemma at line 1435; it does not
prove its joint functional fluid convergence.

### Checked arguments and substantive route changes

- The local-walk strong law, centered Hoeffding bounds, summable deviation
  tails, and the paper's inverse-walk error bound by a multiple of $k^{-5/4}$
  are checked. Uniform boundedness of $M$ follows from a common eventual linear
  lower barrier and a finite initial segment. The paper's separate finite
  maximum-attainment argument and exact parameter-supremum identity are not
  used or certified.
- The centered harmonic series is proved through bounded martingale
  differences, $L^2$ tails, Fatou, and a Doob maximal bound, in place of the
  cited independent-series theorem. These bounds give the source's weak
  parameter uniformity; they do not assert an almost-sure supremum over
  parameters converges to zero.
- The finite count-ratio estimate uses the inherited finite-kernel barriers
  and a new compactness/sequential argument, rather than the source's
  lower-bias-walk survival comparison. Every needed arbitrary-rate-sequence
  estimate is supplied by the existing epidemic proofs.
- The walk-gap proof follows the source's independent Bernoulli domination,
  exponential bound, and quadratic-time blocking, with a looser valid
  constant. The denominator part of the reciprocal comparison follows the
  paper. The birth-indicator mismatch is bounded by Abel summation of the
  coupled gap, replacing the paper's weighted expectation calculation.
- Survival agreement uses a growing logarithmic prefix, its vanishing
  coupling error, and the proved late-extinction tail. Cutoff agreement then
  combines short-prefix equality, cutoff tightness, and survival agreement.
- The unscaled early time-height comparison constructs the first local and
  finite extinction times explicitly and couples their tree heights on a
  common birth-parent space. For varying rates, monotonicity of finite walk
  survival reduces indicator disagreement to a difference of marginal
  survival probabilities. The proof then uses fixed-prefix equality and the
  local late-extinction tail. Absorption identifies the stopped variables with
  genuine event count and tree height on the terminal finite path; the exact
  path law transfers their joint convergence to the epidemic. This checks the
  coupling route for these two observables; it does not yet check the paper's
  identification of $R$ with a conditioned geometric Bienaymé tree or the
  joint functional convergence attributed to the external theorem.
  The proof keeps the survival indicator in the finite-cutoff tail throughout.
- Independent source review checked the full-history law, stopped-walk
  identity, after-event reciprocal indices, centering coefficient, whole-time
  maxima, compact-set quantifiers, cutoff definition and strict safety, and
  the use of one measurable limit for all three local-limit assertions. The
  value at time zero is the empty centered sum, using Lean's `Real.log 0 = 0`;
  positive times and all asymptotic statements agree with the source.

The associated source corrections are recorded in
`MANUSCRIPT_RECOMMENDATIONS.md`; the TeX has not been edited.

### Verification at the stochastic-control milestone

Fresh checks after integrating the complete stochastic-control batch,
2026-10-29:

- `lake build` passed with **3509 jobs**, including dependencies and the
  library entry point. Focused checks and dependency builds passed for all
  20 new modules; all **184 maintained Lean modules** are in the entry-point
  import closure.
- A fresh probe imported the complete entry point and ran `Lean.collectAxioms`
  on all **3287 accessible public and project-private declarations**. Every
  transitive axiom closure was contained in the three permitted foundational
  axioms. The preserved `mainTheorem : MainTheoremStatement` type example
  also compiled against the current entry point.
- Batched axiom queries passed for the new final control exports, the full
  count-history law, survival and cutoff agreement, and supporting martingale
  and concentration estimates. Each used only `propext`, `Classical.choice`,
  and `Quot.sound`. Expanded source-type examples also checked the local
  reciprocal limit with the exact survival gate and corrected limiting
  expression.
- The TeX, toolchain, Lake configuration, dependency manifest, and frozen
  main-theorem file are unchanged from `main-height-theorem`. All nine
  dependency checkout revisions still match the manifest. The sibling
  `height-paper` repository remains clean.
- Source scans found no proof holes, custom axioms, `native_decide`, or
  `bv_decide` in maintained Lean files. Markdown math conventions, the full
  31-result inventory, and `git diff --check` passed. Independent review of
  the updated report found no coverage or correspondence overclaim.

## Strong profile: proved theorem and parameter-uniform strengthening

The exact target is recorded as `StrongProfileStatement` and
`UniformStrongProfileStatement`. Both retain the source lattice equality,
normalization, logarithmic correction, and survival event. A zero profile is
explicitly a failure event, so Lean's totalized logarithm cannot hide it.
Both are proved. The uniform proof chooses its probability and logarithmic
envelope constants before the individual epidemic parameter and population.

The stochastic count controls now supply the actual finite normalizer's
simultaneous complex error bounds and moment-ratio bounds. The local
normalizer has one jointly measurable correction, analytic on the entire safe
half-plane, with almost-sure uniform asymptotics and weakly parameter-uniform
convergence and tightness. Independent source audits checked these conclusions,
including the post-event index and the correction factor missing in the TeX.

The actual finite prescribed-tree law now satisfies uniform moment, increment,
and shrinking-tilt tail estimates. The comparison uses two observations of one
history and keeps the full-horizon safe cutoff. Exact finite-cylinder
conditioning identities are proved. The single-profile and two-time moments
are also identified almost everywhere with conditioning on the complete
infinite binary event word. Their uniform bad-moment and tail events transfer
exactly to the original epidemic path law on survival.
The Jensen bound allows weights of modulus less than one, as required by the
negative-real-part portion of the source domain. The increment endpoint is
corrected to $k<H$ because its denominator uses the count at $k+1$.

The finite coupled proof of `lemme z n proche de z` now obtains its conditional
$p$th-moment conclusion from joint small-tilt convergence in probability and a
uniformly tight conditional moment of a strictly higher order. A three-range
truncation, Fubini, and Markov's inequality make this transfer uniform over the
whole compact tilt set. This proves a stronger diameter condition
$\mathrm{diam}(K_n)\to0$ for the finite coupling. It does not check the
manuscript's separate two-term normalizer/profile expectation estimates; the
algebraic sign correction in that proof remains independently recorded. The
parent integral is now proved to be an almost-everywhere version of conditional
expectation given the full binary event word, by first conditioning on the
birth-uniform coordinate and then using the tower property and finite-word
measurability. On every positive finite event cylinder, the same integral is
the conditional moment under the original epidemic path law. The event that
this moment exceeds a threshold transfers exactly from the birth-uniform
coupling to the original path, with the event word read from count increments.
A compactness argument selects one lower supercritical rate, and the source's
little-o diameter condition implies the shrinking-diameter premise. The full
binary-word conditional expectation is identified almost everywhere on the
coupled space, while the finite count-cylinder law and event-word probability
transport identify its original-path formulation. This completes the lemma's
mathematical content through an alternate proof. It does not check the
manuscript's separate two-term expectation bounds.

For the actual local random word, the count and product hypotheses of the
pointwise almost-sure and $L^p$ limit theorem are discharged. One near-real
disk, moment order, and strict decay margin work above a supercritical lower
parameter. The random moment-tail multiplier is proved uniformly tight; its
mere almost-sure finiteness is not used as a uniform probability estimate.
These near-real results do not complete the larger complex-domain statements
of `lemme majoration M` or the full uniform martingale proposition.

Exact lattice Fourier inversion, its saddle-point factorization with the
varying amplitude retained inside the integral, and deterministic Gaussian
and cubic-error bounds are proved. The non-strict-survival/inactive-cutoff
boundary has uniformly vanishing probability. The remaining active-profile
estimate is an explicit hypothesis of the final boundary-transfer helper.

Additional checked components include the corrected disjoint-outgrowth
profile decomposition, the actual one-step urn expectation, Cauchy interior
control from boundary integrals, and analytic limits along dyadic times from
summable boundary moments. The latter route also yields local uniform
convergence in probability; it does not by itself certify the source's
all-time almost-sure uniform convergence.

Simultaneous nonvanishing is now proved for the canonical local profile on the
actual independent-parent sampler. The full finite-history and infinite
prescribed-tree laws of that sampler are identified. Exact ordered active
depth updates prove that resetting depths after any finite time changes
positive-real profiles by bounded positive factors, uniformly on every compact
tilt set. Thus each compact zero-hit event is a measurable tail event.
The positive prefix mean excludes a probability-one zero at each fixed tilt.
A random closed set with zero–one basic-open-set hit probabilities and
pointwise almost-sure absence must be empty almost surely. All probability-one
quantifiers precede the full real interval where required. Independent source
review approved this correspondence. This proves the numbered nonvanishing
lemma and proposition, bringing the complete inventory to **17 of 31**.

This continuation uses the paper's finite-depth reset and positive-mean ideas,
but replaces its two-subtree independence and random-zero enumeration argument
with the closed-set argument. Those bypassed arguments have not been certified.
The actual outgrowth decomposition and one-step urn law remain separately
checked components. For parameter-uniform comparison, work now uses the
equivalent unshifted profile near positive real tilts: the finite prefix
normalizer cancels exactly, avoiding discontinuities of the random cutoff.
This change of normalization does not change the physical profile or target.

A fresh integrated `lake build` passed with **3576 jobs**, and a fresh global
axiom probe checked **3911 accessible project declarations** in that entry
point, all using only the three permitted foundational axioms. The preserved
`mainTheorem : MainTheoremStatement` example and an independently spelled-out
simultaneous nonvanishing type also compiled. The batch includes the current
positive-mean, singleton zero–one, simultaneous positivity, finite Fourier
moment, product-probability, and finite disk-deviation exports. Subsequent modules
under development receive focused checks and dependency builds; they require
another complete integration check before a later verification claim.

### Remaining work

`thm:profil` is proved as `strongProfileTheorem : StrongProfileStatement`, and
its unnumbered parameter-uniform strengthening is proved as
`uniformStrongProfileTheorem : UniformStrongProfileStatement`.
The full stochastic tree sandwich, joint
functional fluid convergence, joint unscaled early-extinction limits, and
other inventory obligations remain open. No Palomar deposit or separate
external kernel replay has been performed.

The latest continuation discharges the compact lower-tail input from joint
almost-sure nonvanishing and analyticity. A countable dense subset of each
compact real tilt set makes its strict small-value event measurable; compactness
then excludes small values at every tilt on the surviving samples. Parameter
stability gives a single threshold over a compact parameter family, with the
threshold chosen before the initial susceptible count. The actual finite-to-local
comparison is proved uniformly on compact real tilt sets. Combining it with
normalizer bounds proves positive lower and finite upper bounds for the actual
finite residual amplitude at all those tilts with high probability. Analyticity
and a Schwarz estimate also give a uniform central-disk approximation of that
amplitude by the local limit at the center times the finite entire residual at
the center. This last factor is allowed to vary with population size. These
lemmas feed the completed fixed-parameter `thm:profil` proof. The paper's own interchange of a stochastic
normalizer error with the Fourier integral has not been certified by these
arguments: the formal proof keeps the entire residual inside the integral and
controls its variation near the saddle.

The compact-tilt stochastic saddle assembly is proved uniformly over compact
epidemic parameter families. A finite analytic-disk cover gives one complex neighborhood of the
entire real tilt compact. Uniform finite-to-local comparison, a stochastic
modulus of the local limit, and entire-residual bounds yield a central-amplitude
estimate on that neighborhood. Combining it with the actual outer Fourier
integral and Gaussian tail at window $(\log n)^{-5/12}$ gives one probability
threshold for every exact integer lattice height in the compact. The final
normalization retains the finite entire residual inside the integral. Positive
upper and lower bounds on the reference amplitude and on the normalized saddle
integral yield the final logarithmic profile envelope. An exact log identity
produces the $-\frac12\log\log n$ correction. The coupled state law and the
vanishing non-strict survival boundary transfer it to the source path law.
This proves the source statement without certifying the paper's own step that
extracts a stochastic normalizer error from the Fourier integral.

The integrated entry point builds with **3637 jobs**. A fresh batched axiom
probe and exact-type example for `uniformStrongProfileTheorem`,
`strongProfileTheorem`, the compact saddle inputs, and inherited `mainTheorem` report only `propext`,
`Classical.choice`, and `Quot.sound`. This is a mechanical dependency check;
the source comparison here is a self-review and there has been no independent
kernel replay. The numbered-result inventory now has **18 of 31** complete.
