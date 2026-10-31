# Orbit transference implementation notes — 30 October 2026

The user requested removal of the conditional dependence on the author's
other paper. The required part is its orbit generalized von Neumann estimate,
not its Piatetski–Shapiro integer main theorems.

The implementation reuses the permitted finite Teräväinen interface. For
Rᵢ(n)=Pᵢ(n−1), composition with X−1 preserves the exact natural degrees.
One fixed support constant 1+ΣᵢΣⱼ≤d|coeffⱼ(Pᵢ)| bounds a+Rᵢ(n) for
1≤a≤Nᵈ and 1≤n≤N. The spatial functions are literal zero extensions;
the f₀ sum over its Finsupp support equals the full spatial interval sum.
Both normalizations agree exactly, including their complex field casts.

For A(x) equal to the actual finite weighted orbit average, the explicit
multiplier h(x)=conj(A(x))/‖A(x)‖ is everywhere 1-bounded and satisfies
h(x)A(x)=‖A(x)‖, including A(x)=0. Its measurability and integrability are
proved. Action invariance preserves each translated integral. On one common
a.e. set all original fᵢ are 1-bounded along every integer iterate. The finite
VN bound then controls the spatially averaged pairing pointwise. Integrating
proves the exact OrbitVNInput interface, retaining the same degree-only K
and a constant chosen before the system, cutoff, weights and phase bound.

Routine exploratory checks exposed only Finsupp support simplification,
finite-sum congruence, integer-cardinality casts and unfolding goals. These
were resolved in the production proofs, without changing the theorem or
adding hypotheses. Successful actual command:
`source ../tooling/env.sh && flock /tmp/psprimes-orbit-lean.lock lake build PSPrimes.OrbitTransference`.
The subsequent eight-declaration `#print axioms` audit also exited 0, with
only propext, Classical.choice and Quot.sound. Build/audit input and output
are in evidence/orbit-transference-build.log, evidence/OrbitTransferenceAudit.lean
and evidence/orbit-transference-audit.log. Measure helper and polynomial
modules have separately successful builds and standard-foundation audits.

Frozen core SHA-256:
cf4ff2efd8c1cf3f8d6e7806c909c080b578813de85aab1aa09beb3d90669bf0.
The final project-wide rebuild and updated public-main integration are a
separate root-agent step; this note does not claim those have already run.
