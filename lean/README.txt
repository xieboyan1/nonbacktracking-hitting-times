Vertex hitting times for non-backtracking walks with fixed and stationary starts
Lean 4.19.0 and mathlib v4.19.0

Reproduce
  From this directory, using Lean's elan toolchain manager and Lake:

    lake update
    lake exe cache get
    lake build
    lake env lean -DwarningAsError=true Nonbacktracking.lean

  To recheck all local source files in a new temporary build directory,
  including their proofs, use: lake env python verify.py
  The script treats warnings as errors, checks the axioms reported for
  the main theorems and prints the SHA-256 digest of each source file.
  verification.txt records the clean replay supplied with this version.
  Python is used only for this build driver; the proofs are Lean terms.

General theorems
  Stationary.Graph uses finite neighbour sets, symmetry, no loops,
  nonempty neighbourhoods and connectedness. Walks.ordinary and
  Walks.remembered implement the two transition rules. Walks.freshTrunc
  gives the empty-memory first step at the initial vertex. Hitting.lean
  constructs the unique Green solution of the killed first-step system
  and proves convergence of the survival sums, including for periodic
  chains. Walks.nbReach proves access to every target in the presence of
  leaves or deterministic degree-two stretches.

  Walks.fixed_target_comparison and Walks.stationary_limits establish
  the degree-weighted fixed-target comparison and its equality criterion.
  The comparison is obtained from a sum of edge squares in Stationary.
  Kemeny.double_average (Strict.lean) proves that the two degree-weighted
  means over targets agree exactly on two vertices.

  Theta.means treats all p=m+3 and q=n+2. Splitting the p-edge path at
  the target leaves four corridors of lengths 1, p-1, 1 and q.
  A state is a directed corridor and the number of edges already taken
  since its entrance. Every transition costs one graph edge. The fresh
  first step from the adjacent vertex is explicit in Theta.fromX.
  Theta.square_family proves the limits of the two expectations on
  q=p^2, the limit 1/8 of their ratio divided by p, and divergence of
  their ratio to infinity.

  For the remaining theorems the minimum degree is at least two and
  some vertex has degree at least three. Fundamental.Z is the inverse
  of I-F+W. Forward.valid_inverse proves that restriction to valid
  oriented edges determines the same inverse values there.
  Forward.projected_trace identifies the compressed diagonal sum in the
  two edge-indexing conventions. GapData ties the port equations in Gap
  to the actual killed and full-chain solutions, including target and
  normalization terms. Kemeny.comparison_and_equality proves the order
  of the constants and the equivalence with locally uniform returns.

  Kemeny.variance_bounds proves the two bounds with maximum degree and
  longest corridor. The latter is one plus the maximal number of forced
  steps from an oriented edge to a branching vertex. Corridors.chain_norm
  proves the counting estimate by recording the terminal port and its
  distance. Kemeny.min_degree_bound applies to any lower degree bound
  strictly above two, including the actual minimum.

The independently encoded 23-vertex graph in Witness.lean
  Vertices are Fin 23. Vertices differing by one modulo 23 are joined,
  as are 0 and 8. graph_checks and connected check simplicity, symmetry
  and reachability. The target is 1. A state stores the current vertex
  and its arrival direction. Tag 0 means an empty initial memory.

  uniform_moves counts the outcomes of a six-sided uniform draw for each
  proposed next vertex. All admissible vertices receive equal mass and
  all others receive zero. records_previous checks the memory after every
  move. A six-sided draw works since row sizes are 1, 2 or 3.

  word_probability identifies survival at time n with the number of
  length-n draw sequences avoiding the target through time n, divided
  by 6^n. The mean is defined by the limit of finite sums of these tail
  probabilities, the tail-sum definition for an integer hitting time.
  It does not require a separate library of measures on infinite paths.

  rows checks the integer Bellman certificates at every encoded state.
  partial_tail and tail_bound show that the residual is nonnegative and
  at most (255/256)^n times the candidate mean. Thus the limit theorem
  mean proves convergence to the certificate, including finiteness.

  witness and refutes_pointwise prove that from vertex 2 with empty
  memory, the NB and ordinary means are 13 and 1843/143. Their difference
  is 16/143. stationary_witness fixes the same target, samples the
  starting vertex with mass degree/48 and proves means 1087/72 and
  51907/858 respectively.

Scope of the check
  The checked hitting times are limits of truncated expectations or
  finite survival sums. The kernel checks the mathematical statements.
  Bibliographic priority and the interpretation of the 2012 authors'
  wording remain matters for the accompanying referee audit.
