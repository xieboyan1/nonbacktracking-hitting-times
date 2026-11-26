Run the following from the supplement directory, using Python 3.9
  or later with assertions enabled. All three scripts use only the standard
  library. expected_output.txt records an exact run of all three.

    python verify_theta_ldr.py
    python independent_check.py
    python check_trace_variance.py

  verify_theta_ldr.py constructs three paths sharing two terminals and
  solves the two absorbing first-step systems by rational Gaussian
  elimination. Its labels are A=0, B=1, target=2, start=3. It also prints
  an auxiliary ten-vertex example.

  independent_check.py constructs a cycle with chord {0,p}, using
  A=0, B=p, target=1, start=2, precisely the labels in Figure 1. It sums
  the survival probabilities by integer matrix powers and Newton's
  identities, then checks the first-step recurrence in every transient
  state. It checks the conditional and stationary-start means of the
  23-vertex example and tests the equality condition on graphs with leaves.

  check_trace_variance.py uses the outgoing oriented-edge matrix to
  compute the fundamental matrix, conditional returns and two vertex
  constants. It checks both sides of the variance bounds and the
  targetwise equality criterion on five graphs, including the witness.
  This program imports the elimination routine from verify_theta_ldr.py.

  Throughout, a fresh first step is uniform. A walk started at its target
  has hitting time zero. Each reported time is a number of transitions.
