"""Exact survival-function check of two hitting times on a cycle with a chord.

Run with Python 3.9 or later. No third-party packages are used. The calculation
builds the walk directly on a cycle with a chord. Newton's identities and the
Cayley-Hamilton theorem sum the survival probabilities. No linear-system solver
or formula for a corridor is used by the certificate generator.
"""

from fractions import Fraction
from math import lcm


def cycle_with_chord(p, q):
    """A=0, B=p, target=1, start=2. Return sorted adjacency lists."""
    if p < 3 or q < 2:
        raise ValueError("Require p >= 3 and q >= 2.")
    n = p + q
    neighbours = [{(i - 1) % n, (i + 1) % n} for i in range(n)]
    neighbours[0].add(p)
    neighbours[p].add(0)
    return [sorted(row) for row in neighbours]


def killed_transitions(neighbours, start, target, remember_previous):
    """Build the transient transition rows for a walk with an empty initial list."""
    if remember_previous:
        fresh = (None, start)
        states = [fresh] + [
            (previous, current)
            for current, row in enumerate(neighbours) if current != target
            for previous in row
        ]

        def choices(state):
            previous, current = state
            allowed = [nxt for nxt in neighbours[current] if nxt != previous]
            # A one-entry FIFO list allows forced reversal at a leaf.
            return [(current, nxt) for nxt in (allowed or neighbours[current])]
    else:
        fresh = start
        states = [v for v in range(len(neighbours)) if v != target]

        def choices(state):
            return neighbours[state]

    indices = {s: i for i, s in enumerate(states)}
    rows = [choices(s) for s in states]
    common_denominator = lcm(*(len(row) for row in rows))
    # Discard transitions to the target only AFTER computing each denominator.
    weighted_rows = [
        [(indices[s], common_denominator // len(row)) for s in row if s in indices]
        for row in rows
    ]
    return states, indices[fresh], common_denominator, weighted_rows


def exact_survival_sums(scale, transitions):
    """For each start, sum all survival probabilities exactly.

    With P the killed transition matrix, set A=scale*P. For an initial state i,
    the coefficients of [(I-zA)^(-1) 1]_i count survival with integer weights.
    Its common denominator det(I-zA) is found from traces of A^j by Newton's
    identities. Multiplication by its denominator leaves a polynomial of degree
    at most dimension-1. Evaluation at z=1/scale gives E_i[T].
    """
    size = len(transitions)
    power = [[int(i == j) for j in range(size)] for i in range(size)]
    survival_counts = [[1] * size]
    traces = [0]
    denominator = [1]

    for exponent in range(1, size + 1):
        product = []
        for weighted_row in transitions:
            result_row = [0] * size
            for index, weight in weighted_row:
                for j, count in enumerate(power[index]):
                    result_row[j] += weight * count
            product.append(result_row)
        power = product
        traces.append(sum(row[i] for i, row in enumerate(power)))
        numerator = -sum(
            denominator[exponent - j] * traces[j] for j in range(1, exponent + 1)
        )
        coefficient, remainder = divmod(numerator, exponent)
        if remainder:
            raise ArithmeticError("Newton coefficient failed integer division.")
        denominator.append(coefficient)
        if exponent < size:
            survival_counts.append([sum(row) for row in power])

    # Evaluate numerator and denominator after multiplying both by scale**size.
    denominator_value = sum(c * scale ** (size - j) for j, c in enumerate(denominator))
    if denominator_value == 0:
        raise ArithmeticError("Singular killed kernel.")
    values = []
    for state in range(size):
        numerator_value = 0
        for k in range(size):
            ck = sum(denominator[j] * survival_counts[k-j][state] for j in range(k+1))
            numerator_value += ck * scale ** (size - k)
        values.append(Fraction(numerator_value, denominator_value))

    # A second local check, using the defining one-step expectation at every state.
    for i, row in enumerate(transitions):
        rhs = scale + sum(weight * values[j] for j, weight in row)
        if scale * values[i] != rhs:
            raise ArithmeticError(f"Nonzero first-step residual at state {i}.")
    return values


def degree_weighted_mean(neighbours, target, states, values, remember_previous):
    """Use the degree weights pi_i and a fresh, uniformly chosen first edge."""
    by_state = dict(zip(states, values))
    sum_degrees = sum(map(len, neighbours))
    total = Fraction(0)
    for vertex, row in enumerate(neighbours):
        if vertex == target:
            continue
        if remember_previous:
            # For uniform first edge v->j the conditional cost is 1+H((v,j),a).
            total += len(row) + sum(by_state.get((vertex, j), 0) for j in row)
        else:
            total += len(row) * by_state[vertex]
    return total / sum_degrees


def check_case(p, q):
    neighbours = cycle_with_chord(p, q)
    assert sum(map(len, neighbours)) == 2 * (p + q + 1)
    assert [i for i, row in enumerate(neighbours) if len(row) == 3] == [0, p]
    assert all(len(row) in (2, 3) for row in neighbours)
    start, target = 2, 1
    results = []
    stationary = []
    for remember in (False, True):
        states, fresh, scale, rows = killed_transitions(neighbours, start, target, remember)
        values = exact_survival_sums(scale, rows)
        results.append(values[fresh])
        if (p, q) == (8, 15):
            stationary.append(degree_weighted_mean(neighbours, target, states, values, remember))
            # Under the given initial rule the first step is toward 1 or toward 3.
            wrong_direction = (2, 3) if remember else 3
            conditional = 1 + values[states.index(wrong_direction)]
            expected = Fraction(25) if remember else Fraction(3543, 143)
            assert conditional == expected
            assert values[fresh] == (1 + conditional) / 2
    simple, nonbacktracking = results
    # Check two symbolic expressions only AFTER the survival calculation.
    formula_s = p-2 + Fraction((2*q+1)*p + 3*q*q+4*q+2, (p+1)*q+p)
    formula_n = Fraction(4*p+3*q+1, 6)
    assert simple == formula_s and nonbacktracking == formula_n
    if (p, q) == (8, 15):
        assert len(neighbours) == 23
        assert simple == Fraction(1843, 143)
        assert nonbacktracking == 13
        assert nonbacktracking - simple == Fraction(16, 143)
        assert stationary == [Fraction(51907, 858), Fraction(1087, 72)]
        print(f"With target 1 and degree-weighted initial vertex: "
              f"SRW={stationary[0]}, NB={stationary[1]}")
    print(f"Theta(1,{p},{q}): V={len(neighbours)}, E={p+q+1}, "
          f"SRW={simple}, NB={nonbacktracking}, NB-SRW={nonbacktracking-simple}; "
          "all first-step residuals zero")


def check_leaf_examples():
    tests = {
        "single edge": [[1], [0]],
        "three-vertex path": [[1], [0, 2], [1]],
        "star with three leaves": [[1, 2, 3], [0], [0], [0]],
        "four-vertex path": [[1], [0, 2], [1, 3], [2]],
        "triangle with a pendant edge": [[1, 2, 3], [0, 2], [0, 1], [0]],
    }
    for name, neighbours in tests.items():
        equal_targets = []
        for a in range(len(neighbours)):
            start = next(i for i in range(len(neighbours)) if i != a)
            means = []
            for remember in (False, True):
                states, _, scale, rows = killed_transitions(neighbours, start, a, remember)
                values = exact_survival_sums(scale, rows)
                means.append(degree_weighted_mean(neighbours, a, states, values, remember))
            assert means[0] >= means[1]
            expected_equality = all(len(neighbours[j]) == 1 for j in neighbours[a])
            assert (means[0] == means[1]) == expected_equality
            if means[0] == means[1]:
                equal_targets.append(a)
        print(f"Leaf convention, {name}: equality targets {equal_targets}")


if __name__ == "__main__":
    for parameters in ((3, 2), (6, 6), (8, 15), (10, 20), (4, 16)):
        check_case(*parameters)
    check_leaf_examples()
