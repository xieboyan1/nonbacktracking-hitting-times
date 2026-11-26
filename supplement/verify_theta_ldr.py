"""Solve two killed walk chains directly over the rationals, independently of the corridor formulas."""
from fractions import Fraction as F


def solve_chain(states, successors):
    idx = {state: i for i, state in enumerate(states)}
    size = len(states)
    rows = []
    for i, state in enumerate(states):
        neighbors = successors(state)
        row = [F(0)] * (size + 1)
        row[i] = F(len(neighbors))
        row[-1] = F(len(neighbors))
        for v in neighbors:
            if v in idx:
                row[idx[v]] -= 1
        rows.append(row)
    for j in range(size):
        k = next(k for k in range(j, size) if rows[k][j])
        rows[k], rows[j] = rows[j], rows[k]
        pivot = rows[j]
        for row in rows[j + 1:]:
            if not row[j]:
                continue
            c = row[j] / pivot[j]
            row[j:] = [a - c * b for a, b in zip(row[j:], pivot[j:])]
    values = [F(0)] * size
    for j in reversed(range(size)):
        row = rows[j]
        values[j] = (row[-1] - sum(row[k] * values[k] for k in range(j + 1, size))) / row[j]
    return dict(zip(states, values))


def compare(n, edgelist, start, target):
    nb = [[] for _ in range(n)]
    for a, b in edgelist:
        nb[a].append(b)
        nb[b].append(a)
    ordinary = solve_chain([v for v in range(n) if v != target], lambda v: nb[v])
    # Directed states (former, current). A first move to target stops immediately.
    arcs = [(u, v) for v in range(n) if v != target for u in nb[v]]
    aided = solve_chain(arcs, lambda e: [(e[1], w) for w in nb[e[1]] if w != e[0]])
    fresh = 1 + sum(aided.get((start, v), 0) for v in nb[start]) / len(nb[start])
    return ordinary[start], fresh


def theta(m, n):
    a, b = 0, 1
    next_id = 2
    edges = []
    for length in (1, m, n):
        path = [a, *range(next_id, next_id + length - 1), b]
        next_id += length - 1
        edges.extend(zip(path, path[1:]))
    return next_id, edges


if __name__ == '__main__':
    for m, n in [(4, 5), (8, 15), (10, 20), (12, 35)]:
        graph = theta(m, n)
        actual = compare(*graph, start=3, target=2)
        simple = m - 2 + F((2*n + 1)*m + 3*n*n + 4*n + 2, (m + 1)*n + m)
        avoiding = F(4*m + 3*n + 1, 6)
        assert actual == (simple, avoiding)
        print(f'Theta(1,{m},{n}), SRW={simple}, NB={avoiding}, NB-SRW={avoiding-simple}')
    chords = [(0, 2), (0, 4), (5, 9), (6, 9), (7, 9)]
    cycle = [(i, (i + 1) % 10) for i in range(10)]
    srw, nonback = compare(10, cycle + chords, 1, 0)
    assert (srw, nonback) == (F(2426, 773), F(85217, 27136))
    assert nonback - srw == F(40805, 20976128)
    print(f'10-vertex cycle with five chords, SRW={srw}, NB={nonback}, NB-SRW={nonback-srw}')
