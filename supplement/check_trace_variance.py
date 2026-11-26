"""Compute Kemeny statistics from the original directed-edge transition matrix using exact arithmetic."""
from fractions import Fraction as F
from verify_theta_ldr import solve_chain


def longest_chain(adjacent):
    """Count edges along each corridor from a branch to the next branch."""
    lengths = []
    for start, neighbours in enumerate(adjacent):
        if len(neighbours) < 3:
            continue
        for first in neighbours:
            previous, current, length = start, first, 1
            while len(adjacent[current]) == 2:
                u, v = adjacent[current]
                successor = v if u == previous else u
                previous, current = current, successor
                length += 1
            lengths.append(length)
    return max(lengths)


def invert(matrix):
    n = len(matrix)
    rows = [row[:] + [F(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    for j in range(n):
        k = next(k for k in range(j, n) if rows[k][j])
        rows[j], rows[k] = rows[k], rows[j]
        c = rows[j][j]
        rows[j] = [v/c for v in rows[j]]
        for i in range(n):
            if i == j or not rows[i][j]:
                continue
            c = rows[i][j]
            rows[i] = [x-c*y for x, y in zip(rows[i], rows[j])]
    return [row[n:] for row in rows]


def stats(edges):
    n = 1 + max(max(edge) for edge in edges)
    adjacent = [[] for i in range(n)]
    for v, w in edges:
        adjacent[v].append(w)
        adjacent[w].append(v)
    arcs = [(v, w) for v in range(n) for w in adjacent[v]]
    r = len(arcs)
    pi = [F(len(neighbors), r) for neighbors in adjacent]
    delta, Delta = min(map(len, adjacent)), max(map(len, adjacent))
    assert delta >= 2 and Delta >= 3
    ell = longest_chain(adjacent)
    def next_arcs(e):
        return [(e[1], k) for k in adjacent[e[1]] if k != e[0]]
    # Z_e = (I - P_edge + W_edge)^(-1), with outgoing arcs indexed by their tails.
    inverse_z = []
    for i, e in enumerate(arcs):
        successors = next_arcs(e)
        inverse_z.append([F(i == j) + F(1, r) - F(f in successors, len(successors))
                          for j, f in enumerate(arcs)])
    ze = invert(inverse_z)
    total = [F(0)] * 4
    for a in range(n):
        block = [idx for idx, e in enumerate(arcs) if e[0] == a]
        zaa = sum(ze[j][k] for j in block for k in block) / len(block)
        trace_h = zaa / pi[a] - 1
        selected = [arc for arc in arcs if arc[1] != a]
        continuation = solve_chain(selected, next_arcs)
        simple = solve_chain([v for v in range(n) if v != a], lambda v: adjacent[v])
        h = sum(pi[v] * (1 + sum(continuation.get((v, w), 0) for w in adjacent[v])/len(adjacent[v]))
                for v in range(n) if v != a)
        srw = sum(pi[v]*time for v, time in simple.items())
        returns = [1+continuation[a, w] for w in adjacent[a]]
        mean = sum(returns)/len(returns)
        assert mean == 1/pi[a]
        variance = sum((t-mean)**2 for t in returns)/len(returns)
        gap_a = h - trace_h
        assert h < srw
        assert (gap_a == 0) == (variance == 0)
        assert pi[a] * variance / Delta <= gap_a <= 2 * ell * pi[a] * variance
        print('a', a, 'pi', pi[a], 'H', h, 'H_trace', trace_h, 'H_SRW', srw,
              'Delta', h-trace_h, 'returns', tuple(str(t) for t in returns), 'var', variance)
        for j, quantity in enumerate((h, trace_h, srw, pi[a] * variance)):
            total[j] += pi[a]*quantity
    print('K_hit, K_trace, K_SRW, V:', tuple(str(t) for t in total))
    gap = total[0] - total[1]
    lower = total[3] / Delta
    upper = 2 * ell * total[3]
    if delta > 2:
        upper = min(upper, total[3] / (delta-2))
    assert lower <= gap <= upper
    print('gap, lower, upper:', gap, lower, upper)


if __name__ == '__main__':
    print('K4')
    stats([(a,b) for a in range(4) for b in range(a+1,4)])
    print('Diamond = K4 minus edge {2,3}')
    stats([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)])
    print('House = square and triangle with shared edge {0,1}')
    stats([(0, 1), (1, 2), (2, 3), (3, 0), (0, 4), (1, 4)])
    print('K5 minus edge {3,4}')
    stats([(a,b) for a in range(5) for b in range(a+1,5) if (a,b) != (3,4)])
    print('C23 with chord {0,8}')
    stats([(i, (i + 1) % 23) for i in range(23)] + [(0, 8)])
