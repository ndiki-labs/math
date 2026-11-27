"""Recompute the finite K5 exclusions from the written eight-vertex argument."""

from collections import Counter
from itertools import combinations, combinations_with_replacement, product
import json


LABELS = tuple(range(8))
CLIQUE_EDGES = tuple(combinations(range(5), 2))
LABEL_PAIRS = tuple(combinations(LABELS, 2))
PROFILES = tuple(profile for size in range(9) for profile in combinations(LABELS, size))


def kernels():
    # A clique vertex records which of the three ordered ear vertices it sees.
    # Sorting the five records quotients by all permutations of the clique.
    records = tuple(tuple(subset) for size in range(4) for subset in combinations((5, 6, 7), size))
    for marks in combinations_with_replacement(records, 5):
        contacts = {v: {a for a, entry in enumerate(marks) if v in entry} for v in (5, 6, 7)}
        if any(len(neighbours) > 4 for neighbours in contacts.values()):
            continue
        if not any(a != b for a, b in product(contacts[5], contacts[7])):
            continue
        attachments = tuple((a, v) for v, neighbours in contacts.items() for a in sorted(neighbours))
        edges = CLIQUE_EDGES + attachments + ((5, 6), (6, 7))
        yield edges
        yield edges + ((5, 7),)


def simple_path_lengths(edges):
    adjacency = {v: set() for v in LABELS}
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    lengths = {(a, b): set() for a, b in product(LABELS, repeat=2)}
    for start in LABELS:
        stack = [(start, {start})]
        while stack:
            last, seen = stack.pop()
            lengths[start, last].add(len(seen) - 1)
            for next_vertex in adjacency[last] - seen:
                stack.append((next_vertex, seen | {next_vertex}))
    return lengths


def minimum_incident(order):
    if order == 23:
        return 49
    if order == 24:
        return 56
    return 57


def bare_ear_cap(edges, allowed, lengths):
    endpoints = frozenset(a for a, v in edges if a < 5 <= v)
    assert len(edges) == 14 and len(endpoints) == 2
    assert max(map(len, allowed)) == 3
    assert all(len(set(p) - endpoints) <= 2 for p in allowed)
    need = sum(8 - sum(v in edge for edge in edges) for v in LABELS if v not in endpoints)
    assert need == 30

    doubles = [p for p in allowed if len(p) >= 2]
    nonempty = [p for p in allowed if p]
    joint_endpoints = tuple(sorted(endpoints))
    assert joint_endpoints in doubles

    def can_close(first, second, exterior_length):
        return any(a != b and 7 - exterior_length in lengths[a, b]
                   for a, b in product(first, second))

    for p in doubles:
        if p != joint_endpoints:
            assert can_close(p, joint_endpoints, 1)
            assert all(can_close(p, q, 2) for q in nonempty)
        assert all(can_close(p, q, 4) for q in doubles)

    # The path exclusions give at least six empty profiles per multiple
    # profile other than the joint endpoints. The six non-endpoint labels
    # need 30 incidences and get at most two per profile.
    caps = {order: len(edges) + 2 * (order - 8) - need // 2 for order in range(23, 34)}
    assert all(cap < minimum_incident(order) for order, cap in caps.items())
    return caps


def main():
    counts = Counter()
    final_caps = []
    for edges in kernels():
        lengths = simple_path_lengths(edges)
        allowed = [profile for profile in PROFILES
                   if all(7 not in lengths[pair] for pair in combinations(profile, 2))]
        if all(len(p) <= 1 for p in allowed):
            assert all(len(edges) + order - 8 < minimum_incident(order) for order in range(23, 34))
            counts["one_attachment"] += 1
            continue

        maximum_profile = {v: max(len(p) for p in allowed if v in p) for v in LABELS}
        disjoint = {pair for pair in LABEL_PAIRS if {5, 6, 7} <= lengths[pair]}
        if any(sum(9 - maximum_profile[v] for v in labels) > 25
               and all(pair in disjoint for pair in combinations(labels, 2))
               for labels in PROFILES):
            counts["disjoint_attachment_neighbourhoods"] += 1
            continue

        final_caps.append(bare_ear_cap(edges, allowed, lengths))
        counts["bare_ear"] += 1
    print(json.dumps({"kernels": sum(counts.values()), "classification": dict(counts),
                      "bare_ear_incidence_caps": final_caps}, indent=2))


if __name__ == "__main__":
    main()
