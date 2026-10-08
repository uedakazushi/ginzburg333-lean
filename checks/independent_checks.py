#!/usr/bin/env python3
"""Independent exact checks of the mathematical formulas.

Uses integer polynomial arithmetic and finite-field linear algebra; no floating
point, external libraries, Lean, or claim of full formal verification. Symbolic
checks range over all 27 coefficients; finite-field and degree-bounded checks
are illustrations, not a proof of the tensor-regularity implication.
"""
from __future__ import annotations

from collections import defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
import json
import time

Poly = dict[tuple[int, ...], int]
ZERO: Poly = {}
ONE: Poly = {(): 1}


def add(a: Poly, b: Poly) -> Poly:
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + c
        if not out[m]:
            del out[m]
    return out


def scale(a: Poly, n: int) -> Poly:
    return {m: n * c for m, c in a.items() if n * c}


def mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            monomial = tuple(sorted(ma + mb))
            out[monomial] = out.get(monomial, 0) + ca * cb
    return {m: c for m, c in out.items() if c}


def coefficient(i: int, a: int, b: int, c: int) -> Poly:
    x, y, z = ((a, b, c), (c, a, b), (b, c, a))[i]
    return {(9 * x + 3 * y + z,): 1}


def accumulate(out: dict, key, value: Poly) -> None:
    result = add(out.get(key, ZERO), value)
    if result:
        out[key] = result
    else:
        out.pop(key, None)


# A row has dimensions 1,3,3,1. The third entry is a label in vector degrees.
BASIS = tuple((i, d, a) for i in range(3) for d in range(4)
              for a in range(3 if d in (1, 2) else 1))


@lru_cache(None)
def basis_product(x: tuple, y: tuple) -> dict:
    i, d, a = x
    j, e, b = y
    if (i + d) % 3 != j or d + e > 3:
        return {}
    if d == 0:
        return {y: ONE}
    if e == 0:
        return {x: ONE}
    if d == e == 1:
        return {(i, 2, c): coefficient(i, a, b, c) for c in range(3)}
    if (d, e) in ((1, 2), (2, 1)) and a == b:
        return {(i, 3, 0): ONE}
    return {}


def multiply_expression(a: dict, b: dict) -> dict:
    out: dict = {}
    for x, cx in a.items():
        for y, cy in b.items():
            for z, cz in basis_product(x, y).items():
                accumulate(out, z, mul(mul(cx, cy), cz))
    return out


def auxiliary_checks() -> dict:
    count = 0
    for x, y, z in product(BASIS, repeat=3):
        lhs = multiply_expression(basis_product(x, y), {z: ONE})
        rhs = multiply_expression({x: ONE}, basis_product(y, z))
        assert lhs == rhs, ("associativity", x, y, z, lhs, rhs)
        count += 1
    unit = {(i, 0, 0): ONE for i in range(3)}
    for x in BASIS:
        assert multiply_expression(unit, {x: ONE}) == {x: ONE}
        assert multiply_expression({x: ONE}, unit) == {x: ONE}
    return {"basis_dimension": len(BASIS), "symbolic_basis_triples": count,
            "unit_checks": 2 * len(BASIS), "coefficient_ring": "Z[w_000,...,w_222]",
            "passed": True}


# Ginzburg generators in algebra order; [b,a] means traverse a then b.
# kind 0=forward, 1=reverse, 2=loop.
GENERATORS = tuple((kind, i, a) for kind in range(3) for i in range(3)
                   for a in range(3 if kind < 2 else 1))


def endpoints(g: tuple) -> tuple[int, int]:
    kind, i, _ = g
    if kind == 0:
        return i, (i + 1) % 3
    if kind == 1:
        return (i + 1) % 3, i
    return i, i


def endpoint(start: int, word: tuple) -> int | None:
    vertex = start
    for g in reversed(word):
        source, target = endpoints(g)
        if source != vertex:
            return None
        vertex = target
    return vertex


@lru_cache(None)
def generator_d(g: tuple) -> dict:
    kind, i, a = g
    if kind == 0:
        return {}
    if kind == 1:
        return {((0, (i + 2) % 3, c), (0, (i + 1) % 3, b)):
                coefficient(i, a, b, c) for b, c in product(range(3), repeat=2)}
    out: dict = {}
    for j in range(3):
        accumulate(out, ((1, i, j), (0, i, j)), ONE)
        accumulate(out, ((0, (i + 2) % 3, j), (1, (i + 2) % 3, j)), scale(ONE, -1))
    return out


@lru_cache(None)
def word_d(word: tuple) -> dict:
    if not word:
        return {}
    g, rest = word[0], word[1:]
    out: dict = {}
    for w, p in generator_d(g).items():
        accumulate(out, w + rest, p)
    for w, p in word_d(rest).items():
        accumulate(out, (g,) + w, scale(p, (-1) ** g[0]))
    return out


def expression_d(expr: dict) -> dict:
    out: dict = {}
    for w, c in expr.items():
        for v, p in word_d(w).items():
            accumulate(out, v, mul(c, p))
    return out


def weight(word: tuple) -> int:
    return sum(g[0] + 1 for g in word)


def coh_degree(word: tuple) -> int:
    return -sum(g[0] for g in word)


def ginzburg_checks(max_weight: int = 6) -> dict:
    gen_terms = 0
    for g in GENERATORS:
        s, t = endpoints(g)
        dg = generator_d(g)
        assert expression_d(dg) == {}, ("d^2 generator", g)
        for w in dg:
            assert endpoint(s, w) == t
            assert weight(w) == g[0] + 1
            assert coh_degree(w) == -g[0] + 1
            gen_terms += 1
    count = term_count = 0
    # Enumerate valid paths; no vertex-free empty paths are merged.
    for start in range(3):
        stack = [((), start, 0)]
        while stack:
            word, target, n = stack.pop()
            dw = word_d(word)
            assert expression_d(dw) == {}, ("d^2 path", start, word)
            for w in dw:
                assert endpoint(start, w) == target
                assert weight(w) == n
                assert coh_degree(w) == coh_degree(word) + 1
                term_count += 1
            count += 1
            for g in GENERATORS:
                s, t = endpoints(g)
                ng = g[0] + 1
                if s == target and n + ng <= max_weight:
                    stack.append(((g,) + word, t, n + ng))
    return {"generators_checked": len(GENERATORS), "generator_terms_checked": gen_terms,
            "all_valid_paths_up_to_weight": max_weight, "valid_paths_checked": count,
            "nonzero_differential_terms_checked": term_count,
            "coefficient_ring": "Z[w_000,...,w_222]", "passed": True}


def sigma(ds: tuple[int, ...]) -> int:
    return sum(j * d for j, d in enumerate(ds)) + len(ds) * (len(ds) - 1) // 2 + ds.count(3)


def recursive_sigma(ds: tuple[int, ...]) -> int:
    if not ds:
        return 0
    return recursive_sigma(ds[1:]) + sum(ds[1:]) + len(ds[1:]) + (ds[0] == 3)


@lru_cache(None)
def compositions(n: int) -> tuple:
    if n == 0:
        return ((),)
    return tuple((d,) + tail for d in (1, 2, 3) if d <= n
                 for tail in compositions(n - d))


def sign_checks(max_internal_degree: int = 14) -> dict:
    words = splits = 0
    for n in range(max_internal_degree + 1):
        for ds in compositions(n):
            assert sigma(ds) == recursive_sigma(ds)
            words += 1
            for j, d in enumerate(ds):
                for p, q in ((1, 1), (1, 2), (2, 1)):
                    if p + q != d:
                        continue
                    pre, post = ds[:j], ds[j + 1:]
                    split = pre + (p, q) + post
                    assert sigma(split) + (p + q == 3) == sigma(ds) + q + sum(post) + len(ds)
                    ge = sigma(ds) + len(post) - sum(post) + p + 1
                    be = sigma(split) + len(pre)
                    assert (ge - be) % 2 == 0, (ds, j, p, q)
                    assert len(split) == len(ds) + 1 and sum(split) == sum(ds)
                    splits += 1
    return {"max_internal_degree": max_internal_degree, "words_checked": words,
            "splits_checked": splits, "passed": True,
            "scope": "Bounded independent check; all-length Lean proof script remains uncompiled."}


# Small finite-field exact linear algebra for row-annihilator/colon examples.
P = 5


def rref(rows: list[list[int]], ncols: int) -> tuple[list[list[int]], list[int]]:
    m = [[x % P for x in r] for r in rows]
    pivots, r = [], 0
    for c in range(ncols):
        pivot = next((i for i in range(r, len(m)) if m[i][c]), None)
        if pivot is None:
            continue
        m[r], m[pivot] = m[pivot], m[r]
        inverse = pow(m[r][c], -1, P)
        m[r] = [x * inverse % P for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c]:
                a = m[i][c]
                m[i] = [(x - a * y) % P for x, y in zip(m[i], m[r])]
        pivots.append(c)
        r += 1
        if r == len(m):
            break
    return m[:r], pivots


def span(vectors: list[list[int]], dim: int) -> tuple:
    return tuple(tuple(r) for r in rref(vectors, dim)[0])


def kernel(matrix: list[list[int]], ncols: int) -> list[list[int]]:
    m, pivots = rref(matrix, ncols)
    out = []
    for c in range(ncols):
        if c in pivots:
            continue
        v = [0] * ncols
        v[c] = 1
        for row, pivot in zip(m, pivots):
            v[pivot] = -row[c] % P
        out.append(v)
    return out


def transpose(m: list[list[int]]) -> list[list[int]]:
    return [list(c) for c in zip(*m)]


def matvec(m: list[list[int]], v: list[int]) -> list[int]:
    return [sum(a * b for a, b in zip(row, v)) % P for row in m]


def dot(a, b) -> int:
    return sum(x * y for x, y in zip(a, b)) % P


def levi(a: int, b: int, c: int) -> int:
    if len({a, b, c}) < 3:
        return 0
    inversions = (a > b) + (a > c) + (b > c)
    return (-1) ** inversions


def contraction(a: list[int]) -> list[list[int]]:
    return [[sum(levi(x, y, c) * a[x] for x in range(3)) % P
             for y in range(3)] for c in range(3)]


def left_one(a: list[int]) -> list[list[int]]:
    m = [[0] * 8 for _ in range(8)]
    mu = contraction(a)
    for j in range(3):
        m[1 + j][0] = a[j]
        m[7][4 + j] = a[j]
        for c in range(3):
            m[4 + c][1 + j] = mu[c][j]
    return m


def preimage_of_image(l: list[list[int]], g: list[list[int]]) -> list[list[int]]:
    # The image is annihilator of ker(l^T), no numeric pseudoinverse.
    image_annihilator = kernel(transpose(l), len(l))
    equations = [[dot(a, column) for column in transpose(g)] for a in image_annihilator]
    return kernel(equations, len(g[0]))


def normalize(v: tuple[int, ...]) -> tuple[int, ...]:
    a = next(x for x in v if x)
    inverse = pow(a, -1, P)
    return tuple(x * inverse % P for x in v)


def finite_field_checks() -> dict:
    points = sorted({normalize(v) for v in product(range(P), repeat=3) if any(v)})
    line_count = plane_count = full_count = 0
    for aa in points:
        a = list(aa)
        ma, la = contraction(a), left_one(a)
        assert len(rref(ma, 3)[1]) == 2
        kb = kernel(ma, 3)
        assert len(kb) == 1
        b = kb[0]
        lb = left_one(b)
        assert span(kernel(la, 8), 8) == span(transpose(lb), 8)
        line_count += 1
        for gg in points:
            g = list(gg)
            if len(span([a, g], 3)) != 2:
                continue
            mg, lg = contraction(g), left_one(g)
            T = preimage_of_image(ma, mg)
            assert len(T) == 2
            colon = span(preimage_of_image(la, lg), 8)
            generated = [column for t in T for column in transpose(left_one(t))]
            assert colon == span(generated, 8)
            plane_count += 1
    # A plane is the annihilator of a projective nonzero functional.
    for nn in points:
        plane = kernel([list(nn)], 3)
        assert len(plane) == 2
        # Matrix whose image is the ideal generated by the plane.
        columns = [c for a in plane for c in transpose(left_one(a))]
        lplane = transpose(columns)
        for gg in points:
            if not dot(nn, gg):
                continue
            colon = span(preimage_of_image(lplane, left_one(list(gg))), 8)
            positive_rows = [[int(i == j) for i in range(8)] for j in range(1, 8)]
            assert colon == span(positive_rows, 8)
            full_count += 1
    # Negative control: for the zero tensor, a degree-one annihilator is too large.
    a = [1, 0, 0]
    lzero = [[0] * 8 for _ in range(8)]
    lzero[1][0] = 1
    lzero[7][4] = 1
    negative_control = len(kernel(lzero, 8)) != len(span(transpose(lzero), 8))
    assert negative_control
    return {"field": "F_5", "tensor": "alternating determinant tensor",
            "projective_rank_checks": len(points), "annihilator_cases": line_count,
            "plane_colon_cases": plane_count, "full_colon_cases": full_count,
            "zero_tensor_negative_control_detected": negative_control,
            "scope": "Examples only; this finite field is not algebraically closed.",
            "passed": True}



@lru_cache(None)
def bar_basis(n: int, r: int) -> tuple:
    """Basis of e_i B_(r,n)(S): positive-degree composable E factors."""
    return tuple(tuple(zip(ds, labels))
                 for ds in compositions(n) if len(ds) == r
                 for labels in product(*(range(3 if d in (1, 2) else 1) for d in ds)))


def bar_column(i: int, word: tuple, row_index: dict, zero_tensor: bool) -> dict[int, int]:
    out: dict[int, int] = {}
    vertex = i
    for j in range(len(word) - 1):
        d, a = word[j]
        e, b = word[j + 1]
        result = []
        if d == e == 1 and not zero_tensor:
            result = [(2, c, levi(a, b, c)) for c in range(3)]
        elif (d, e) in ((1, 2), (2, 1)) and a == b:
            result = [(3, 0, 1)]
        for degree, label, scalar in result:
            if scalar:
                merged = word[:j] + ((degree, label),) + word[j + 2:]
                row = row_index[merged]
                out[row] = (out.get(row, 0) + (-1) ** j * scalar) % P
                if not out[row]:
                    del out[row]
        vertex = (vertex + d) % 3
    # Alternating and zero tensors used here are cyclically identical in each row.
    return out


def sparse_rank(columns: list[dict[int, int]]) -> int:
    pivots: dict[int, dict[int, int]] = {}
    for column in columns:
        vector = dict(column)
        while vector:
            pivot = min(vector)
            scalar = vector[pivot]
            if pivot in pivots:
                for j, value in pivots[pivot].items():
                    vector[j] = (vector.get(j, 0) - scalar * value) % P
                    if not vector[j]:
                        vector.pop(j, None)
            else:
                inverse = pow(scalar, -1, P)
                pivots[pivot] = {j: value * inverse % P for j, value in vector.items()}
                break
    return len(pivots)


def bar_checks(max_internal_degree: int = 5) -> dict:
    diagonal = []
    exactness_positions = square_zero_columns = 0
    for n in range(max_internal_degree + 1):
        dimensions = [len(bar_basis(n, r)) for r in range(n + 2)]
        for i in range(3):
            differentials: dict[int, list[dict[int, int]]] = {}
            ranks = [0] * (n + 2)
            for r in range(1, n + 2):
                rows = {w: j for j, w in enumerate(bar_basis(n, r - 1))}
                columns = [bar_column(i, w, rows, False) for w in bar_basis(n, r)]
                differentials[r] = columns
                ranks[r] = sparse_rank(columns)
                if r > 1:
                    previous = differentials[r - 1]
                    for column in columns:
                        squared: dict[int, int] = {}
                        for j, scalar in column.items():
                            for row, value in previous[j].items():
                                squared[row] = (squared.get(row, 0) + scalar * value) % P
                        assert all(value == 0 for value in squared.values())
                        square_zero_columns += 1
            for r in range(n + 1):
                homology_dimension = dimensions[r] - ranks[r] - ranks[r + 1]
                expected = (n + 2) * (n + 1) // 2 if r == n else 0
                assert homology_dimension == expected, (i, n, r, homology_dimension)
                exactness_positions += (r != n)
            if i == 0:
                diagonal.append({"n": n, "dim_Tor_nn_per_vertex": dimensions[n] - ranks[n]})
    # Off-diagonal homology appears for the zero tensor already at (r,n)=(1,2).
    rows = {w: j for j, w in enumerate(bar_basis(2, 1))}
    zero_columns = [bar_column(0, w, rows, True) for w in bar_basis(2, 2)]
    zero_h12 = len(bar_basis(2, 1)) - sparse_rank(zero_columns)
    assert zero_h12 == 3
    return {"field": "F_5", "tensor": "alternating determinant tensor",
            "max_internal_degree": max_internal_degree,
            "vertices_checked": 3, "square_zero_columns_checked": square_zero_columns,
            "off_diagonal_positions_checked": exactness_positions,
            "diagonal_dimensions": diagonal,
            "zero_tensor_Tor_1_internal_2_dimension": zero_h12,
            "passed": True,
            "scope": "Finite-degree example, NOT the all-tensor/all-degree theorem."}


def main() -> None:
    start = time.monotonic()
    report = {"lean_kernel_verification": False,
              "main_theorem_verified": False,
              "auxiliary_algebra": auxiliary_checks(),
              "ginzburg_differential": ginzburg_checks(),
              "comparison_signs": sign_checks(),
              "row_ideal_examples": finite_field_checks(),
              "bar_complex_examples": bar_checks()}
    report["elapsed_seconds"] = round(time.monotonic() - start, 3)
    root = Path(__file__).resolve().parents[1]
    (root / "logs").mkdir(exist_ok=True)
    text = json.dumps(report, ensure_ascii=False, indent=2)
    (root / "logs" / "independent_checks.json").write_text(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
