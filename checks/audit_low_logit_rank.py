#!/usr/bin/env python3
"""Exact finite structural audit of the masked branching-program construction.

This is not a cryptographic security experiment. It verifies a two-input toy
with both keys, all active prefixes, every active cut matrix, and every active
length-H outcome. The complete model has T=128 bits: its label precedes fair
padding. Padding contributes only zero logit columns and an independent uniform
factor to probabilities, so the active enumeration suffices for these checks.

Only Python's standard library is used. All tests of logits, ranks, probabilities,
normalization, total variation, and oracle errors use exact integers/Fractions.
"""

from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import sys


N = 2
WIDTH = 5
DIMENSION = N + 7
SCALE = 8  # B = SCALE * ln(2), deliberately different from N in this finite toy.
BASE = 2 ** (2 * SCALE)
ETA = Fraction(1, 1 + BASE)
T = 128
IDENTITY = tuple(range(WIDTH))
ALPHA = (1, 2, 3, 4, 0)
BETA = (2, 0, 4, 1, 3)
SCHEDULE = (0, 1, 0, 1, 0, 1, 0)
L = len(SCHEDULE)
H = N + L + 1


def words(length):
    return list(product((0, 1), repeat=length))


def compose(left, right):
    """Permutation for left applied after right."""
    return tuple(left[right[i]] for i in range(WIDTH))


def inverse(permutation):
    return tuple(permutation.index(i) for i in range(WIDTH))


COMMUTATOR = compose(
    inverse(BETA), compose(inverse(ALPHA), compose(BETA, ALPHA))
)
TRUE_STATE = COMMUTATOR[0]
READOUT = tuple(1 if i == TRUE_STATE else -1 for i in range(WIDTH))


def identity_matrix(size):
    return [[int(i == j) for j in range(size)] for i in range(size)]


def matrix_vector(matrix, vector):
    return tuple(sum(a * b for a, b in zip(row, vector)) for row in matrix)


def row_matrix(row, matrix):
    return tuple(
        sum(row[i] * matrix[i][j] for i in range(len(row)))
        for j in range(len(row))
    )


def dot(left, right):
    return sum(a * b for a, b in zip(left, right))


def exact_rank(matrix):
    """Fraction Gaussian elimination, with no numerical rank tolerance."""
    if not matrix:
        return 0
    work = [[Fraction(value) for value in row] for row in matrix]
    rows, columns = len(work), len(work[0])
    pivot_row = 0
    for column in range(columns):
        selected = next(
            (i for i in range(pivot_row, rows) if work[i][column]), None
        )
        if selected is None:
            continue
        work[pivot_row], work[selected] = work[selected], work[pivot_row]
        pivot = work[pivot_row][column]
        work[pivot_row] = [value / pivot for value in work[pivot_row]]
        for i in range(pivot_row + 1, rows):
            coefficient = work[i][column]
            if coefficient:
                work[i] = [
                    x - coefficient * y
                    for x, y in zip(work[i], work[pivot_row])
                ]
        pivot_row += 1
        if pivot_row == rows:
            break
    return pivot_row


@lru_cache(maxsize=None)
def probability_one(normalized_logit):
    """sigma(2 B m) exactly, since exp(2 B) = BASE."""
    if normalized_logit >= 0:
        weight = BASE ** normalized_logit
        return Fraction(weight, 1 + weight)
    weight = BASE ** (-normalized_logit)
    return Fraction(1, 1 + weight)


def fraction_record(value):
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
        "decimal_for_orientation_only": float(value),
    }


class ToyTeacher:
    def __init__(self, key):
        assert key in (0, 1)
        self.key = key
        swap = list(IDENTITY)
        swap[0], swap[TRUE_STATE] = swap[TRUE_STATE], swap[0]
        key_permutation = tuple(swap) if key else IDENTITY
        self.permutations = (
            (IDENTITY, IDENTITY),
            (IDENTITY, IDENTITY),
            (IDENTITY, ALPHA),
            (IDENTITY, BETA),
            (IDENTITY, inverse(ALPHA)),
            (IDENTITY, inverse(BETA)),
            (key_permutation, key_permutation),
        )
        assert len(self.permutations) == L
        assert SCHEDULE[:N] == tuple(range(N))
        assert all(pair == (IDENTITY, IDENTITY) for pair in self.permutations[:N])

    def target(self, x):
        return (x[0] & x[1]) ^ self.key

    def direct_bp_state(self, copied_word):
        state = 0
        for j, bit in enumerate(copied_word):
            state = self.permutations[j][bit][state]
        return state

    def direct_logit(self, prefix):
        """Logit divided by B, defined without using the linear-state code."""
        t = len(prefix)
        assert 0 <= t < T
        if t < N or t >= H:
            return 0
        x = prefix[:N]
        if t < N + L:
            return 2 * x[SCHEDULE[t - N]] - 1
        copied_word = prefix[N:N + L]
        mismatch_count = sum(
            bit != x[SCHEDULE[j]] for j, bit in enumerate(copied_word)
        )
        sign = READOUT[self.direct_bp_state(copied_word)]
        assert sign in (-1, 1)
        return 2 * mismatch_count + sign

    @lru_cache(maxsize=None)
    def transition(self, t, bit):
        """Independent dense integer matrix on [1,x0,x1,C,v0,...,v4]."""
        matrix = identity_matrix(DIMENSION)
        if t < N:
            matrix[1 + t] = [0] * DIMENSION
            matrix[1 + t][0] = bit
        elif t < N + L:
            j = t - N
            counter = 1 + N
            matrix[counter][0] = bit
            matrix[counter][1 + SCHEDULE[j]] = 1 if bit == 0 else -1
            offset = N + 2
            for i in range(WIDTH):
                matrix[offset + i] = [0] * DIMENSION
            permutation = self.permutations[j][bit]
            for old, new in enumerate(permutation):
                matrix[offset + new][offset + old] = 1
        # Reading the label or padding preserves the state.
        return tuple(tuple(row) for row in matrix)

    @lru_cache(maxsize=None)
    def readout(self, t):
        row = [0] * DIMENSION
        if N <= t < N + L:
            row[0] = -1
            row[1 + SCHEDULE[t - N]] = 2
        elif t == N + L:
            row[1 + N] = 2
            row[N + 2:] = READOUT
        return tuple(row)

    @lru_cache(maxsize=None)
    def linear_state(self, prefix):
        if not prefix:
            return (1,) + (0,) * N + (0, 1, 0, 0, 0, 0)
        return matrix_vector(
            self.transition(len(prefix) - 1, prefix[-1]),
            self.linear_state(prefix[:-1]),
        )

    def future_functional(self, cut, future):
        row = self.readout(cut + len(future))
        for offset in range(len(future) - 1, -1, -1):
            row = row_matrix(row, self.transition(cut + offset, future[offset]))
        return row

    def oracle_simulator_p1(self, prefix):
        """Use only the public copy rule and the target's ordinary label."""
        t = len(prefix)
        if t < N or t >= H:
            return Fraction(1, 2)
        x = prefix[:N]
        if t < N + L:
            return Fraction(x[SCHEDULE[t - N]])
        copied_word = prefix[N:N + L]
        valid = all(bit == x[SCHEDULE[j]] for j, bit in enumerate(copied_word))
        return Fraction(self.target(x) if valid else 1)

    def active_probability(self, word):
        assert len(word) == H
        value = Fraction(1)
        for t, bit in enumerate(word):
            p1 = probability_one(self.direct_logit(word[:t]))
            value *= p1 if bit else 1 - p1
        return value


def audit_key(key):
    teacher = ToyTeacher(key)
    active_prefixes = [h for t in range(H) for h in words(t)]
    maximum_abs_logit = 0
    maximum_oracle_error = Fraction(0)
    for prefix in active_prefixes:
        direct = teacher.direct_logit(prefix)
        linear = dot(teacher.readout(len(prefix)), teacher.linear_state(prefix))
        assert direct == linear, (key, prefix, direct, linear)
        maximum_abs_logit = max(maximum_abs_logit, abs(direct))
        error = abs(probability_one(direct) - teacher.oracle_simulator_p1(prefix))
        assert error <= ETA, (key, prefix, error)
        maximum_oracle_error = max(maximum_oracle_error, error)
    assert maximum_abs_logit <= 2 * L + 1
    # Since ln(2) < 1, this integer inequality certifies |ell| < T exactly.
    assert SCALE * maximum_abs_logit < T

    cut_results = []
    factorization_entries_checked = 0
    for cut in range(H):
        histories = words(cut)
        futures = [f for length in range(H - cut) for f in words(length)]
        functionals = [teacher.future_functional(cut, f) for f in futures]
        matrix = []
        for history in histories:
            state = teacher.linear_state(history)
            row = []
            for future, functional in zip(futures, functionals):
                direct = teacher.direct_logit(history + future)
                assert direct == dot(state, functional)
                factorization_entries_checked += 1
                row.append(direct)
            matrix.append(row)
        rank = exact_rank(matrix)
        assert rank <= DIMENSION
        cut_results.append({
            "cut": cut,
            "rows": len(histories),
            "active_columns": len(futures),
            "exact_rank": rank,
        })

    # All later readouts are identically zero, not merely zero on sampled states.
    assert all(all(value == 0 for value in teacher.readout(t)) for t in range(H, T))
    for bit in (0, 1):
        assert teacher.transition(H - 1, bit) == tuple(map(tuple, identity_matrix(DIMENSION)))

    probabilities = {word: teacher.active_probability(word) for word in words(H)}
    total_mass = sum(probabilities.values(), Fraction(0))
    assert total_mass == 1
    assert all(value > 0 for value in probabilities.values())
    ideal = {}
    truth_table = []
    for x in words(N):
        copies = tuple(x[index] for index in SCHEDULE)
        label = teacher.target(x)
        assert READOUT[teacher.direct_bp_state(copies)] == 2 * label - 1
        ideal[x + copies + (label,)] = Fraction(1, 2 ** N)
        truth_table.append({"x": list(x), "label": label})
    actual_tv = sum(
        (abs(value - ideal.get(word, Fraction(0))) for word, value in probabilities.items()),
        Fraction(0),
    ) / 2
    expected_tv = 1 - (1 - ETA) ** (L + 1)
    assert actual_tv == expected_tv

    copy_marginal_matrix = []
    for x in words(N):
        row = []
        for future in words(N):
            probability = Fraction(1)
            prefix = x
            for bit in future:
                p1 = probability_one(teacher.direct_logit(prefix))
                probability *= p1 if bit else 1 - p1
                prefix += (bit,)
            row.append(probability)
        assert sum(row, Fraction(0)) == 1
        copy_marginal_matrix.append(row)
    marginal_rank = exact_rank(copy_marginal_matrix)
    assert marginal_rank == 2 ** N == 4

    return {
        "key": key,
        "target": "(x0 AND x1) XOR key",
        "truth_table": truth_table,
        "active_prefixes_checked": len(active_prefixes),
        "integer_factorization_entries_checked": factorization_entries_checked,
        "direct_and_linear_logits_agree_exactly": True,
        "all_prefix_oracle_error_bound_verified": True,
        "maximum_oracle_error": fraction_record(maximum_oracle_error),
        "maximum_abs_logit_divided_by_B": maximum_abs_logit,
        "certified_logit_upper_bound_using_ln2_lt_1": SCALE * maximum_abs_logit,
        "cut_matrices": cut_results,
        "maximum_exact_active_rank": max(item["exact_rank"] for item in cut_results),
        "padding_cut_ranks": {"cuts": [H, T - 1], "exact_rank": 0},
        "active_outcomes_enumerated": len(probabilities),
        "total_active_probability": fraction_record(total_mass),
        "all_active_probabilities_strictly_positive": True,
        "full_T_bit_support_follows_from_independent_fair_padding": True,
        "tv_to_ideal": fraction_record(actual_tv),
        "tv_exactly_equals_1_minus_1_minus_eta_to_L_plus_1": True,
        "first_N_copy_probability_marginal_exact_rank": marginal_rank,
    }


def main():
    assert H == 10 and L == 7 and DIMENSION == 9 and T >= H
    orbit = []
    point = 0
    for _ in range(WIDTH):
        orbit.append(point)
        point = COMMUTATOR[point]
    assert len(set(orbit)) == WIDTH and point == 0
    report = {
        "audit_kind": "finite exact structural verification, not cryptographic evidence",
        "parameters": {
            "n": N, "L": L, "active_horizon_H": H, "T": T,
            "d": DIMENSION, "B": "8 * ln(2)", "eta": fraction_record(ETA),
            "padding_length": T - H, "block_order": ["x", "copies", "label", "fair_padding"],
        },
        "compiler": {
            "description": "two identity copies, four S5 commutator instructions, one key toggle",
            "public_schedule_zero_indexed": list(SCHEDULE),
            "alpha": list(ALPHA), "beta": list(BETA),
            "commutator": list(COMMUTATOR), "commutator_orbit": orbit,
            "readout": list(READOUT),
            "limitation": "toy fixed public schedule; the general sweeping compiler is proved separately",
        },
        "keys": [audit_key(key) for key in (0, 1)],
        "all_assertions_passed": True,
        "limitations": [
            "The two-input target is easy and is not proposed as a PRF.",
            "No experiment tests or establishes a cryptographic assumption.",
            "All 2^H active outcomes are enumerated; 2^T padded outcomes are handled by exact factorization.",
            "The normalized-logit rank is exact; decimal values in the JSON are display aids only.",
        ],
    }
    destination = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name("audit_low_logit_rank_results.json")
    destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "all_assertions_passed": True,
        "result_file": str(destination.resolve()),
        "exact_ranks_by_key": [[cut["exact_rank"] for cut in key["cut_matrices"]] for key in report["keys"]],
        "active_prefixes_per_key": report["keys"][0]["active_prefixes_checked"],
        "active_outcomes_per_key": report["keys"][0]["active_outcomes_enumerated"],
        "first_copy_marginal_ranks": [key["first_N_copy_probability_marginal_exact_rank"] for key in report["keys"]],
        "tv_to_ideal": report["keys"][0]["tv_to_ideal"],
    }, indent=2))


if __name__ == "__main__":
    main()
