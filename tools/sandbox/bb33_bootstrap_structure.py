#!/usr/bin/env -S uv run python3
"""Structural probe of the distinct bootstrap-word language at sweep
reversals.

The bootstrap-novelty curve (`bb33_bootstrap_novelty.py`) answers HOW
MANY distinct words appear. This script answers WHAT KIND OF LANGUAGE
they form. Specifically:

1. **Length distribution** — are the words bounded? Linear-growing?
2. **Alphabet** — what symbols appear? Does each position have a fixed
   small alphabet?
3. **Prefix-determinism** — given a length-k prefix, is the next symbol
   determined? (Suffix automaton signal.)
4. **Substitutivity** — does the language look like the image of a
   morphism σ : Σ → Σ* applied iteratively? (Tests by checking whether
   long words decompose as concatenations of a small set of factor blocks.)
5. **Periodic structure** — fraction of words with non-trivial period.

Output is a structural report per (file, peak/valley, head_sig, side).

Usage:
    bb33_bootstrap_structure.py --in sim/531_burn_10M.reversals.json \\
                                --side right --kind valleys
    bb33_bootstrap_structure.py --in sim/397_burn_10M_v2.reversals.json \\
                                --side left --kind peaks
"""

import argparse
import json
import re
from collections import Counter, defaultdict
from pathlib import Path

BLOCK = re.compile(r"^([0-9]+)\^[\d_]+$")


def tok_sym(t):
    m = BLOCK.match(t)
    return m.group(1) if m else t


def find_longest_periodic_window(tokens, max_period=4):
    syms = [tok_sym(t) for t in tokens]
    n = len(syms)
    best = (None, None, 0, None)
    for p in range(1, max_period + 1):
        for start in range(max(0, n - p)):
            i = start
            while i + p < n and syms[i] == syms[i + p]:
                i += 1
            run_len = i - start + p
            if run_len > best[2]:
                pattern = tuple(syms[start:start + p])
                best = (p, start, run_len, pattern)
    return best


def decompose(side_tokens, side_name, max_period=4):
    """Same as bb33_bootstrap_novelty.decompose — keep in sync."""
    if len(side_tokens) < 4:
        return {"period": None, "pattern": None, "N": 0, "body_len": 0,
                "bootstrap": tuple(tok_sym(t) for t in side_tokens), "cap": ()}
    period, start, run_len, pattern = find_longest_periodic_window(side_tokens, max_period)
    if period is None or run_len < 2:
        return {"period": None, "pattern": None, "N": 0, "body_len": 0,
                "bootstrap": tuple(tok_sym(t) for t in side_tokens), "cap": ()}
    if side_name == "left":
        bootstrap = tuple(tok_sym(t) for t in side_tokens[:start])
        cap = tuple(tok_sym(t) for t in side_tokens[start + run_len:])
    else:
        cap = tuple(tok_sym(t) for t in side_tokens[:start])
        bootstrap = tuple(tok_sym(t) for t in side_tokens[start + run_len:])
    return {"period": period, "pattern": pattern, "body_len": run_len,
            "N": run_len // period, "bootstrap": bootstrap, "cap": cap}


def split_left_right(tokens):
    for i, t in enumerate(tokens):
        if t.startswith("<") and i + 1 < len(tokens):
            return tokens[:i], tokens[i + 2:]
        if t.endswith(">") and i > 0:
            return tokens[:i - 1], tokens[i + 1:]
    return None, None


def extract_bootstraps(snapshots, side):
    """Return (head_sig -> Counter of bootstrap words on the requested side)."""
    by_head = defaultdict(Counter)
    for s in snapshots:
        sig = (s["head_dir"], s["head_state"], s["cell"])
        left, right = split_left_right(s["tokens"])
        if left is None:
            continue
        L = decompose(left, "left")
        R = decompose(right, "right")
        boot = L["bootstrap"] if side == "left" else R["bootstrap"]
        by_head[sig][boot] += 1
    return by_head


def analyze_word_set(words, *, label, max_examples=5):
    """Run all structural probes on a Counter of words."""
    n_total = sum(words.values())
    n_distinct = len(words)
    if n_distinct == 0:
        print(f"\n  {label}: empty word set")
        return
    if n_distinct == 1:
        only = next(iter(words))
        print(f"\n  {label}: single word, count={n_total}")
        print(f"    word: {' '.join(only) if only else '(empty)'}")
        return

    print(f"\n  {label}")
    print(f"    distinct={n_distinct}  total_occurrences={n_total}  "
          f"unique_pct={100*n_distinct/n_total:.1f}%")

    # 1. Length distribution
    lens = sorted(len(w) for w in words)
    len_counter = Counter(len(w) for w in words)
    print(f"    length: min={lens[0]}  max={lens[-1]}  "
          f"mean={sum(lens)/len(lens):.2f}  median={lens[len(lens)//2]}")
    top_lens = len_counter.most_common(5)
    print(f"    length distribution (top 5): {top_lens}")

    # 2. Alphabet (per-position and global)
    global_alphabet = Counter()
    for w in words:
        for sym in w:
            global_alphabet[sym] += 1
    print(f"    alphabet: {dict(global_alphabet.most_common())}")

    # Per-position alphabet at first few positions (constant prefix?)
    max_pos_to_check = min(8, lens[-1])
    print(f"    per-position alphabet (first {max_pos_to_check} positions):")
    for pos in range(max_pos_to_check):
        pos_syms = Counter()
        for w in words:
            if len(w) > pos:
                pos_syms[w[pos]] += 1
        if len(pos_syms) == 1:
            sym, cnt = pos_syms.most_common(1)[0]
            print(f"      pos {pos}: {dict(pos_syms)}  ← deterministic")
        else:
            print(f"      pos {pos}: {dict(pos_syms.most_common(4))}")

    # 3. Prefix-determinism: for length-k prefix, is next symbol unique?
    print(f"    prefix-determinism test:")
    for k in (1, 2, 3, 4, 5):
        prefix_to_next = defaultdict(set)
        for w in words:
            for i in range(len(w) - k):
                prefix = w[i:i + k]
                next_sym = w[i + k]
                prefix_to_next[prefix].add(next_sym)
        if not prefix_to_next:
            continue
        deterministic = sum(1 for v in prefix_to_next.values() if len(v) == 1)
        total = len(prefix_to_next)
        max_branch = max(len(v) for v in prefix_to_next.values())
        print(f"      k={k}: {deterministic}/{total} prefixes deterministic  "
              f"({100*deterministic/total:.0f}%)  max_branch={max_branch}")

    # 4. Substitutivity / periodicity: max periodic factor
    has_period = 0
    period_examples = []
    for w in words:
        if len(w) < 2:
            continue
        for p in range(1, len(w)):
            if len(w) % p == 0 and all(w[i] == w[i % p] for i in range(len(w))):
                has_period += 1
                if len(period_examples) < 3:
                    period_examples.append((w, p))
                break
    print(f"    pure-periodic words: {has_period}/{n_distinct} "
          f"({100*has_period/n_distinct:.1f}%)")

    # 5. Top frequent words (preview structure)
    print(f"    top {max_examples} most-frequent words:")
    for w, cnt in words.most_common(max_examples):
        preview = ' '.join(w[:20]) + ('...' if len(w) > 20 else '')
        print(f"      ({cnt:6d}x) len={len(w):3d}  {preview}")

    # 6. Suffix structure: do long words extend shorter ones?
    sorted_by_len = sorted(words.keys(), key=len)
    if len(sorted_by_len) >= 10:
        # For each word, check if any shorter word is a prefix or suffix
        prefix_extends = 0
        suffix_extends = 0
        for w in sorted_by_len[1:]:
            for s in sorted_by_len:
                if len(s) >= len(w):
                    break
                if w[:len(s)] == s:
                    prefix_extends += 1
                    break
            for s in sorted_by_len:
                if len(s) >= len(w):
                    break
                if w[-len(s):] == s:
                    suffix_extends += 1
                    break
        print(f"    extension test: {prefix_extends}/{n_distinct-1} extend a shorter word as prefix; "
              f"{suffix_extends}/{n_distinct-1} as suffix")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp", required=True)
    ap.add_argument("--side", choices=("left", "right"), default="right")
    ap.add_argument("--kind", choices=("peaks", "valleys", "both"), default="both")
    ap.add_argument("--min-snapshots", type=int, default=50,
                    help="Skip head signatures with fewer than N samples")
    args = ap.parse_args()

    data = json.load(open(args.inp))
    label_prefix = Path(args.inp).stem

    kinds = ("peaks", "valleys") if args.kind == "both" else (args.kind,)

    for kind in kinds:
        snapshots = data[kind]
        by_head = extract_bootstraps(snapshots, args.side)
        print(f"\n========== {label_prefix} {kind.upper()} ({args.side.upper()} bootstrap) ==========")
        for sig, words in sorted(by_head.items()):
            n_snap = sum(words.values())
            if n_snap < args.min_snapshots:
                continue
            label = f"<{sig[0]} {sig[1]}, cell={sig[2]}>"
            analyze_word_set(words, label=label)


if __name__ == "__main__":
    main()
