"""Exact supplementary certificate; the uniform proof is in paper/main.tex.

The sparse verification visits generated sums below c+m, not all c+m integers.
No unproved conjecture, floating point, or conjectural pruning is used.
"""
import argparse
from heapq import heappop, heappush
import json
from math import comb
from pathlib import Path


def certificate(scale=1_000_000):
    if scale < 1_000_000:
        raise ValueError('The proved family requires M >= 1000000')
    m, c = 4 * scale, 32 * scale
    generators = [m, m + 1] + [5 * scale + 10**i for i in range(1, 6)]
    sums, queue = {0}, [0]
    while queue:
        x = heappop(queue)
        for g in generators:
            y = x + g
            if y < c + m and y not in sums:
                sums.add(y)
                heappush(queue, y)
    left = {x for x in sums if x < c}
    threshold = {x for x in sums if c <= x < c + m}
    primitives = sorted(x for x in left - {0}
                        if not any(g < x and x - g in sums for g in generators))
    # Independently check every threshold value is a sum of two positive left values.
    positive_left = sorted(left - {0})
    double = {a + b for i, a in enumerate(positive_left)
              for b in positive_left[i:] if c <= a + b < c + m}
    rows = []
    for t in range(8):
        choices = comb(t + 4, 4)
        low = max(0, 8 - (5*t)//4)
        right = 9 - (5*t)//4
        rows.append(dict(t=t, compositions=choices,
                         left=choices*low*(low+1)//2,
                         threshold=choices*right))
    k, ell, s = len(left), len(primitives), len(threshold)
    assert primitives == generators
    assert c-1 not in sums
    assert double == threshold
    assert k == sum(row['left'] for row in rows) == 2024
    assert s == sum(row['threshold'] for row in rows) == 1772
    assert ell == 7 and k*ell-8*s == -8
    return dict(scale=scale, multiplicity=m, conductor=c, generators=generators,
                first_gap=1, depth=8, rho=0, k=k, ell=ell, s=s, r=m-s,
                E=k*ell-8*s, W=k*(ell+m-s)-c,
                conductor_predecessor_absent=True,
                threshold_equals_positive_double_sumset=True,
                degree_counts=rows,
                method='Exact sparse check; the infinite-family proof is symbolic.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scale', type=int, default=1_000_000)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = certificate(args.scale)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
