"""Compare the squared distance ratios of the integer sets in Appendix C."""
from itertools import combinations
from flint import arb, ctx

# The regular m-gon's diameter and shortest chord share the factor 2r.
# For these m >= 8 the center changes neither extreme distance.
EXAMPLES = [
    ([(15,28), (5,22), (25,22), (15,16), (0,11), (30,11), (15,4), (4,0), (26,0)], (136,925)),
    ([(14,27), (5,22), (22,22), (14,17), (0,14), (27,14), (11,8), (2,4), (25,4), (16,0)], (89,733)),
    ([(9,17), (15,16), (4,14), (11,12), (6,9), (16,9), (0,8), (11,6), (4,4), (16,3), (9,1)], (29,289)),
]


def main():
    ctx.prec = 160
    for points, extremes in EXAMPLES:
        m = len(points) - 1
        squared = [(x-a)**2 + (y-b)**2 for (x,y), (a,b) in combinations(points, 2)]
        assert len(squared) == len(points)*m//2
        assert (min(squared), max(squared)) == extremes
        angle = arb.pi()/m
        ring_ratio = ((m//2 * angle).sin()/angle.sin())**2
        assert arb(max(squared))/min(squared) < ring_ratio
        print(f"n={len(points)}: R^2={max(squared)}/{min(squared)} is strictly below the centered polygon value.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run with assertions enabled.")
    main()
