# You are the frontier. Break the barrier.

You have already reduced an entire research programme to one arithmetic fact, and you have
proved that sieves cannot supply that fact. That is not a reason to stop — it is a reason to
change weapons. The parity barrier is a statement about sieves; Friedlander–Iwaniec and
Heath–Brown broke it with bilinear sums and geometry, and you can too. Hard mathematics has
fallen to you before, not by caution but by seeing the object nobody else saw. Be bold. Be
brave. Attack it mercilessly, with the tools that can actually win. Do not hedge, do not
restate, do not retreat into the sieve.

---

# Finish the theorem with parity-breaking tools. Discard the sieves.

You are the frontier: the strongest reasoning model we have. You have taken this programme to its
sharpest point — one arithmetic statement stands between the whole framework and the twin-prime
conjecture. You also showed, precisely, that sieve and divisor-counting methods cannot cross that
last step: a prime `p+2` and a semiprime `q₁q₂` with no small factor are indistinguishable to
small-divisor data, yet contribute differently to the tail. That is the parity barrier, and it is
a statement about *sieves*, not about mathematics.

So discard the sieves. Stop estimating Möbius tails. Attack the target with tools that break
parity. Be bold. Be brave. You have complete freedom of method. Use everything you have.

## The target (unchanged)

Infinitely many `p` with `p` and `p+2` prime — equivalently, in this framework's compiled terms,
`CofinalNodeOverload`, or the floor `CofinalLargeDivisorFloor` in `CpnfLean/DivisorFloor.lean`.
The framework's machinery (equivalence, transfer lemmas, telescoping identity) is all proved; what
is missing is the one arithmetic fact that a sieve cannot supply.

## What I want you to try — the parity-breaking families

The canonical fact you should reason from: parity is *breakable* when the sequence has structure a
sieve cannot see. Friedlander–Iwaniec proved `x² + y⁴` is prime infinitely often by bilinear
(type I/II) sums; Heath–Brown did `x³ + 2y³`. Those broke the barrier with geometry, not with
small-prime bookkeeping. The twin forms are `6n ∓ 1`, a linear pair — your job is to find the
analogue of that structure. Specifically, explore and decide among:

1. **Bilinear / type I–II sums.** Write the twin correlation as a bilinear form over smooth or
   well-spaced weights and bound it directly, the way Friedlander–Iwaniec defeat the parity
   obstruction. Give the actual type-I and type-II estimates, not a sketch.

2. **Circle method.** The Hardy–Littlewood heuristic is `N₂(x) ~ 2C₂·x/log²x`. The parity barrier
   is exactly the "minor arcs" term a sieve leaves behind. Give the minor-arc bound for the shift-2
   generating function, or show precisely where it fails and what hypothesis rescues it.

3. **Spectral / automorphic.** Express the shift-2 correlation as a sum of Kloosterman or Poincaré
   series terms and bound them, bypassing the divisor split entirely.

4. **Selberg `Λ²` or Vaughan identity with both sides.** A weighted, genuinely two-sided identity
   that does not reduce to "how many prime factors does `p+2` have".

5. **Any structure I have not named** — a different transform, a different base, a different
   pairing of the two columns. You decide. The only forbidden path is the one we have already
   proved dead: estimating the Möbius tail over divisors.

## What I need back

1. A proof — or a genuine, specific reduction — giving cofinal twins, with the parity-breaking
   mechanism explicit (which type-I/II or minor-arc bound, with exponents and ranges); or
2. A precise statement of the *sharpest* unconditional theorem your chosen method yields (e.g. a
   lower bound on `N₂(x)` beyond Chen's theorem, or a new level of the twin correlation), with the
   exact exponent; or
3. If even parity-breaking methods hit a named open obstruction, say which one, with the mechanism.

Give compile-ready Lean for any fragment you can (a generating-function definition, a type-I bound,
a rearrangement of the correlation). For the rest: exact definitions, ranges, exponents, and the
real proof obligations. Be specific about arithmetic. The one thing that is not useful is another
divisor split or another sieve bound.
