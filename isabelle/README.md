# Isabelle/HOL proofs

This directory contains the proof development for floating-point conversion in
`fp-sls`.  The session is deliberately small and executable independently of
the Rust build.

## Prerequisites and build

The session was checked with:

- Isabelle2025-2;
- an AFP stable snapshot dated 2026-07-21
  (`AFP_VERSION=2025-2`).

Set portable paths for those installations, then build from the repository
root:

```sh
ISABELLE_DIR=/path/to/Isabelle2025-2
AFP_DIR=/path/to/afp-2026-07-21

"$ISABELLE_DIR/bin/isabelle" build \
  -A "$AFP_DIR" \
  -d isabelle FP_SLS_Verification
```

`-A` registers the AFP tree and `-d isabelle` registers this repository's
session. The session extends AFP's `IEEE_Floating_Point` session, which in turn
provides the `Word_Lib` and `HOL-Library` dependencies. Other AFP snapshots
compatible with Isabelle2025-2 may also work, but the dated snapshot above is
the verified configuration.

For an interactive session, first build as above and then start Isabelle/jEdit
with both session directories visible:

```sh
"$ISABELLE_DIR/bin/isabelle" jedit \
  -d "$AFP_DIR/thys" \
  -d isabelle -R FP_SLS_Verification isabelle/Fp_Round_Format.thy
```

## Checked model and results

The development models the exact conversion path in `src/data/fp.rs` as pure
HOL arithmetic over unbounded integers.  `round_integer`, `scale_ratio`, the
binary floor logarithm, significand carry, subnormal encoding, and
mode-dependent overflow records have the same mathematical decomposition as
Rust's `round_rational_to_format`.

`Fp_Arbitrary_Precision.thy` models a finite arbitrary-precision binary source
as a sign bit, an unbounded natural significand, and an integer exponent.  Its
value is

```text
(-1)^sign * significand * 2^exponent.
```

The source-to-rational theorem proves that the numerator and denominator fed
to the rounding model denote exactly this value; no intermediate floating
approximation occurs.  The sign is retained separately, so both source zero
signs are representable.  `Fp_Arbitrary_Precision_Sound.thy` additionally
defines an abstract source datatype with finite, NaN, and signed-infinity
cases.

The destination is AFP's type-indexed IEEE representation.  The bridge counts
AFP's stored fraction width as one less than the runtime precision (which
includes the hidden bit), proves all emitted fields fit, and proves exact
agreement of decoded finite values and signs.

### IEEE specification

`Fp_IEEE_Spec.thy` uses AFP's representation, `valof`, and classification
library, but defines a corrected relational rounding specification.  It does
not use AFP's current `IEEE.round` directly:

- AFP's RNA branch filters candidates to outward values before minimizing the
  error, which makes every inexact input round away rather than only resolving
  a nearest tie away;
- AFP itself marks the RNE `closest` preference as broken in some preference
  configurations.

The local `fp_round_rel` first minimizes over every finite destination value
and then applies the even-LSB or away-from-zero tie preference.  It also states
the exact nearest overflow threshold and the directed endpoint policies.

### Strict-green theorem coverage

The session currently proves all of the following without admissions:

- exact quotient/remainder behavior for RNE, RNA, RTZ, RTP, and RTN;
- normal and subnormal field well-formedness, carry, promotion to the smallest
  normal, and signed underflow to zero;
- global nearest-error minimality against every finite AFP value for normal
  and subnormal RNE/RNA results, including opposite-sign competitors;
- the full even-LSB and away-from-zero nearest preference for normal and
  subnormal RNE/RNA results, with no explicit midpoint premise, including
  lower-binade competitors and significand carry;
- least-above, greatest-below, and toward-zero extremality for all finite
  non-overflow directed results;
- equality of the dynamic maximum finite magnitude with AFP `fp_largest`, and
  equality of the dynamic nearest-overflow threshold with AFP `fp_threshold`;
- RNE/RNA infinity at and above that threshold, including the equality tie;
- RTP, RTN, and RTZ behavior beyond maximum finite, including both the
  `e > emax` branch and the delicate `e = emax` carry/no-carry branch;
- signed-zero correctness for every rounding mode, plus abstract preservation
  of NaN and both infinities.

At the arbitrary-precision source level, the checked `fp_signed_round_rel`
theorems now provide both reusable region results and their complete assembly:

- every zero source in all five modes;
- nonzero RTP/RTN/RTZ sources at or below maximum finite via a proved
  non-overflow partition, and beyond maximum finite with the IEEE endpoint or
  infinity selected by mode and sign;
- nonzero RNE/RNA sources below the nearest overflow threshold, automatically
  partitioned into subnormal and normal cases, and at or above the threshold;
- explicit subnormal, normal, overflow, and core-condition lemmas for clients
  that need an individual arithmetic region.

The theorem `round_ap_binary_signed_sound` assembles these regions into one
unconditional result for every `ap_binary_float` and all five rounding modes.
Its only premise is the runtime exponent-width requirement
`2 ≤ LENGTH('e)`; it covers signed zero, underflow, finite rounding, and
mode- and sign-dependent overflow.

The former normal-binade tie-preference gap is closed.  An equally-near
competitor below the binade boundary is ruled out by strict boundary
distance; every remaining competitor is lifted to the selected normal grid,
where integer parity or outwardness determines the preferred result.

### Refinement boundary

These are theorems about the HOL reference algorithm.  A successful build does
**not** yet prove that the compiled Rust code refines it.  In particular, the
following remain outside the formal result:

- correspondence between Rug's `Integer`/`Rational` extraction and the HOL
  numerator, denominator, sign, and exponent;
- correspondence between Rust control flow in `round_rational_to_format` or
  `fpconv` and the HOL functions;
- the MPFR/Rug contract used by the normal fast path;
- bounds and safety of runtime-width shifts and conversions; and
- NaN payload preservation beyond the chosen single-NaN abstraction.

The exact-rational fallback is the best next refinement target because its
arithmetic can be related to the HOL model without assuming MPFR rounding.

## Proof policy

Committed proof theories must contain no `sorry`, `oops`, axiomatized shortcut,
or proof-skipping configuration.  The session explicitly disables
`quick_and_dirty` and `skip_proofs`.  Isabelle nevertheless permits an explicit
`sorry`, so a green build alone is not sufficient; also run:

```sh
rg -n '\b(sorry|oops)\b|\baxiomatization\b|skip_proofs\s*=\s*true' \
  isabelle -g '*.thy' -g ROOT
```

The expected result is no matches.  Any future axiom or oracle use must be
called out explicitly as part of the trust boundary rather than silently added
to the proof development.
