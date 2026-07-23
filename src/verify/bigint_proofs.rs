// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
verus! {

use super::bigint_assumptions::bigint_bits_ensures;
use vstd::arithmetic::power2::{lemma2_to64_rest, lemma_pow2_strictly_increases, pow2};

pub proof fn lemma_bigint_bits_le_53()
    ensures
        forall|value: int, bits: nat| #[trigger] bigint_bits_ensures(value, bits) ==>
            ((bits <= 53) == (-9_007_199_254_740_992 < value < 9_007_199_254_740_992)),
{
    lemma2_to64_rest();
    assert(pow2(53) == 9_007_199_254_740_992);
    assert forall|value: int, bits: nat| #[trigger] bigint_bits_ensures(value, bits) implies
        ((bits <= 53) == (-9_007_199_254_740_992 < value < 9_007_199_254_740_992)) by
    {
        if bigint_bits_ensures(value, bits) {
            if bits < 53 {
                lemma_pow2_strictly_increases(bits, 53);
            } else if bits > 53 {
                assert(!( -(pow2(53) as int) < value < pow2(53) ));
            }
        }
    }
}

}
