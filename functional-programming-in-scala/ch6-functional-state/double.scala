package functional_state

import NonNegativeInt.nonNegativeInt

object Double_ {
    /** ex6.2 */
    def double(rng: RNG): (Double, RNG) = {
        val (i, r) = nonNegativeInt(rng)
        (i / (Int.MaxValue.toDouble + 1), r)
    }

    /** ex6.5 Requirment: use map */
    def double2(rng: RNG): (Double, RNG) = {
        RNG.map(nonNegativeInt)(_ / (Int.MaxValue.toDouble + 1))(rng)
    }
}
