package functional_state

import NonNegativeInt.nonNegativeInt
import Double_.double

/** ex6.3 */
object IntDouble {
    def intDouble(rng: RNG): ((Int, Double), RNG) = {
        val (i, r1) = nonNegativeInt(rng)
        val (d, r2) = double(r1)
        ((i, d), r2)
    }

    def doubleInt(rng: RNG): ((Double, Int), RNG) = {
        val (d, r1) = double(rng)
        val (i, r2) = nonNegativeInt(r1)
        ((d, i), r2)
    }

    def double3(rng: RNG): ((Double, Double, Double), RNG) = {
        val (d1, r1) = double(rng)
        val (d2, r2) = double(r1)
        val (d3, r3) = double(r2)
        ((d1, d2, d3), r3)
    }
}