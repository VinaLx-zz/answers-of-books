package functional_state

import NonNegativeInt.nonNegativeInt

object NonNegativeLt {
    /** ex6.8 Requirment: use flatMap */
    def nonNegativeLessThan(n: Int): RNG.Rand[Int] = {
        RNG.flatMap(nonNegativeInt) { i ⇒
            val m = i % n
            if (i - m + (n - 1) >= 0) rng ⇒ (m, rng)
            else nonNegativeLessThan(n)
        }
    }
}