package functional_state

object NonNegativeInt {
    /** ex6.1 */
    def nonNegativeInt(rng: RNG): (Int, RNG) = {
        val (i, r) = rng.nextInt
        val nni = if (i == Int.MinValue) 0 else math.abs(i)
        (nni, r)
    }
}