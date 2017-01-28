package functional_state

object Ints {
    /** ex6.4 */
    def ints(count: Int)(rng: RNG): (List[Int], RNG) = {
        @annotation.tailrec
        def intsImpl(c: Int, l: List[Int], r: RNG): (List[Int], RNG) = {
            if (c > 0) {
                val (ni, nr) = r.nextInt
                intsImpl(c - 1, ni :: l, nr)
            } else {
                (l, r)
            }
        }
        intsImpl(count, Nil, rng)
    }

    /** ex6.7 Requirement: use sequence*/
    def ints2(count: Int)(rng: RNG): (List[Int], RNG) = {
        import RNG._
        sequence(List.fill[Rand[Int]](count)(_.nextInt))(rng)
    }
}