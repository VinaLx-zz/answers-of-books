/**
 * this file contains the random generator and related problems
 */

package functional_state

trait RNG {
    def nextInt: (Int, RNG)
}

case class SimpleRNG(seed: Long) extends RNG {
    def nextInt: (Int, RNG) = {
        val new_seed = (seed * 0x5DEECE66DL + 0xBL) & 0xFFFFFFFFFFFFL
        val next_rng = SimpleRNG(new_seed)
        val n = (new_seed >>> 16).toInt
        (n, next_rng)
    }
}

object RNG {
    type Rand[+A] = (RNG ⇒ (A, RNG))

    def map[A, B](s: Rand[A])(f: A ⇒ B): Rand[B] = { rng ⇒
        val (a, r1) = s(rng)
        (f(a), r1)
    }

    /** ex6.6 */
    def map2[A, B, C](a: Rand[A], b: Rand[B])(f: (A, B) ⇒ C): Rand[C] = { rng ⇒
        val (aa, ra) = a(rng)
        val (bb, rb) = b(ra)
        (f(aa, bb), rb)
    }

    /** ex6.7 */

    // my implementation with foldLeft
    def sequence[A](fs: List[Rand[A]]): Rand[List[A]] = {
        fs.foldLeft[Rand[List[A]]](rng ⇒ (Nil, rng)) { (rl, r) ⇒
            rng ⇒
                val (l, r1) = rl(rng)
                val (a, r2) = r(r1)
                (a :: l, r2)
        }
    }
    // answer ref implementation by fold right and map, far more elegant
    def sequence2[A](fs: List[Rand[A]]): Rand[List[A]] = {
        fs.foldRight[Rand[List[A]]](rng ⇒ (Nil, rng)) {
            (r, rl) ⇒ map2(r, rl)(_ :: _)
        }
    }
    // or foldleft + reverse
    def sequence3[A](fs: List[Rand[A]]): Rand[List[A]] = {
        map(fs.foldLeft[Rand[List[A]]](rng ⇒ (Nil, rng)) {
            (rl, r) ⇒ map2(r, rl)(_ :: _)
        })(_.reverse)
    }

    /** ex6.8 */
    def flatMap[A, B](f: Rand[A])(g: A ⇒ Rand[B]): Rand[B] = { rng ⇒
        val (a, r1) = f(rng)
        val rand = g(a)
        rand(r1)
    }

    /** ex6.9 */
    def mapByFlatMap[A, B](r: Rand[A])(f: A ⇒ B): Rand[B] = {
        flatMap(r)(a ⇒ rng ⇒ (f(a), rng))
    }

    def map2ByFlatMap[A, B, C](ra: Rand[A], rb: Rand[B])(f: (A, B) ⇒ C): Rand[C] = {
        flatMap(ra)(a ⇒ map(rb)(b ⇒ f(a, b)))
    }
}