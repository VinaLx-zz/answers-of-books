package testing

import functional_state._
import NonNegativeLt.nonNegativeLessThan
import NonNegativeInt.nonNegativeInt
import parallelism.part1._

case class Gen[+A](sample: State[RNG, A]) {
    def map[B](f: A ⇒ B): Gen[B] = {
        Gen[B](sample map (a ⇒ f(a)))
    }

    def map2[B, C](gb: Gen[B])(f: (A, B) ⇒ C): Gen[C] = {
        Gen[C](sample.map2(gb.sample)(f))
    }

    def **[B](gb: Gen[B]): Gen[(A, B)] = {
        map2(gb)(_ -> _)
    }

    /** ex8.6 */
    def flatMap[B](f: A ⇒ Gen[B]): Gen[B] = {
        Gen[B](sample flatMap (a ⇒ f(a).sample))
    }

    def listOfN(size: Gen[Int]): Gen[List[A]] = {
        size flatMap (n ⇒ Gen.listOfN(n, this))
    }

    /** ex8.10 */
    def unsized: SGen[A] = SGen(_ ⇒ this)
}

object Gen {
    /** ex8.4 */
    def choose(start: Int, stopExclusive: Int): Gen[Int] = {
        val temp = State(nonNegativeLessThan(stopExclusive - start))
        Gen[Int](temp.map(_ + start))
    }

    /** ex8.5 */
    def unit[A](a: ⇒ A): Gen[A] = Gen[A](State.unit[RNG, A](a))

    def boolean: Gen[Boolean] = {
        Gen[Boolean](
            State(nonNegativeInt).map(i ⇒ if (i % 2 == 0) false else true))
    }

    def listOfN[A](n: Int, g: Gen[A]): Gen[List[A]] = {
        Gen[List[A]](State.sequence(List.fill(n)(g.sample)))
    }

    /** ex8.7 */
    def union[A](g1: Gen[A], g2: Gen[A]): Gen[A] = {
        boolean flatMap (b ⇒ if (b) g1 else g2)
    }

    /** ex8.8 */
    def double: Gen[Double] = Gen(State(Double_.double))

    def weighted[A](p1: (Gen[A], Double), p2: (Gen[A], Double)) = {
        val weight1 = p1._2 / (p1._2 + p2._2)
        double flatMap (d ⇒ if (d < weight1) p1._1 else p2._1)
    }

    /** ex8.11 */
    def listOf[A](g: Gen[A]): SGen[List[A]] = SGen(n ⇒ listOfN(n, g))

    /** ex8.13 */
    def listOf1[A](g: Gen[A]): SGen[List[A]] = SGen(n ⇒ listOfN(1 max n, g))

    /** ex8.16 open question */
    def choosePar(start: Int, stopExclusive: Int): Gen[Par.Par[Int]] = {
        choose(start, stopExclusive) map (i ⇒ Par.fork(Par.unit(i)))
    }

}