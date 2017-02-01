package testing
package prop2

import functional_state._
import Prop._
import strictness_laziness._
import parallelism.part1._
import Par._
import java.util.concurrent._

sealed trait Result {
    def isFalsified: Boolean
}

case object Passed extends Result {
    def isFalsified = false
}

case object Proved extends Result {
    def isFalsified = false
}

case class Falsified(
    failure: FailedCase, successes: SuccessCount) extends Result {
    def isFalsified = true
}

case class Prop(run: (MaxSize, TestCases, RNG) ⇒ Result) {
    /** ex8.9 */
    def &&(rhs: Prop): Prop = Prop { (maxsize, n, rng) ⇒
        Prop.this.run(maxsize, n, rng) match {
            case Passed ⇒ rhs.run(maxsize, n, rng)
            case fail ⇒ fail
        }
    }
    def ||(rhs: Prop): Prop = Prop { (maxsize, n, rng) ⇒
        Prop.this.run(maxsize, n, rng) match {
            case Passed ⇒ Passed
            case _ ⇒ rhs.run(maxsize, n, rng)
        }
    }
}

object Prop {
    type SuccessCount = Int
    type FailedCase = String
    type TestCases = Int
    type MaxSize = Int

    def forAll[A](as: Gen[A])(f: A ⇒ Boolean): Prop = Prop { (maxsize, n, rng) ⇒
        randomStream(as)(rng).zip(From.from(0)).take(n).map {
            case (a, i) ⇒ try {
                if (f(a)) Passed else Falsified(a.toString, i)
            } catch {
                case e: Exception ⇒ Falsified(buildMessage(a, e), i)
            }
        }.find(_.isFalsified).getOrElse(Passed)
    }

    def randomStream[A](g: Gen[A])(rng: RNG): Stream[A] = {
        Stream.unfold(rng)(rng ⇒ Some(g.sample.run(rng)))
    }

    def buildMessage[A](s: A, e: Exception): String = {
        s"Test case: $s\n" +
            s"generated an exception: ${e.getMessage}.\n" +
            s"Stack trace: ${e.getStackTrace.mkString("\n")}"
    }

    def forAll[A](g: SGen[A])(f: A ⇒ Boolean): Prop = forAll(g.forSize)(f)

    def forAll[A](g: Int ⇒ Gen[A])(f: A ⇒ Boolean): Prop = Prop {
        (max, n, rng) ⇒
            val casesPerSize = (n + max - 1) / max
            val props: Stream[Prop] =
                From.from(0).take((n min max) + 1).map(i ⇒ forAll(g(i))(f))
            val prop: Prop =
                props.map(p ⇒ Prop { (max, _, rng) ⇒
                    p.run(max, casesPerSize, rng)
                }).toList.reduce(_ && _)
            prop.run(max, n, rng)
    }

    def run(
        p: Prop, max_size: MaxSize = 100, test_cases: TestCases = 100,
        rng: RNG = SimpleRNG(System.currentTimeMillis)): Unit = {

        p.run(max_size, test_cases, rng) match {
            case Falsified(msg, n) ⇒
                println(s"! Falsified after $n passed tests:\n $msg")
            case Passed ⇒
                println(s"+ OK, passed $test_cases tests.")
            case Proved ⇒
                println(s"+ OK, proved property")
        }
    }

    def check(p: ⇒ Boolean): Prop = Prop { (_, _, _) ⇒
        if (p) Proved else Falsified("()", 0)
    }

    def forAllPar[A](g: Gen[A])(f: A ⇒ Par[Boolean]): Prop = {
        val s = Gen.weighted(
            Gen.choose(1, 4).map[ExecutorService](
                Executors.newFixedThreadPool) -> 0.75,
            Gen.unit(Executors.newCachedThreadPool) -> 0.25)
        forAll(s ** g) { case (es, a) ⇒ f(a)(es).get }
    }

    /** ex8.14 */
    def ex8_14(): Unit = {
        val gen = Gen.choose(0, 100)
        val sgen = Gen.listOf1(gen)
        val prop = forAll(sgen) { l ⇒
            val sorted_seq = l.toIndexedSeq.sorted
            sorted_seq.zip(0 to sorted_seq.size).forall {
                case (n, i) ⇒
                    if (i != l.size - 1) n <= sorted_seq(i + 1)
                    else true
            }
        }
        run(prop, max_size = 50, test_cases = 100)
    }

    /** ex8.17 */
    def ex8_17(): Unit = {
        val p = forAllPar(Gen.choose(0, 100))(
            a ⇒ Par.equal(unit(a), fork(unit(a))))
        run(p)
    }
}