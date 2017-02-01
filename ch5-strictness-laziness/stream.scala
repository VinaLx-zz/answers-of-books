/**
 * this file contains Stream and related problems
 */

package strictness_laziness

sealed trait Stream[+A] {

    def foldRight[B](z: ⇒ B)(f: (A, ⇒ B) ⇒ B): B = this match {
        case Empty ⇒ z
        case Cons(head, tail) ⇒ f(head(), tail().foldRight(z)(f))
    }

    @annotation.tailrec
    final def find(f: A ⇒ Boolean): Option[A] = this match {
        case Empty ⇒ None
        case Cons(h, t) ⇒ if (f(h())) Some(h()) else t().find(f)
    }

    // special case of `zipWith`
    def zip[B](s2: Stream[B]): Stream[(A, B)] = zipWith(s2)((_, _))

    /** ex5.1 */
    def toList: List[A] = this match {
        case Empty ⇒ Nil
        case Cons(head, tail) ⇒ head() :: tail().toList
    }

    // tailrec version of toList, walk through the stream twice
    def toList2: List[A] = {
        @annotation.tailrec
        def toReverseList(s: Stream[A], cur: List[A]): List[A] = s match {
            case Empty ⇒ cur
            case Cons(head, tail) ⇒ toReverseList(tail(), head() :: cur)
        }
        toReverseList(this, Nil).reverse
    }

    /** ex5.2 */
    def take(n: Int): Stream[A] = this match {
        case _ if n == 0 ⇒ Empty
        case Empty ⇒ Empty
        case Cons(head, tail) ⇒ Stream.cons(head(), tail().take(n - 1))
    }
    def drop(n: Int): Stream[A] = this match {
        case _ if n == 0 ⇒ this
        case Empty ⇒ Empty
        case Cons(head, tail) ⇒ tail().drop(n - 1)
    }

    /** ex5.3 */
    def takeWhile(p: A ⇒ Boolean): Stream[A] = this match {
        case Empty ⇒ Empty
        case Cons(head, tail) if !p(head()) ⇒ Empty
        case Cons(head, tail) ⇒ Stream.cons(head(), tail().takeWhile(p))
    }

    /** ex5.4 */
    def forAll(p: A ⇒ Boolean): Boolean = {
        foldRight(true)((a, b) ⇒ p(a) && b)
    }

    /** ex5.5 Requirement: use foldRight */
    def takeWhile2(p: A ⇒ Boolean): Stream[A] = {
        foldRight(Empty: Stream[A]) {
            (a, b) ⇒ if (p(a)) Stream.cons(a, b) else Empty
        }
    }

    /** ex5.6 */
    def headOption(): Option[A] = {
        foldRight(None: Option[A])((a, b) ⇒ Some(a))
    }

    /** ex5.7 */
    def map[B](f: A ⇒ B): Stream[B] = {
        foldRight(Empty: Stream[B])((a, sb) ⇒ Stream.cons(f(a), sb))
    }

    def filter(f: A ⇒ Boolean): Stream[A] = {
        foldRight(Empty: Stream[A]) {
            (a, sa) ⇒ if (f(a)) Stream.cons(a, sa) else sa
        }
    }

    def append[B >: A](s: ⇒ Stream[B]): Stream[B] = {
        foldRight(s)((a, sb) ⇒ Stream.cons(a, sb))
    }

    def flatMap[B](f: A ⇒ Stream[B]): Stream[B] = {
        foldRight(Empty: Stream[B])((a, sb) ⇒ f(a).append(sb))
    }

    /** ex5.13 Requirement: use unfold */
    def map2[B](f: A ⇒ B): Stream[B] = {
        Stream.unfold(this) {
            _ match {
                case Empty ⇒ None
                case Cons(head, tail) ⇒ Some((f(head()), tail()))
            }
        }
    }

    def take2(n: Int): Stream[A] = {
        Stream.unfold((n, this)) {
            _ match {
                case (c, Cons(head, tail)) if c > 0 ⇒
                    Some((head(), (c - 1, tail())))
                case _ ⇒ None
            }
        }
    }

    def takeWhile3(p: A ⇒ Boolean) = {
        Stream.unfold(this) {
            _ match {
                case Cons(head, tail) if p(head()) ⇒ Some((head(), tail()))
                case _ ⇒ None
            }
        }
    }

    def zipWith[B, C](s: Stream[B])(f: (A, B) ⇒ C): Stream[C] = {
        Stream.unfold((this, s)) {
            _ match {
                case (Cons(h1, t1), Cons(h2, t2)) ⇒
                    Some((f(h1(), h2()), (t1(), t2())))
                case _ ⇒ None
            }
        }
    }

    def zipAll[B](s: Stream[B]): Stream[(Option[A], Option[B])] = {
        Stream.unfold((this, s)) {
            _ match {
                case (Cons(head, tail), Empty) ⇒
                    Some(((Some(head()), None), (tail(), Empty)))
                case (Empty, Cons(head, tail)) ⇒
                    Some(((None, Some(head())), (Empty, tail())))
                case (Cons(h1, t1), Cons(h2, t2)) ⇒
                    Some(((Some(h1()), Some(h2())), (t1(), t2())))
                case _ ⇒ None
            }
        }
    }

    /** ex5.14 */
    def startsWith[B](s: Stream[B]): Boolean = (this, s) match {
        case (_, Empty) ⇒ true
        case (Empty, _) ⇒ false
        case (Cons(h1, t1), Cons(h2, t2)) ⇒
            h1() == h2() && (t1() startsWith t2())
    }

    /** ex5.15 */
    def tails: Stream[Stream[A]] = this match {
        case Empty ⇒ Stream(Stream(): Stream[A])
        case Cons(head, tail) ⇒
            lazy val ts = tail().tails
            ts match {
                case c @ Cons(h, t) ⇒
                    Stream.cons(Stream.cons(head(), h()), c)
                case _ ⇒ ???
            }
    }
    /** ex5.16 */
    def scanRight[B](z: B)(f: (A, ⇒ B) ⇒ B): Stream[B] = this match {
        // did't quite understand, seems that both this implementation and answer
        // don't really exploit laziness
        case Empty ⇒ Stream(z)
        case Cons(head, tail) ⇒
            lazy val ts = tail().scanRight(z)(f)
            ts match {
                case c @ Cons(h, t) ⇒
                    Stream.cons(f(head(), h()), c)
                case _ ⇒ ???
            }
    }

}
case object Empty extends Stream[Nothing]
case class Cons[+A](head: () ⇒ A, tail: () ⇒ Stream[A]) extends Stream[A]

object Stream {
    def cons[A](h: ⇒ A, t: ⇒ Stream[A]): Stream[A] = {
        lazy val head = h
        lazy val tail = t
        Cons(() ⇒ head, () ⇒ tail)
    }

    def empty[A]: Stream[A] = Empty

    def apply[A](as: A*): Stream[A] = {
        if (as.isEmpty) empty
        else cons(as.head, apply(as.tail: _*))
    }

    /** ex5.11 */
    def unfold[A, S](z: S)(f: S ⇒ Option[(A, S)]): Stream[A] = f(z) match {
        case None ⇒ Empty
        case Some((a, s)) ⇒ cons(a, unfold(s)(f))
    }

    // then comes testing procedures

    def testToList() = {
        println("Testing Stream.toList")
        val s1 = Stream(1, 2, 3, 4)
        val s2 = Stream.empty[Int]
        println(s1.toList)
        println(s2.toList)
        println(s1.toList2)
        println(s2.toList2)
        println("")
    }

    def testTake() = {
        println("Testing Stream.take")
        val s1 = Stream(1, 2, 3, 4)
        val s2 = Stream.empty[Int]
        println(s1.take(2).toList)
        println(s1.take(4).toList)
        println(s1.take(5).toList)
        println(s1.take(0).toList)
        println(s2.take(1).toList)
        println("")

        println("Testing Stream.take2")
        println(s1.take2(2).toList)
        println(s1.take2(4).toList)
        println(s1.take2(5).toList)
        println(s1.take2(0).toList)
        println(s2.take2(1).toList)
        println("")
    }

    def testDrop() = {
        println("Testing Stream.drop")
        val s1 = Stream(1, 2, 3, 4)
        val s2 = Stream.empty[Int]
        println(s1.drop(0).toList)
        println(s1.drop(1).toList)
        println(s1.drop(4).toList)
        println(s1.drop(5).toList)
        println(s2.drop(2).toList)
        println("")
    }

    def testTakeWhile() = {
        println("Testing Stream.takeWhile")
        val s1 = Stream(1, 2, 3, 4)
        val s2 = Stream.empty[Int]
        println(s1.takeWhile(_ < 0).toList)
        println(s1.takeWhile(_ < 3).toList)
        println(s1.takeWhile(_ < 5).toList)
        println(s2.takeWhile(a ⇒ true).toList)
        println("")

        println("Testing Stream.takeWhile2")
        println(s1.takeWhile2(_ < 0).toList)
        println(s1.takeWhile2(_ < 3).toList)
        println(s1.takeWhile2(_ < 5).toList)
        println(s2.takeWhile2(a ⇒ true).toList)
        println("")

        println("Testing Stream.takeWhile3")
        println(s1.takeWhile3(_ < 0).toList)
        println(s1.takeWhile3(_ < 3).toList)
        println(s1.takeWhile3(_ < 5).toList)
        println(s2.takeWhile3(a ⇒ true).toList)
        println("")
    }

    def testAppend() = {
        println("Testing Stream.append")
        val s1 = {
            println("stream evaluated")
            Stream(5, 6, 7, 8)
        }
        val s2 = Stream(1, 2, 3, 4)
        val s3 = s2.append(s1)
        println(s"after append: ${s3.toList}\n")
    }

    def testZipWith() = {
        println("Testing Stream.zipWith")
        import Fibs._
        import From._
        val s = fibs.zipWith(from(0))(_ + _)
        println(s.take(10).toList)
        println("")
    }

    def testZipAll() = {
        println("Testing Stream.zipAll")
        import Fibs._
        import From._
        val s = (fibs take 10) zipAll ((from(0)) take 5)
        println(s.toList)
        println("")
    }

    def testStartsWith() = {
        println("Testing Stream.startsWith")
        import Fibs._
        import From._
        println(fibs startsWith from(0))
        println(fibs startsWith (from(0) take 2))
        println(Stream(1, 2, 3) startsWith Stream(1, 2, 3, 4))
        println("")
    }

    def testTails() = {
        println("Testing Stream.tails")
        val s = Stream(1, 2, 3, 4, 5)
        for (l ← (s.tails toList)) println(l.toList)
        println("")
    }

    def testScanRight() = {
        println("Testing Stream.scanRight")
        val s = Stream(1, 2, 3, 4, 5)
        println(s.scanRight(0)(_ + _).toList)
        println("")
    }

    def main(argv: Array[String]) = {
        testToList()
        testTake()
        testDrop()
        testTakeWhile()
        testAppend()
        testZipWith()
        testZipAll()
        testStartsWith()
        testTails()
        testScanRight()
    }
}