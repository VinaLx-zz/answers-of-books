/**
 * this file contains the List and all related problems
 */
package data_structure

sealed trait List[+A]

case object Nil extends List[Nothing]
case class Cons[+A](head: A, tail: List[A]) extends List[A]

object List {
    def apply[A](elems: A*): List[A] = {
        if (elems.isEmpty) Nil
        else Cons(elems.head, apply(elems.tail: _*))
    }

    def foldRight[A, B](list: List[A], z: B)(f: (A, B) ⇒ B): B =
        list match {
            case Nil ⇒ z
            case Cons(head, tail) ⇒ f(head, foldRight(tail, z)(f))
        }

    /** ex3.2 */
    def tail[A](list: List[A]): List[A] = list match {
        case Nil ⇒ Nil
        case Cons(head, tail) ⇒ tail
    }

    /** ex3.3 */
    def setHead[A](list: List[A], value: A) = list match {
        case Nil ⇒ Nil
        case Cons(head, tail) ⇒ Cons(value, tail)
    }

    /** ex3.4 */
    def drop[A](list: List[A], n: Int): List[A] = (list, n) match {
        case (Nil, _) ⇒ Nil
        case (list, 0) ⇒ list
        case (Cons(head, tail), n) ⇒ drop(tail, n - 1)
    }

    /** ex3.5 */
    def dropWhile[A](list: List[A], pred: A ⇒ Boolean): List[A] = list match {
        case Nil ⇒ Nil
        case cur @ Cons(head, tail) ⇒
            if (pred(head)) dropWhile(tail, pred)
            else cur
    }

    /** ex3.6 */
    def init[A](list: List[A]): List[A] = list match {
        case Nil ⇒ Nil
        case Cons(last, Nil) ⇒ Nil
        case Cons(head, tail) ⇒ Cons(head, init(tail))
    }

    /** ex3.9 - Requirement: use foldRight */
    def length[A](list: List[A]): Int = {
        foldRight(list, 0)((a, cur) ⇒ (cur + 1))
    }

    /** ex3.10 */
    @annotation.tailrec
    def foldLeft[A, B](list: List[A], z: B)(f: (B, A) ⇒ B): B =
        list match {
            case Nil ⇒ z
            case Cons(head, tail) ⇒ foldLeft(tail, f(z, head))(f)
        }

    /** ex3.11 Requirement: use foldLeft */
    def sum(list: List[Double]) = foldLeft(list, 0.0)(_ + _)

    def product(list: List[Double]) = foldLeft(list, 1.0)(_ * _)

    def length2(list: List[Double]) = foldLeft(list, 0)((cur, a) ⇒ cur + 1)

    /** ex3.12 */
    def reverse[A](list: List[A]) = foldLeft[A, List[A]](list, Nil) {
        (cur, elem) ⇒ Cons(elem, cur)
    }

    /** ex3.13 Requirement: use another fold to implement fold*/
    def foldLeft2[A, B](list: List[A], z: B)(f: (B, A) ⇒ B) = {
        def fold_aux(a: A, f2: B ⇒ B): B ⇒ B = b ⇒ f2(f(b, a))
        foldRight(list, (b: B) ⇒ b)(fold_aux)(z)
    }

    def foldRight2[A, B](list: List[A], z: B)(f: (A, B) ⇒ B) = {
        def fold_aux(f2: B ⇒ B, a: A): B ⇒ B = b ⇒ f2(f(a, b))
        foldLeft(list, (b: B) ⇒ b)(fold_aux)(z)
    }

    /** ex3.14 */
    def append[A](l1: List[A], l2: List[A]) = {
        foldRight[A, List[A]](l1, l2)(Cons(_, _))
    }

    /** ex3.15 */
    def concat[A](ll: List[List[A]]): List[A] = {
        foldRight[List[A], List[A]](ll, Nil)(append)
    }

    /** ex3.16 */
    def increment(list: List[Int]): List[Int] = {
        foldRight[Int, List[Int]](list, Nil)((x, l) ⇒ Cons(x + 1, l))
    }

    /** ex3.17 */
    def double2String(list: List[Double]): List[String] = {
        foldRight[Double, List[String]](list, Nil)((x, l) ⇒ Cons(x.toString, l))
    }

    /** ex3.18 */
    def map[A, B](list: List[A])(f: A ⇒ B): List[B] = {
        foldRight[A, List[B]](list, Nil)((a, l) ⇒ Cons(f(a), l))
    }

    /** ex3.19 */
    def filter[A](list: List[A])(f: A ⇒ Boolean): List[A] = {
        def filter_aux(a: A, l: List[A]): List[A] = {
            if (f(a)) Cons(a, l)
            else l
        }
        foldRight[A, List[A]](list, Nil)(filter_aux)
    }

    /** ex3.20 */
    def flatMap[A, B](list: List[A])(f: A ⇒ List[B]) = {
        foldRight[A, List[B]](list, Nil)((x, l) ⇒ append(f(x), l))
    }

    /** ex3.21 */
    def filter2[A](list: List[A])(f: A ⇒ Boolean): List[A] = {
        flatMap(list)(a ⇒ if (f(a)) List(a) else Nil)
    }

    /** ex3.22 */
    def addSamePosition(l1: List[Int], l2: List[Int]): List[Int] = {
        (l1, l2) match {
            case (Cons(h1, t1), Cons(h2, t2)) ⇒
                Cons(h1 + h2, addSamePosition(t1, t2))
            case _ ⇒ Nil
        }
    }

    /** ex3.23 */
    def zipWith[A, B, C](l1: List[A], l2: List[B])(f: (A, B) ⇒ C): List[C] = {
        (l1, l2) match {
            case (Cons(h1, t1), Cons(h2, t2)) ⇒
                Cons(f(h1, h2), zipWith(t1, t2)(f))
            case _ ⇒ Nil
        }
    }

    /** ex3.24 */
    @annotation.tailrec
    def hasSubsequence[A](list: List[A], sub: List[A]): Boolean = {
        @annotation.tailrec
        def check(l1: List[A], l2: List[A]): Boolean = (l1, l2) match {
            case (Cons(h1, t1), Cons(h2, t2)) if h1 == h2 ⇒ check(t1, t2)
            case (_, Nil) ⇒ true
            case _ ⇒ false
        }
        list match {
            case Cons(head, tail) ⇒
                if (check(tail, sub)) true
                else hasSubsequence(tail, sub)
            case Nil ⇒ false
        }
    }

    // then comes testing procedures

    def testTail() = {
        println("Testing List.tail")
        val l1 = List(1, 2, 3, 4)
        val l2 = List(1)
        val l3 = Nil
        for (l ← Seq(l1, l2, l3))
            println(s"tail of $l is: ${tail(l)}")
        println("")
    }

    def testSetHead() = {
        println("Testing List.setHead")
        val l1 = List(1, 2, 3, 4)
        val l2 = List(1)
        val l3 = Nil
        for (l ← Seq(l1, l2, l3))
            println(s"set head of $l to 100 is: ${setHead(l, 100)}")
        println("")
    }

    def testDrop() = {
        println("Testing List.drop")
        val l = List(1, 2, 3, 4)
        for (n ← 0 to 5)
            println(s"drop $n from $l yield: ${(drop(l, n))}")
        println("")
    }

    def testDropWhile() = {
        println("Testing List.dropWhile")
        val l = List(1, 2, 3, 4)
        val pred = (e: Int) ⇒ (e < 3)
        println(s"dropping the list while elem < 3: ${dropWhile(l, pred)}\n")
    }

    def testInit() = {
        println("Testing List.Init")
        val l1 = List(1, 2, 3, 4)
        val l2 = List(1)
        val l3 = Nil
        for (l ← Seq(l1, l2, l3))
            println(s"init of $l is: ${init(l)}")
        println("")
    }

    def testLength() = {
        println("Testing List.Length")
        val l1 = List(1.5, 2.5, 3.5, 4.5)
        val l2 = List("1")
        val l3 = Nil
        for (l ← Seq(l1, l2, l3))
            println(s"length of $l is: ${length(l)}")
        println("")
    }

    def testFoldLeft() = {
        println("Testing List.foldLeft")
        val l = List(1.5, 2.5, 3.5, 4.5)
        println(s"sum of $l: ${sum(l)}")
        println(s"product of $l: ${product(l)}")
        println(s"length of $l: ${length2(l)}")
        println("")
    }

    def testReverse() = {
        println("Testing List.reverse")
        val l1 = List(1.5, 2.5, 3.5, 4.5)
        val l2 = List("1")
        val l3 = Nil
        for (l ← Seq(l1, l2, l3))
            println(s"reverse of $l is: ${reverse(l)}")
        println("")
    }

    def testAppend() = {
        println("Testing List.Append")
        val l1 = List(1, 2, 3, 4)
        val l2 = List(1)
        val l3 = Nil
        val ap = List(123, 456)
        for (l ← Seq(l1, l2, l3))
            println(s"append List(123, 456) to $l yield: ${append(l, ap)}")
        println("")
    }

    def testFold2() = {
        println("Testing List.foldxxxx2")
        val l1 = List(1, 2, 3, 4)
        val l2 = List(1)
        val l3: List[Int] = Nil
        for (l ← Seq(l1, l2, l3)) {
            println(s"$l foldLeft: ${foldLeft(l, 1)(_ - _)}")
            println(s"$l foldRight: ${foldRight(l, 1)(_ - _)}")
        }
        println("")
    }

    def testConcat() = {
        println("Testing List.concat")
        val l1 = List(1, 2, 3, 4)
        val l2 = List(1)
        val l3: List[Int] = Nil
        val l4 = List(5, 6, 7, 8)
        val ll = List(l1, l2, l3, l4)
        println("concat of")
        for (l ← Seq(l1, l2, l3, l4))
            println(l)
        println(s"is ${concat(ll)}\n")
    }

    def testIncrement() = {
        println("Testing List.increment")
        val l = List(1, 2, 3, 4)
        println(s"increment $l by 1 is: ${increment(l)}\n")
    }

    def testDouble2String() = {
        println("Test List.double2String")
        val l = List(1.5, 2.5, 3.5, 4.5)
        println(s"$l to string list is: ${double2String(l)}\n")
    }

    def testMap() = {
        println("Testing List.map")
        val l = List(1, 2, 3, 4)
        println(s"2 times elem in $l and map to string: ${map(l)(i ⇒ (i * 2).toString)}\n")
    }

    def testFilter() = {
        println("Testing List.filter")
        val l = List(1, 2, 3, 4)
        println(s"filtering out even number in $l yields: ${filter(l)(_ % 2 == 1)}\n")
    }

    def testFlatMap() = {
        println("Testing List.flatMap")
        val l = List(1, 2, 3, 4)
        println(s"duplicating $l with flatMap yields: ${flatMap(l)(a ⇒ List(a, a))}\n")
    }

    def testFilter2() = {
        println("Testing List.filter2")
        val l = List(1, 2, 3, 4)
        println(s"filtering out even number in $l yields: ${filter2(l)(_ % 2 == 1)}\n")
    }

    def testAddSamePosition() = {
        println("Testing List.addSamePosition")
        val l1 = List(1, 2, 3, 4)
        val l2 = List(5, 6, 7, 8, 9)
        println(s"add $l1 and $l2 yields: ${addSamePosition(l1, l2)}")
        println(s"add $l2 and $l1 yields: ${addSamePosition(l2, l1)}\n")
    }

    def testZipWith() = {
        println("Testing List.zipWith")
        val l1 = List(1, 2, 3, 4)
        val l2 = List(1.5, 2.5, 3.5, 4.5, 5.5)
        println(s"zipping $l1 and $l2 as string yields: ${zipWith(l1, l2)((a, b) ⇒ (a.toString + b.toString))}")
    }

    def testHasSubsequence() = {
        println("Testing List.hasSubsequence")
        val list = List(1, 2, 3, 4, 5)
        val l1 = Nil
        val l2 = List(1, 2)
        val l3 = List(1, 2, 3, 4, 5, 6)
        val l4 = List(2, 3, 4)
        val l5 = List(4)
        println(s"searching subsequences in $list")
        for (l ← Seq(l1, l2, l3, l4, l5))
            println(s"$l ? ${hasSubsequence(list, l)}")
        println("")
    }

    def main(argv: Array[String]) = {
        testTail()
        testSetHead()
        testDrop()
        testDropWhile()
        testInit()
        testLength()
        testFoldLeft()
        testReverse()
        testAppend()
        testFold2()
        testConcat()
        testIncrement()
        testDouble2String()
        testMap()
        testFilter()
        testFlatMap()
        testFilter2()
        testAddSamePosition()
        testZipWith()
        testHasSubsequence()
    }
}
