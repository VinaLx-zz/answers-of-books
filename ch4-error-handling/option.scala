package error_handling

/**
 * ex4.1
 * Requirement:
 * pattern matching can be only used to implement map and getOrElse
 */
sealed trait Option[+A] {
    def map[B](f: A ⇒ B): Option[B] = this match {
        case None ⇒ None
        case Some(value) ⇒ Some(f(value))
    }

    def flatMap[B](f: A ⇒ Option[B]): Option[B] = {
        map(f) getOrElse None
    }

    def getOrElse[B >: A](default: ⇒ B): B = this match {
        case None ⇒ default
        case Some(value) ⇒ value
    }

    def orElse[B >: A](ob: ⇒ Option[B]): Option[B] = {
        map(Some(_)) getOrElse ob
    }

    def filter(f: A ⇒ Boolean): Option[A] = {
        flatMap(a ⇒ if (f(a)) Some(a) else None)
    }
}

case class Some[+A](get: A) extends Option[A]
case object None extends Option[Nothing]

object Option {
    /** ex4.3 */
    def map2[A, B, C](a: Option[A], b: Option[B])(f: (A, B) ⇒ C): Option[C] = {
        (a, b) match {
            case (Some(va), Some(vb)) ⇒ Some(f(va, vb))
            case _ ⇒ None
        }
    }

    /** ex4.4 */
    def sequence[A](lo: List[Option[A]]): Option[List[A]] = {
        lo.foldRight[Option[List[A]]](Some(Nil))((o, ol) ⇒ map2(o, ol)(_ :: _))
    }

    /** ex4.5 */
    def traverse[A, B](list: List[A])(f: A ⇒ Option[B]): Option[List[B]] = {
        list.foldRight[Option[List[B]]](Some(Nil)) {
            (a, ol) ⇒ map2(f(a), ol)(_ :: _)
        }
    }

    def sequence2[A](lo: List[Option[A]]): Option[List[A]] = {
        traverse(lo)(_ orElse None)
    }

    def testSequence() = {
        println("Testing Option.sequence")
        val l1 = List(Some(1), Some(2), None, Some(3))
        val l2 = List(Some(1), Some(2), Some(3))
        val l3 = List[Option[Int]](None)
        for (l ← Seq(l1, l2, l3))
            println(s"$l => ${sequence(l)}")
        println("")
    }

    def testSequence2() = {
        println("Testing Option.sequence2")
        val l1 = List(Some(1), Some(2), None, Some(3))
        val l2 = List(Some(1), Some(2), Some(3))
        val l3 = List[Option[Int]](None)
        for (l ← Seq(l1, l2, l3))
            println(s"$l => ${sequence2(l)}")
        println("")
    }

    def main(argv: Array[String]) = {
        testSequence()
        testSequence2()
    }
}