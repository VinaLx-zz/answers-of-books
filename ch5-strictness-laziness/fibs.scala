package strictness_laziness

object Fibs {
    /** ex5.10 */
    def fibs: Stream[Int] = {
        def fibsImpl(cur: Int, next: Int): Stream[Int] = {
            Stream.cons(cur, fibsImpl(next, cur + next))
        }
        fibsImpl(0, 1)
    }

    /** ex5.12 Requirement: use unfold*/
    def fibs2: Stream[Int] = {
        Stream.unfold((0, 1))(s ⇒ Some((s._1, (s._2, s._1 + s._2))))
    }

    def main(args: Array[String]): Unit = {
        println("Testing fibs")
        val s = fibs
        println(s.take(10).toList)

        println("Testing fibs2")
        val s2 = fibs2
        println(s.take(10).toList)
    }
}