package strictness_laziness

object Constant {
    /** ex5.8 */
    def constant[A](c: A): Stream[A] = Stream.cons(c, constant(c))

    /** ex5.12 Requirement: use unfold*/
    def constant2[A](c: A): Stream[A] = {
        Stream.unfold(c)(s ⇒ Some((s, s)))
    }

    def main(argv: Array[String]) = {
        println("Testing constant")
        val s = constant(1)
        println(s.take(5).toList)
        println(s.take(0).toList)

        println("Testing constant2")
        val s2 = constant2(1)
        println(s.take(10).toList)
        println(s.take(0).toList)
    }
}