package strictness_laziness

object From {
    /** ex5.9 */
    def from(i: Int): Stream[Int] = Stream.cons(i, from(i + 1))

    /** ex5.12 Requirement: use unfold */
    def from2(i: Int): Stream[Int] = {
        Stream.unfold(i)(s ⇒ Some((s, s + 1)))
    }

    def main(args: Array[String]): Unit = {
        println("Testing from")
        val s = from(0)
        val s2 = from(5)
        println(s.take(10).toList)
        println(s.take(15).toList)
        println(s2.take(2).toList)

        println("Testing from2")
        val s3 = from(1)
        val s4 = from(10)
        println(s3.take(10).toList)
        println(s4.take(5).toList)
        println(s4.take(0).toList)
    }
}