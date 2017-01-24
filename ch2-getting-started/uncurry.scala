object Uncurry {
    def uncurry[A, B, C](f: A ⇒ B ⇒ C): (A, B) ⇒ C = {
        (a, b) ⇒ f(a)(b)
    }

    def main(argv: Array[String]) = {
        import Curry._
        val f = (a: Int, b: Double) ⇒ a + b
        val g = curry(f)
        val h = uncurry(g)
        println(h(1, 2.5))
    }
}
