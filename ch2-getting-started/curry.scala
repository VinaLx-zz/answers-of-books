object Curry {
    def curry[A, B, C](f: (A, B) ⇒ C): A ⇒ B ⇒ C =
        a ⇒ b ⇒ f(a, b)

    def main(argv: Array[String]) = {
        def f(a: Int, b: Double): Double = a + b
        val g = curry(f)
        val h = g(1)
        println(h(2.5))
    }
}
