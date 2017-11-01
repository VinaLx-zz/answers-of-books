object Compose {
    def compose[A, B, C](f: A ⇒ B, g: B ⇒ C): A ⇒ C = {
        a ⇒ g(f(a))
    }

    def main(argv: Array[String]) = {
        val f = (a: Int) ⇒ a + 2.5
        val g = (b: Double) ⇒ b / 2
        val h = compose(f, g)
        println(h(5))
    }
}