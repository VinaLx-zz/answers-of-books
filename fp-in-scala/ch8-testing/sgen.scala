package testing

case class SGen[+A](forSize: Int ⇒ Gen[A]) {
    def apply(n: Int): Gen[A] = forSize(n)

    /** ex8.11 */
    def flatMap[B](f: A ⇒ SGen[B]) = SGen { i ⇒
        forSize(i) flatMap (a ⇒ f(a).forSize(i))
    }
}