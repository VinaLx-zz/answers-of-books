package error_handling

/** ex4.6 */
sealed trait Either[+E, +A] {
    def map[B](f: A ⇒ B): Either[E, B] = this match {
        case Left(err) ⇒ Left(err)
        case Right(value) ⇒ Right(f(value))
    }

    def flatMap[B, EE >: E](f: A ⇒ Either[EE, B]): Either[EE, B] = this match {
        case Left(err) ⇒ Left(err)
        case Right(value) ⇒ f(value)
    }

    def orElse[EE >: E, B >: A](b: ⇒ Either[EE, B]): Either[EE, B] = this match {
        case Left(err) ⇒ b
        case Right(value) ⇒ Right(value)
    }

    def map2[EE >: E, B, C](b: Either[EE, B])(f: (A, B) ⇒ C): Either[EE, C] = {
        flatMap(aa ⇒ b map (bb ⇒ f(aa, bb)))
    }
}

case class Left[+E](value: E) extends Either[E, Nothing]
case class Right[+A](value: A) extends Either[Nothing, A]

/** ex4.7 */
object Either {
    def traverse[E, A, B](list: List[A])(f: A ⇒ Either[E, B]): Either[E, List[B]] = {
        list.foldRight[Either[E, List[B]]](Right(Nil))((e, el) ⇒ f(e).map2(el)(_ :: _))
    }

    def sequence[E, A](list: List[Either[E, A]]): Either[E, List[A]] = {
        traverse(list)(e ⇒ e)
    }
}