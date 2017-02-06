package monad

trait Functor[F[_]] {
    def map[A, B](fa: F[A])(f: A ⇒ B): F[B]
    def distribute[A, B](fab: F[(A, B)]): (F[A], F[B]) = {
        (map(fab)(_._1), map(fab)(_._2))
    }
    def codistribute[A, B](e: Either[F[A], F[B]]): F[Either[A, B]] =
        e match {
            case Left(fa) ⇒ map(fa)(Left(_))
            case Right(fb) ⇒ map(fb)(Right(_))
        }
}

import applicative._

trait Monad[F[_]] extends Applicative[F] {
    def flatMap[A, B](ma: F[A])(f: A ⇒ F[B]): F[B]
    override def map[A, B](ma: F[A])(f: A ⇒ B): F[B] = {
        flatMap(ma)(a ⇒ unit(f(a)))
    }
    override def map2[A, B, C](ma: F[A], mb: F[B])(f: (A, B) ⇒ C) = {
        flatMap(ma)(a ⇒ map(mb)(b ⇒ f(a, b)))
    }

    /** ex11.3 */
    override def sequence[A](mas: List[F[A]]): F[List[A]] = {
        // sugar for foldRight
        (mas :\ unit(Nil: List[A]))((ma, mla) ⇒ map2(ma, mla)(_ :: _))
    }
    override def traverse[A, B](as: List[A])(f: A ⇒ F[B]): F[List[B]] = {
        (as :\ unit(Nil: List[B]))((a, mlb) ⇒ map2(f(a), mlb)(_ :: _))
    }

    /** ex11.4 */
    override def replicateM[A](n: Int, ma: F[A]): F[List[A]] = {
        sequence(List.fill(n)(ma))
    }

    /** ex11.5 */
    def filterM[A](as: List[A])(f: A ⇒ F[Boolean]): F[List[A]] = as match {
        case Nil ⇒ unit(Nil)
        case head :: tail ⇒ flatMap(f(head)) { b ⇒
            if (b) map(filterM(tail)(f))(head :: _)
            else filterM(tail)(f)
        }
    }

    /** ex11.6 */
    def compose[A, B, C](f: A ⇒ F[B])(g: B ⇒ F[C]): A ⇒ F[C] = {
        a ⇒ flatMap(f(a))(g)
    }

    /** ex11.7 Requirment: use compose */
    def flatMap2[A, B](ma: F[A])(f: A ⇒ F[B]): F[B] = {
        compose((_: Unit) ⇒ ma)(f)(())
    }

    /** ex11.12 */
    def join[A](mma: F[F[A]]): F[A] = {
        flatMap(mma)(x ⇒ x)
    }

    /** ex11.13 */
    def flatMap3[A, B](ma: F[A])(f: A ⇒ F[B]): F[B] = {
        join(map(ma)(f))
    }
    def compose2[A, B, C](f: A ⇒ F[B])(g: B ⇒ F[C]): A ⇒ F[C] = {
        a ⇒ join(map(f(a))(g))
    }

}

case class Id[A](value: A)

import parallelism.part2._
import parsing.MyParser._

object Monad {

    /** ex11.1 typing exercise :) */
    object ParMonad extends Monad[Par.Par] {
        import Par.Par
        def unit[A](a: ⇒ A): Par[A] = Par.unit(a)
        def flatMap[A, B](pa: Par[A])(f: A ⇒ Par[B]): Par[B] = {
            Par.flatMap(pa)(f)
        }
    }

    object ParserMonad extends Monad[Parser] {
        def unit[A](a: ⇒ A): Parser[A] = MyParsers.succeed(a)
        def flatMap[A, B](pa: Parser[A])(f: A ⇒ Parser[B]): Parser[B] = {
            MyParsers.flatMap(pa)(f)
        }
    }

    object OptionMonad extends Monad[Option] {
        def unit[A](a: ⇒ A): Option[A] = Some(a)
        def flatMap[A, B](oa: Option[A])(f: A ⇒ Option[B]): Option[B] = {
            oa flatMap f
        }
    }

    object ListMonad extends Monad[List] {
        def unit[A](a: ⇒ A): List[A] = List(a)
        def flatMap[A, B](as: List[A])(f: A ⇒ List[B]): List[B] = {
            as flatMap f
        }
    }

    object StreamMonad extends Monad[Stream] {
        def unit[A](a: ⇒ A): Stream[A] = Stream(a)
        def flatMap[A, B](sa: Stream[A])(f: A ⇒ Stream[B]): Stream[B] = {
            sa flatMap f
        }
    }

    import functional_state._

    /** ex11.2 */
    trait StateMonad[S] extends Monad[({ type L[A] = State[S, A] })#L] {
        def unit[A](a: ⇒ A): State[S, A] = State(s ⇒ (a, s))
        def flatMap[A, B](sa: State[S, A])(f: A ⇒ State[S, B]): State[S, B] = {
            sa flatMap f
        }
    }

    /** ex11.17 */
    object IdMonad extends Monad[Id] {
        def unit[A](a: ⇒ A): Id[A] = Id(a)
        def flatMap[A, B](ida: Id[A])(f: A ⇒ Id[B]) = {
            f(ida.value)
        }
        override def map[A, B](ida: Id[A])(f: A ⇒ B) = {
            Id(f(ida.value))
        }
    }
}

