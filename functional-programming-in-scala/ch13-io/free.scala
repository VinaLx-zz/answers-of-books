package iomonad

sealed trait Free[F[_], A] {
    def map[B](f: A ⇒ B): Free[F, B] = flatMap(f andThen (Return(_)))
    def flatMap[B](f: A ⇒ Free[F, B]): Free[F, B] = FlatMap(this, f)
}
case class Return[F[_], A](a: A) extends Free[F, A]
case class Suspend[F[_], A](s: F[A]) extends Free[F, A]
case class FlatMap[F[_], A, B](
    s: Free[F, A], f: A ⇒ Free[F, B]) extends Free[F, B]

import monad._

object Free {

    type ~>[F[_], G[_]] = Translate[F, G]

    def runFree[F[_], G[_]: Monad, A](
        free: Free[F, A])(t: F ~> G): G[A] = free match {
        case Return(a) ⇒ implicitly[Monad[G]].unit(a)
        case Suspend(f) ⇒ t(f)
        case FlatMap(sub, f) ⇒ sub match {
            case Return(a) ⇒ runFree(f(a))(t)
            case Suspend(fa) ⇒
                implicitly[Monad[G]].flatMap(t(fa))(a ⇒ runFree(f(a))(t))
            case FlatMap(sub2, f2) ⇒
                runFree(sub2 flatMap (a ⇒ f2(a) flatMap f))(t)
        }
    }

    /** ex13.1 */
    def freeMonad[F[_]] = new Monad[({ type X[Y] = Free[F, Y] })#X] {
        def unit[A](a: ⇒ A): Free[F, A] = Return[F, A](a)
        def flatMap[A, B](fa: Free[F, A])(f: A ⇒ Free[F, B]) = {
            FlatMap(fa, f)
        }
    }

    /** ex13.2 */
    @annotation.tailrec
    def runTrampoline[A](ffa: Free[Function0, A]): A = ffa match {
        case Return(a) ⇒ a
        case Suspend(f) ⇒ f()
        case FlatMap(sub, f) ⇒ sub match {
            case Return(a) ⇒ runTrampoline(f(a))
            case Suspend(sf) ⇒ runTrampoline(f(sf()))
            case FlatMap(sub2, f2) ⇒
                runTrampoline(sub2 flatMap (a ⇒ f2(a) flatMap f))
        }
    }

    /** ex13.3 */
    def run[F[_]: Monad, A](ffa: Free[F, A]): F[A] = ffa match {
        case Return(a) ⇒ implicitly[Monad[F]].unit(a)
        case Suspend(f) ⇒ f
        case FlatMap(sub, f) ⇒ sub match {
            case Return(a) ⇒ run(f(a))
            case Suspend(fa) ⇒ implicitly[Monad[F]].flatMap(fa)(a ⇒ run(f(a)))
            case FlatMap(sub2, f2) ⇒
                run(sub2 flatMap (a ⇒ f2(a) flatMap f))
        }
    }

    /** ex13.4 */
    def translate[F[_], G[_], A](free: Free[F, A])(fg: F ~> G): Free[G, A] = {
        val fToFreeG = new Translate[F, ({ type X[Y] = Free[G, Y] })#X] {
            def apply[A](f: F[A]): Free[G, A] = Suspend(fg(f))
        }
        implicit val freeG = freeMonad[G]
        runFree[F, ({ type X[Y] = Free[G, Y] })#X, A](free)(fToFreeG)
    }
}