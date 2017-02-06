package applicative

import monad._
import monoid._

trait Applicative[F[_]] extends Functor[F] { self ⇒
    def map2[A, B, C](fa: F[A], fb: F[B])(f: (A, B) ⇒ C): F[C]
    def unit[A](a: ⇒ A): F[A]

    def map[A, B](fa: F[A])(f: A ⇒ B): F[B] = {
        map2(fa, unit(()))((a, _) ⇒ f(a))
    }
    def traverse[A, B](as: List[A])(f: A ⇒ F[B]): F[List[B]] = {
        as.foldRight[F[List[B]]](unit(Nil))((a, flb) ⇒ map2(f(a), flb)(_ :: _))
    }

    type Const[M, B] = M
    def monoidApplicative[M](m: Monoid[M]) = {
        new Applicative[({ type X[Y] = Const[M, Y] })#X] {
            def unit[A](a: ⇒ A): Const[M, A] = m.zero
            def map2[A, B, C](
                m1: Const[M, A], m2: Const[M, B])(
                    f: (A, B) ⇒ C): Const[M, C] = {
                m.op(m1, m2)
            }
        }
    }

    /** ex12.1 */
    def sequence[A](lfa: List[F[A]]): F[List[A]] = {
        traverse(lfa)(x ⇒ x)
    }
    def replicateM[A](n: Int, fa: F[A]): F[List[A]] = {
        map(fa)(a ⇒ List.fill(n)(a))
    }
    def product[A, B](fa: F[A], fb: F[B]): F[(A, B)] = {
        map2(fa, fb)((a, b) ⇒ (a, b))
    }

    /** ex12.2 */
    def apply[A, B](fab: F[A ⇒ B])(fa: F[A]): F[B] = {
        map2(fab, fa)((f, a) ⇒ f(a))
    }

    def mapByApply[A, B](fa: F[A])(f: A ⇒ B): F[B] = {
        apply(unit(f))(fa)
    }
    def map2ByApply[A, B, C](fa: F[A], fb: F[B])(f: (A, B) ⇒ C) = {
        apply(apply(unit(f.curried))(fa))(fb)
    }

    /** ex12.3 */
    def map3[A, B, C, D](
        fa: F[A], fb: F[B], fc: F[C])(f: (A, B, C) ⇒ D): F[D] = {
        apply(apply(apply(unit(f.curried))(fa))(fb))(fc)
    }
    def map4[A, B, C, D, E](
        fa: F[A], fb: F[B], fc: F[C], fd: F[D])(f: (A, B, C, D) ⇒ E): F[E] = {
        apply(apply(apply(apply(unit(f.curried))(fa))(fb))(fc))(fd)
    }

    /** ex12.8 */
    def product[G[_]](ag: Applicative[G]) = {
        new Applicative[({ type X[a] = (F[a], G[a]) })#X] {
            def unit[A](a: ⇒ A): (F[A], G[A]) = (self.unit(a), ag.unit(a))
            def map2[A, B, C](
                pa: (F[A], G[A]), pb: (F[B], G[B]))(
                    f: (A, B) ⇒ C): (F[C], G[C]) = {
                (self.map2(pa._1, pb._1)(f), ag.map2(pa._2, pb._2)(f))
            }
        }
    }

    /** ex12.9 */
    def compose[G[_]](ag: Monad[G]) = {
        new Applicative[({ type X[x] = F[G[x]] })#X] {
            def unit[A](a: ⇒ A): F[G[A]] = self.unit(ag.unit(a))
            def map2[A, B, C](
                ca: F[G[A]], cb: F[G[B]])(f: (A, B) ⇒ C): F[G[C]] = {
                self.map2(ca, cb)((ga, gb) ⇒ ag.map2(ga, gb)(f))
            }
        }
    }

    /** ex12.12 */
    def sequenceMap[K, V](ofa: Map[K, F[V]]): F[Map[K, V]] = {
        ofa.foldRight(unit(Map[K, V]())) {
            case ((k, fv), fm) ⇒
                map2(fv, fm)((v, m) ⇒ m.updated(k, v))
        }
    }
}

object Applicative {
    object StreamApplicative extends Applicative[Stream] {
        def unit[A](a: ⇒ A): Stream[A] = Stream.continually(a)
        def map2[A, B, C](
            as: Stream[A], bs: Stream[B])(f: (A, B) ⇒ C): Stream[C] = {
            as zip bs map f.tupled
        }
    }

    /** ex12.5 */
    trait EitherMonad[E] extends Monad[({ type F[x] = Either[E, x] })#F] {
        def unit[A](a: ⇒ A): Either[E, A] = Right(a)
        def flatMap[A, B](ea: Either[E, A])(f: A ⇒ Either[E, B]) = {
            ea.right flatMap f
        }
    }

    /** ex12.6 */
    trait ValidationApplicative[E]
        extends Applicative[({ type F[x] = Validation[E, x] })#F] {
        def unit[A](a: ⇒ A): Validation[E, A] = Success(a)
        def map2[A, B, C](va: Validation[E, A], vb: Validation[E, B])(
            f: (A, B) ⇒ C): Validation[E, C] = {
            (va, vb) match {
                case (Success(a), Success(b)) ⇒ Success(f(a, b))
                case (Failure(e, v), Success(_)) ⇒ Failure(e, v)
                case (Success(_), Failure(e, v)) ⇒ Failure(e, v)
                case (Failure(e1, v1), Failure(e2, v2)) ⇒
                    Failure(e1, v1 ++ (e2 +: v2))
            }
        }
    }
}