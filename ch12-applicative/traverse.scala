package applicative

import monad._
import functional_state._

trait Traverse[F[_]] { self ⇒
    def traverse[G[_]: Applicative, A, B](fa: F[A])(f: A ⇒ G[B]): G[F[B]]

    def sequence[G[_]: Applicative, A](fga: F[G[A]]): G[F[A]] = {
        traverse(fga)(ga ⇒ ga)
    }

    def traverseS[S, A, B](fa: F[A])(f: A ⇒ State[S, B]): State[S, F[B]] = {
        implicit val sa = new Monad.StateMonad[S] {}
        traverse[({ type X[Y] = State[S, Y] })#X, A, B](fa)(f)
    }

    def zipWithIndex[A](as: F[A]): F[(A, Int)] = {
        traverseS(as)(a ⇒ (for {
            i ← State.get[Int]
            _ ← State.set(i + 1)
        } yield (a, i))).run(0)._1
    }

    def toList[A](as: F[A]): List[A] = {
        traverseS(as)(a ⇒ (for {
            prev ← State.get[List[A]]
            _ ← State.set(a :: prev)
        } yield ())).run(Nil)._2.reverse
    }

    def mapAccum[S, A, B](fa: F[A], s: S)(f: (A, S) ⇒ (B, S)): (F[B], S) = {
        traverseS(fa)(a ⇒ (for {
            s1 ← State.get[S]
            (b, s2) = f(a, s1)
            _ ← State.set(s2)
        } yield b)).run(s)
    }

    def toList2[A](as: F[A]): List[A] = {
        mapAccum(as, List[A]())((a, s) ⇒ ((), a :: s))._2.reverse
    }

    def zipWithIndex2[A](as: F[A]): F[(A, Int)] = {
        mapAccum(as, 0)((a, s) ⇒ ((a, s), s + 1))._1
    }

    /** ex12.14 */
    def map[A, B](fa: F[A])(f: A ⇒ B): F[B] = {
        // or simply type Id[A] = A
        case class Id[X](get: X)
        implicit val g = new Applicative[Id] {
            def unit[A](a: ⇒ A) = Id(a)
            def map2[A, B, C](a: Id[A], b: Id[B])(f: (A, B) ⇒ C): Id[C] = {
                Id(f(a.get, b.get))
            }
        }
        traverse(fa)(a ⇒ Id(f(a))).get
    }

    /** ex12.16 */
    def reverse[A](fa: F[A]): F[A] = {
        mapAccum(fa, toList(fa).reverse)((_, as) ⇒ (as.head, as.tail))._1
    }

    /** ex12.17 */
    def foldLeft[A, B](as: F[A])(z: B)(f: (B, A) ⇒ B): B = {
        mapAccum(as, z)((a, acc) ⇒ ((), f(acc, a)))._2
    }

    /** ex12.18 */
    def fuse[G[_], H[_], A, B](fa: F[A])(f: A ⇒ G[B], g: A ⇒ H[B])(
        G: Applicative[G], H: Applicative[H]): (G[F[B]], H[F[B]]) = {
        implicit val GH = G.product(H)
        traverse[({ type X[Y] = (G[Y], H[Y]) })#X, A, B](fa)(a ⇒ (f(a), g(a)))
    }

    /** ex12.19 */
    def compose[G[_]: Traverse] = new Traverse[({ type X[Y] = F[G[Y]] })#X] {
        def traverse[H[_]: Applicative, A, B](
            fga: F[G[A]])(f: A ⇒ H[B]): H[F[G[B]]] = {
            self.traverse(fga)(ga ⇒ implicitly[Traverse[G]].traverse(ga)(f))
        }
    }
}

object Traverse {
    /** ex12.13 */
    object ListTraverse extends Traverse[List] {
        def traverse[G[_]: Applicative, A, B](
            as: List[A])(f: A ⇒ G[B]): G[List[B]] = {
            val ag = implicitly[Applicative[G]]
            as.foldRight[G[List[B]]](ag.unit(Nil)) {
                (a, glb) ⇒ ag.map2(f(a), glb)(_ :: _)
            }
        }
    }

    object OpitonTraverse extends Traverse[Option] {
        def traverse[G[_]: Applicative, A, B](
            oa: Option[A])(f: A ⇒ G[B]): G[Option[B]] = {
            val ag = implicitly[Applicative[G]]
            oa.foldRight[G[Option[B]]](ag.unit(None)) {
                (a, gob) ⇒ ag.map2(f(a), gob)((b, _) ⇒ Some(b))
            }
        }
    }
}