package applicative

trait Traverse[F[_]] {
    def traverse[G[_]: Applicative, A, B](
        fa: F[A])(f: A ⇒ G[B])(ag: Applicative[G]): G[F[B]]

    def sequence[G[_]: Applicative, A](
        fga: F[G[A]])(ag: Applicative[G]): G[F[A]] = {
        traverse(fga)(ga ⇒ ga)(ag)
    }
}

object Traverse {
    /** ex12.13 */
    object ListTraverse extends Traverse[List] {
        def traverse[G[_]: Applicative, A, B](
            as: List[A])(f: A ⇒ G[B])(ag: Applicative[G]): G[List[B]] = {
            as.foldRight[G[List[B]]](ag.unit(Nil)) {
                (a, glb) ⇒ ag.map2(f(a), glb)(_ :: _)
            }
        }
    }

    object OpitonTraverse extends Traverse[Option] {
        def traverse[G[_]: Applicative, A, B](
            oa: Option[A])(f: A ⇒ G[B])(ag: Applicative[G]): G[Option[B]] = {
            oa.foldRight[G[Option[B]]](ag.unit(None)) {
                (a, gob) ⇒ ag.map2(f(a), gob)((b, _) ⇒ Some(b))
            }
        }
    }
}