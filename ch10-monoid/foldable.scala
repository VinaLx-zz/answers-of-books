package monoid

trait Foldable[F[_]] {
    def foldRight[A, B](as: F[A])(z: B)(f: (A, B) ⇒ B): B
    def foldLeft[A, B](as: F[A])(z: B)(f: (B, A) ⇒ B): B
    def foldMap[A, B](as: F[A])(f: A ⇒ B)(mb: Monoid[B]): B
    def concatenate[A](as: F[A])(m: Monoid[A]): A = {
        foldLeft(as)(m.zero)(m.op)
    }

    /** ex10.15 */
    def toList[A](fa: F[A]): List[A] = {
        foldRight(fa)(Nil: List[A])(_ :: _)
    }
}

/** ex10.12 */ // what's the point of this problem?
object ListFoldable extends Foldable[List] {
    def foldRight[A, B](as: List[A])(z: B)(f: (A, B) ⇒ B) = {
        as.foldRight(z)(f)
    }
    def foldLeft[A, B](as: List[A])(z: B)(f: (B, A) ⇒ B) = {
        as.foldLeft(z)(f)
    }
    def foldMap[A, B](as: List[A])(f: A ⇒ B)(mb: Monoid[B]): B = {
        foldLeft(as)(mb.zero)((b, a) ⇒ mb.op(b, f(a)))
    }
}

object IndexedSeqFoldable extends Foldable[IndexedSeq] {
    def foldRight[A, B](as: IndexedSeq[A])(z: B)(f: (A, B) ⇒ B) = {
        as.foldRight(z)(f)
    }
    def foldLeft[A, B](as: IndexedSeq[A])(z: B)(f: (B, A) ⇒ B) = {
        as.foldLeft(z)(f)
    }
    def foldMap[A, B](as: IndexedSeq[A])(f: A ⇒ B)(mb: Monoid[B]): B = {
        Monoid.foldMapV(as, mb)(f)
    }
}

object StreamFoldable extends Foldable[Stream] {
    def foldRight[A, B](as: Stream[A])(z: B)(f: (A, B) ⇒ B) = {
        as.foldRight(z)(f)
    }
    def foldLeft[A, B](as: Stream[A])(z: B)(f: (B, A) ⇒ B) = {
        as.foldLeft(z)(f)
    }
    def foldMap[A, B](as: Stream[A])(f: A ⇒ B)(mb: Monoid[B]): B = {
        as.foldLeft(mb.zero)((b, a) ⇒ mb.op(b, f(a)))
    }
}

/** ex10.13 */
sealed trait Tree[+A]
case class Leaf[A](value: A) extends Tree[A]
case class Branch[A](left: Tree[A], right: Tree[A]) extends Tree[A]

object TreeFoldable extends Foldable[Tree] {
    def foldRight[A, B](as: Tree[A])(z: B)(f: (A, B) ⇒ B): B = as match {
        case Branch(left, right) ⇒ foldRight(left)(foldRight(right)(z)(f))(f)
        case Leaf(value) ⇒ f(value, z)
    }
    def foldLeft[A, B](as: Tree[A])(z: B)(f: (B, A) ⇒ B): B = as match {
        case Branch(left, right) ⇒ foldLeft(right)(foldLeft(left)(z)(f))(f)
        case Leaf(value) ⇒ f(z, value)
    }
    def foldMap[A, B](as: Tree[A])(f: A ⇒ B)(mb: Monoid[B]): B = {
        foldLeft(as)(mb.zero)((b, a) ⇒ mb.op(b, f(a)))
    }
}

/** ex10.14 */
object OptionFoldable extends Foldable[Option] {
    def foldRight[A, B](oa: Option[A])(z: B)(f: (A, B) ⇒ B): B = {
        (for (a ← oa) yield f(a, z)) getOrElse z
    }
    def foldLeft[A, B](oa: Option[A])(z: B)(f: (B, A) ⇒ B): B = {
        foldRight(oa)(z)((a, b) ⇒ f(b, a))
    }
    def foldMap[A, B](oa: Option[A])(f: A ⇒ B)(mb: Monoid[B]): B = {
        (for (a ← oa) yield f(a)) getOrElse mb.zero
    }
}
