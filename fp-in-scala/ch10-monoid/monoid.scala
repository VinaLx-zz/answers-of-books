package monoid

/** ex10.1 */
object IntAddition extends Monoid[Int] {
    def op(lhs: Int, rhs: Int): Int = lhs + rhs
    def zero = 0
}

object IntMultiplication extends Monoid[Int] {
    def op(lhs: Int, rhs: Int): Int = lhs * rhs
    def zero = 1
}

object BooleanOr extends Monoid[Boolean] {
    def op(lhs: Boolean, rhs: Boolean): Boolean = lhs || rhs
    def zero = false
}

object BooleanAnd extends Monoid[Boolean] {
    def op(lhs: Boolean, rhs: Boolean): Boolean = lhs && rhs
    def zero = true
}

/** ex10.2 */
trait OptionMonoid[A] extends Monoid[Option[A]] {
    def op(lhs: Option[A], rhs: Option[A]): Option[A] = lhs orElse rhs
    def zero = None
}

/** ex10.3 */
trait EndoMonoid[A] extends Monoid[A ⇒ A] {
    def op(lhs: A ⇒ A, rhs: A ⇒ A): A ⇒ A = lhs andThen rhs
    def zero = x ⇒ x
}

trait Monoid[A] {
    def op(lhs: A, rhs: A): A
    def zero: A
}

object Monoid {
    def mapMergeMonoid[K, V](mv: Monoid[V]): Monoid[Map[K, V]] = {
        new Monoid[Map[K, V]] {
            def zero = Map[K, V]()
            def op(lhs: Map[K, V], rhs: Map[K, V]) = {
                (lhs.keySet ++ rhs.keySet).foldLeft(zero) { (map, k) ⇒
                    map.updated(k, mv.op(
                        lhs.getOrElse(k, mv.zero),
                        rhs.getOrElse(k, mv.zero)))
                }
            }
        }
    }

    import testing.Gen
    import testing.prop2._
    /** ex10.4 */
    def monoidLaws[A](m: Monoid[A], gen: Gen[A]): Prop = {
        Prop.forAll {
            for (a1 ← gen; a2 ← gen; a3 ← gen) yield (a1, a2, a3)
        } {
            case (a1, a2, a3) ⇒
                m.op(a1, m.op(a2, a3)) == m.op(m.op(a1, a2), a3)
        } && Prop.forAll(gen) {
            a ⇒ m.op(a, m.zero) == a && m.op(m.zero, a) == a
        }
    }

    /** ex10.5 */
    def foldMap[A, B](as: List[A], m: Monoid[B])(f: A ⇒ B): B = {
        (m.zero /: as)((b, a) ⇒ m.op(b, f(a)))
    }

    /** ex10.6 Requirement: use foldMap*/
    def foldLeft[A, B](as: List[A])(z: B)(f: (B, A) ⇒ B): B = {
        foldMap(as, new EndoMonoid[B] {})(a ⇒ b ⇒ f(b, a))(z)
    }
    def foldRight[A, B](as: List[A])(z: B)(f: (A, B) ⇒ B): B = {
        foldMap(as, new Monoid[B ⇒ B] {
            def op(lhs: B ⇒ B, rhs: B ⇒ B) = lhs compose rhs
            def zero = x ⇒ x
        })(a ⇒ b ⇒ f(a, b))(z)
    }

    /** ex10.7 */
    def foldMapV[A, B](v: IndexedSeq[A], m: Monoid[B])(f: A ⇒ B): B = {
        if (v.isEmpty) m.zero
        else if (v.size == 1) f(v.head)
        else {
            val (left, right) = v.splitAt(v.size / 2)
            m.op(foldMapV(left, m)(f), foldMapV(right, m)(f))
        }
    }

    /** ex10.8 */
    import parallelism.part2.Par
    import Par.Par
    def par[A](m: Monoid[A]): Monoid[Par[A]] = {
        new Monoid[Par[A]] {
            def zero = Par.unit(m.zero)
            def op(lhs: Par[A], rhs: Par[A]) = Par.map2(lhs, rhs)(m.op)
        }
    }

    def parFoldMap[A, B](v: IndexedSeq[A], m: Monoid[B])(f: A ⇒ B): Par[B] = {
        if (v.isEmpty) par(m).zero
        if (v.size == 1) Par.map(Par.unit(v.head))(f)
        val (left, right) = v.splitAt(v.size / 2)
        par(m).op(parFoldMap(left, m)(f), parFoldMap(right, m)(f))
    }

    /** ex10.9 */
    def isOrdered(v: IndexedSeq[Int]): Boolean = {
        val range_monoid = new Monoid[Option[(Int, Int, Boolean)]] {
            def zero = None
            def op(
                lhs: Option[(Int, Int, Boolean)],
                rhs: Option[(Int, Int, Boolean)]) = {
                (lhs, rhs) match {
                    case (Some((l1, r1, o1)), Some((l2, r2, o2))) ⇒
                        Some((l1 min l2, r1 max r2, o1 && o2 && r1 <= l2))
                    case (l, None) ⇒ l
                    case (None, r) ⇒ r
                }
            }
        }
        foldMapV(v, range_monoid)(
            a ⇒ Some((a, a, true))).map(_._3).getOrElse(true)
    }

    /** ex10.16 */
    def productMonoid[A, B](ma: Monoid[A], mb: Monoid[B]): Monoid[(A, B)] = {
        new Monoid[(A, B)] {
            def zero = (ma.zero, mb.zero)
            def op(lhs: (A, B), rhs: (A, B)): (A, B) = (lhs, rhs) match {
                case ((a1, b1), (a2, b2)) ⇒ (ma.op(a1, a2), mb.op(b1, b2))
            }
        }
    }

    /** ex10.17 */
    def functionMonoid[A, B](mb: Monoid[B])(f: A ⇒ B): Monoid[A ⇒ B] = {
        new Monoid[A ⇒ B] {
            def zero = f
            def op(lhs: A ⇒ B, rhs: A ⇒ B): A ⇒ B = {
                a ⇒ mb.op(lhs(a), rhs(a))
            }
        }
    }

    /** ex10.18 */
    def bag[A](as: IndexedSeq[A]): Map[A, Int] = {
        foldMapV(as, mapMergeMonoid[A, Int](IntAddition))(a ⇒ Map(a -> 1))
    }
}
