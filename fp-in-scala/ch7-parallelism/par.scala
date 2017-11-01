/**
 * this file contains Par and related problems
 */

package parallelism.part1

import java.util.concurrent._

object Par {
    type Par[A] = ExecutorService ⇒ Future[A]

    def run[A](s: ExecutorService)(a: Par[A]): Future[A] = a(s)

    def unit[A](a: A): Par[A] = (es: ExecutorService) ⇒ UnitFuture(a)

    private case class UnitFuture[A](get: A) extends Future[A] {
        def isDone = true
        def get(timeout: Long, units: TimeUnit) = get
        def isCancelled = false
        def cancel(evenIfRunning: Boolean) = false
    }

    def map2[A, B, C](a: Par[A], b: Par[B])(f: (A, B) ⇒ C): Par[C] = {
        es ⇒
            val (af, bf) = (a(es), b(es))
            UnitFuture(f(af.get, bf.get))
    }

    def map[A, B](a: Par[A])(f: A ⇒ B): Par[B] = {
        map2(a, unit(()))((a, _) ⇒ f(a))
    }

    def fork[A](a: ⇒ Par[A]): Par[A] = { es ⇒
        es.submit(new Callable[A] {
            def call = a(es).get
        })
    }

    def lazyUnit[A](a: ⇒ A): Par[A] = fork(unit(a))

    def parMap[A, B](l: List[A])(f: A ⇒ B): Par[List[B]] = {
        val lp = l.map(asyncF(f))
        sequence(lp)
    }

    def equal[A](lhs: Par[A], rhs: Par[A]): Par[Boolean] = {
        map2(lhs, rhs)(_ == _)
    }

    /** ex7.3 */
    private case class MapFuture[A, B, C](
        af: Future[A], bf: Future[B], f: (A, B) ⇒ C) extends Future[C] {

        def isDone = af.isDone && bf.isDone

        def isCancelled = af.isCancelled || bf.isCancelled

        def cancel(evenIfRunning: Boolean) =
            af.cancel(evenIfRunning) || bf.cancel(evenIfRunning)

        def get = f(af.get, bf.get)

        def get(timeout: Long, units: TimeUnit) = {
            val nano_timeout = units.toNanos(timeout)
            val start = System.nanoTime
            val a = af.get(nano_timeout, TimeUnit.NANOSECONDS)
            val past = System.nanoTime - start
            val b = bf.get(nano_timeout - past, TimeUnit.NANOSECONDS)
            f(a, b)
        }
    }

    def map2WithTimeout[A, B, C](
        a: Par[A], b: Par[B])(f: (A, B) ⇒ C): Par[C] = { es ⇒
        val (af, bf) = (a(es), b(es))
        MapFuture(af, bf, f)
    }

    /** ex7.4 */
    def asyncF[A, B](f: A ⇒ B): A ⇒ Par[B] = a ⇒ lazyUnit(f(a))

    /** ex7.5 */
    def sequence[A](ps: List[Par[A]]): Par[List[A]] = {
        ps.foldRight[Par[List[A]]](unit(Nil))((p, pl) ⇒ map2(p, pl)(_ :: _))
    }

    // implementation from answer reference
    def sequence2[A](ps: List[Par[A]]): Par[List[A]] = {
        def sequenceImpl(vs: IndexedSeq[Par[A]]): Par[IndexedSeq[A]] = {
            if (vs.isEmpty) unit(IndexedSeq())
            else if (vs.size == 1) map(vs.head)(e ⇒ IndexedSeq(e))
            else {
                val (left, right) = vs.splitAt(vs.size / 2)
                map2(sequenceImpl(left), sequenceImpl(right))(_ ++ _)
            }
        }
        map(sequenceImpl(ps.toIndexedSeq))(_ toList)
    }

    /** ex7.6 */
    def parFilter[A](as: List[A])(f: A ⇒ Boolean): Par[List[A]] = {
        val lpl = as map (asyncF[A, List[A]](a ⇒ if (f(a)) List(a) else Nil))
        map(sequence(lpl))(_ flatten)
    }

    /** ex7.11 */
    def choiceN[A](n: Par[Int])(choices: List[Par[A]]): Par[A] = { es ⇒
        val i = run(es)(n).get
        run(es)(choices(i))
    }

    def choice[A](cond: Par[Boolean])(t: Par[A], f: Par[A]): Par[A] = {
        choiceN(map(cond)(i ⇒ if (i) 1 else 0))(List(f, t))
    }

    /** ex7.12 */
    def choiceMap[K, V](key: Par[K])(choices: Map[K, Par[V]]): Par[V] = { es ⇒
        val k = run(es)(key).get
        run(es)(choices(k))
    }

    /** ex7.13 */
    def chooser[A, B](pa: Par[A])(choices: A ⇒ Par[B]): Par[B] = { es ⇒
        val a = run(es)(pa).get
        run(es)(choices(a))
    }

    def choice2[A](cond: Par[Boolean])(t: Par[A], f: Par[A]): Par[A] = {
        chooser(cond)(b ⇒ if (b) t else f)
    }

    def choiceN2[A](n: Par[Int])(choices: List[Par[A]]): Par[A] = {
        chooser(n)(n ⇒ choices(n))
    }

    /** ex7.14 Requirement: join use chooser, flatMap(chooser) use join*/
    def join[A](a: Par[Par[A]]): Par[A] = {
        chooser(a)(a ⇒ a)
    }

    def flatMap[A, B](pa: Par[A])(f: A ⇒ Par[B]): Par[B] = {
        join(map(pa)(f))
    }
}