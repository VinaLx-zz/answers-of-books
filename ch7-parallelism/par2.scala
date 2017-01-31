/**
 * this file contains second implementation of Par
 */

package parallelism.part2

import java.util.concurrent._
import parallelism.Actor // borrowed

object Par {
    sealed trait Future[+A] {
        def apply(callback: A ⇒ Unit): Unit
    }
    type Par[+A] = ExecutorService ⇒ Future[A]

    def run[A](es: ExecutorService)(p: Par[A]): A = {
        val ref = new atomic.AtomicReference[A]
        val latch = new CountDownLatch(1)
        p(es) { a ⇒ ref.set(a); latch.countDown }
        latch.await
        ref.get
    }

    def unit[A](a: A): Par[A] = { es ⇒
        new Future[A] {
            def apply(callback: A ⇒ Unit): Unit =
                callback(a)
        }
    }

    def fork[A](a: ⇒ Par[A]): Par[A] = { es ⇒
        new Future[A] {
            def apply(callback: A ⇒ Unit): Unit =
                eval(es)(a(es)(callback))
        }
    }

    def eval(es: ExecutorService)(r: ⇒ Unit): Unit = {
        es.submit(new Callable[Unit] { def call = r })
    }

    def map2[A, B, C](pa: Par[A], pb: Par[B])(f: (A, B) ⇒ C): Par[C] = {
        es ⇒
            new Future[C] {
                def apply(callback: C ⇒ Unit): Unit = {
                    var ar: Option[A] = None
                    var br: Option[B] = None
                    val combiner = Actor[Either[A, B]](es) {
                        case Left(a) ⇒ br match {
                            case None ⇒ ar = Some(a)
                            case Some(b) ⇒ eval(es)(callback(f(a, b)))
                        }
                        case Right(b) ⇒ ar match {
                            case None ⇒ br = Some(b)
                            case Some(a) ⇒ eval(es)(callback(f(a, b)))
                        }
                    }
                    pa(es)(a ⇒ combiner ! Left(a))
                    pb(es)(b ⇒ combiner ! Right(b))
                }
            }
    }

    def map[A, B](pa: Par[A])(f: A ⇒ B): Par[B] = { es ⇒
        new Future[B] {
            def apply(callback: B ⇒ Unit) = {
                pa(es) { a ⇒ eval(es) { callback(f(a)) } }
            }
        }
    }

    /** ex7.11 */
    def choiceN[A](n: Par[Int])(choices: List[Par[A]]): Par[A] = { es ⇒
        new Future[A] {
            def apply(callback: A ⇒ Unit) {
                eval(es)(n(es) { i ⇒ choices(i)(es)(callback) })
            }
        }
    }

    def choice[A](cond: Par[Boolean])(t: Par[A], f: Par[A]): Par[A] = {
        choiceN(map(cond)(i ⇒ if (i) 1 else 0))(List(f, t))
    }

    /** ex7.12 */
    def choiceMap[K, V](key: Par[K])(choices: Map[K, Par[V]]): Par[V] = { es ⇒
        new Future[V] {
            def apply(callback: V ⇒ Unit) {
                eval(es)(key(es) { k ⇒ choices(k)(es)(callback) })
            }
        }
    }

    /** ex7.13 */
    def chooser[A, B](pa: Par[A])(choices: A ⇒ Par[B]): Par[B] = { es ⇒
        new Future[B] {
            def apply(callback: B ⇒ Unit) {
                eval(es)(pa(es) { a ⇒ choices(a)(es)(callback) })
            }
        }
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