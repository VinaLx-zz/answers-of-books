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
}