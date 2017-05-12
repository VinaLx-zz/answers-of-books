package stream_processing

sealed trait Process[I, O] {
    import Process._

    def apply(s: Stream[I]): Stream[O] = this match {
        case Halt() ⇒ Stream()
        case Await(recv) ⇒ s match {
            case head #:: tail ⇒ recv(Some(head))(tail)
            case other ⇒ recv(None)(other)
        }
        case Emit(o, tail) ⇒ o #:: tail(s)
    }

    def repeat: Process[I, O] = {
        def go(p: Process[I, O]): Process[I, O] = p match {
            case Halt() ⇒ go(this)
            case Await(recv) ⇒ Await {
                case None ⇒ recv(None)
                case i ⇒ go(recv(i))
            }
            case Emit(o, tail) ⇒ Emit(o, go(tail))
        }
        go(this)
    }

    def map[O2](f: O ⇒ O2): Process[I, O2] = this |> Process.lift(f)

    def ++(p: ⇒ Process[I, O]): Process[I, O] = this match {
        case Halt() ⇒ p
        case Emit(o, tail) ⇒ Emit(o, tail ++ p)
        case Await(recv) ⇒ Await(recv andThen (_ ++ p))
    }

    def flatMap[O2](f: O ⇒ Process[I, O2]): Process[I, O2] = this match {
        case Halt() ⇒ Halt()
        case Emit(o, tail) ⇒ f(o) ++ tail.flatMap(f)
        case Await(recv) ⇒ Await(recv andThen (_ flatMap f))
    }

    /** ex15.5 */
    def |>[O2](p2: Process[O, O2]): Process[I, O2] = (this, p2) match {
        case (_, Halt()) ⇒ Halt()
        case (any, Emit(o2, tail2)) ⇒ Emit(o2, any |> tail2)
        case (Halt(), Await(recv)) ⇒ Halt() |> recv(None)
        case (Emit(o, tail), Await(recv2)) ⇒ tail |> recv2(Some(o))
        case (Await(recv), await2) ⇒ Await {
            any ⇒ recv(any) |> await2
        }
    }

    /** ex15.6 */
    def zipWithIndex: Process[I, (O, Int)] = {
        this |> loop[Int, O, (O, Int)](0)((o, idx) ⇒ ((o, idx), idx + 1))
    }

    /** ex15.7 */
    def feed[I, O](p: Process[I, O])(i: Option[I]): Process[I, O] = p match {
        case Halt() ⇒ Halt()
        case Emit(o, tail) ⇒ Emit(o, feed(tail)(i))
        case Await(recv) ⇒ recv(i)
    }
    def zip[O2](p2: Process[I, O2]): Process[I, (O, O2)] = (this, p2) match {
        case (Halt(), _) | (_, Halt()) ⇒ Halt()
        case (Await(recv), any) ⇒ Await(some ⇒ recv(some) zip feed(any)(some))
        case (any, Await(recv)) ⇒ Await(some ⇒ feed(any)(some) zip recv(some))
        case (Emit(o1, tail1), Emit(o2, tail2)) ⇒
            Emit((o1, o2), tail1 zip tail2)
    }
}

case class Emit[I, O](
    head: O, tail: Process[I, O] = Halt[I, O]()) extends Process[I, O]
case class Await[I, O](recv: Option[I] ⇒ Process[I, O]) extends Process[I, O]
case class Halt[I, O]() extends Process[I, O]

import monad._

object Process {
    def liftOne[I, O](f: I ⇒ O): Process[I, O] = {
        Await {
            case Some(i) ⇒ Emit(f(i), Halt())
            case None ⇒ Halt()
        }
    }

    def lift[I, O](f: I ⇒ O): Process[I, O] = liftOne(f).repeat

    def filter[I](p: I ⇒ Boolean): Process[I, I] = {
        Await[I, I] {
            case Some(i) if p(i) ⇒ Emit[I, I](i)
            case _ ⇒ Halt[I, I]()
        }.repeat
    }

    def emit[I, O](head: O,
        tail: Process[I, O] = Halt[I, O]()): Process[I, O] = {
        Emit(head, tail)
    }

    def await[I, O](f: I ⇒ Process[I, O],
        fallback: Process[I, O] = Halt[I, O]()): Process[I, O] = {
        Await[I, O] {
            case Some(i) ⇒ f(i)
            case None ⇒ fallback
        }
    }

    def loop[S, I, O](z: S)(f: (I, S) ⇒ (O, S)): Process[I, O] = {
        await((i: I) ⇒ f(i, z) match {
            case (o, s2) ⇒ emit(o, loop(s2)(f))
        })
    }

    def monad[I] = new Monad[({ type X[Y] = Process[I, Y] })#X] {
        def unit[A](a: ⇒ A): Process[I, A] = Emit(a)
        def flatMap[O, O2](p: Process[I, O])(f: O ⇒ Process[I, O2]) = {
            p flatMap f
        }
    }

    /** ex15.1 */
    def take[I](n: Int): Process[I, I] = {
        if (n <= 0) Halt()
        else Await {
            case None ⇒ Halt()
            case Some(i) ⇒ Emit(i, take(n - 1))
        }
    }
    def drop[I](n: Int): Process[I, I] = {
        Await[I, I] {
            case None ⇒ Halt()
            case _ if n > 0 ⇒ drop[I](n - 1)
            case Some(i) ⇒ Emit(i, drop[I](0))
        }
    }
    def takeWhile[I](f: I ⇒ Boolean): Process[I, I] = {
        Await[I, I] {
            case Some(i) if f(i) ⇒ Emit(i, takeWhile(f))
            case _ ⇒ Halt()
        }
    }
    def dropWhile[I](f: I ⇒ Boolean): Process[I, I] = {
        Await[I, I] {
            case None ⇒ Halt()
            case Some(i) if f(i) ⇒ dropWhile(f)
            case Some(i) ⇒ Emit(i, drop(0))
        }
    }

    /** ex15.2 */
    def count[I]: Process[I, Int] = {
        def countImpl(n: Int): Process[I, Int] = {
            Await[I, Int] {
                case None ⇒ Halt()
                case Some(_) ⇒ Emit(n, countImpl(n + 1))
            }
        }
        countImpl(0)
    }

    /** ex15.3 */
    def mean: Process[Double, Double] = {
        def meanImpl(m: Double, n: Int): Process[Double, Double] = {
            Await[Double, Double] {
                case None ⇒ Halt()
                case Some(d) ⇒
                    val nn = n + 1
                    val nm = (m * n + d) / nn
                    Emit(nm, meanImpl(nm, nn))
            }
        }
        Await[Double, Double] {
            case None ⇒ Halt()
            case Some(d) ⇒ Emit(d, meanImpl(d, 1))
        }
    }

    /** ex15.4 Requirement: use `loop` */
    def sum: Process[Double, Double] = {
        loop[Double, Double, Double](0)((i, s) ⇒ (i + s, i + s))
    }
    def count2[I]: Process[I, Int] = {
        loop[Int, I, Int](0)((_, s) ⇒ (s + 1, s + 1))
    }

    /** ex15.7 Requirement: user zip */
    def mean2: Process[Double, Double] = {
        (sum zip count2) map { case (s, c) ⇒ s / c }
    }

    /** 15.8 */
    // not accumulated, halting
    def exists[I](f: I ⇒ Boolean): Process[I, Boolean] = {
        Await {
            case None ⇒ Emit(false)
            case Some(i) if f(i) ⇒ Emit(true)
            case otherwise ⇒ exists(f)
        }
    }
    // accumulated, halting
    def exists2[I](f: I ⇒ Boolean): Process[I, Boolean] = {
        Await {
            case None ⇒ Halt()
            case Some(i) if f(i) ⇒ Emit(true)
            case otherwise ⇒ Emit(false, exists2(f))
        }
    }
    // accumulated, not halting
    def exists3[I](f: I ⇒ Boolean): Process[I, Boolean] = {
        Await {
            case None ⇒ Halt()
            case Some(i) ⇒ Emit(f(i), exists3(f))
        }
    }
}