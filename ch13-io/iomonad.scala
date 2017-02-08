package iomonad

sealed trait IO[A] {
    def run: A = IO.run(this)
    def map[B](f: A ⇒ B): IO[B] = {
        flatMap(f andThen (Return(_)))
    }
    def flatMap[B](f: A ⇒ IO[B]): IO[B] = {
        FlatMap(this, f)
    }
}

case class Return[A](a: A) extends IO[A]
case class Suspend[A](resume: () ⇒ A) extends IO[A]
case class FlatMap[A, B](sub: IO[A], f: A ⇒ IO[B]) extends IO[B]

import monad._

object IO extends Monad[IO] {
    import scala.io._
    def unit[A](a: ⇒ A): IO[A] = Suspend(() ⇒ a)
    def flatMap[A, B](fa: IO[A])(f: A ⇒ IO[B]) = fa flatMap f
    def apply[A](a: ⇒ A): IO[A] = unit(a)

    @annotation.tailrec
    def run[A](io: IO[A]): A = io match {
        case Return(a) ⇒ a
        case Suspend(f) ⇒ f()
        case FlatMap(sub, f) ⇒ sub match {
            case Return(a) ⇒ run(f(a))
            case Suspend(g) ⇒ run(f(g()))
            case FlatMap(sub2, g) ⇒ run(sub2 flatMap (a ⇒ g(a) flatMap f))
        }
    }

    def forever[A, B](a: IO[A]): IO[B] = {
        lazy val t: IO[B] = forever(a)
        a flatMap (_ ⇒ t)
    }

    def ReadLine: IO[String] = Suspend(() ⇒ StdIn.readLine())
    def PrintLine(message: String): IO[Unit] = {
        Suspend(() ⇒ println(message))
    }
}