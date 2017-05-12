package iomonad

import parallelism.part1.Par
import scala.io.StdIn

trait Translate[F[_], G[_]] { def apply[A](f: F[A]): G[A] }

sealed trait Console[A] {
    def toPar: Par.Par[A]
    def toThunk: () ⇒ A
}

case object ReadLine extends Console[Option[String]] {
    def toPar = Par.lazyUnit(run)
    def toThunk = () ⇒ run
    def run: Option[String] = {
        try Some(StdIn.readLine())
        catch { case e: Exception ⇒ None }
    }
}

case class PrintLine(line: String) extends Console[Unit] {
    def toPar = Par.lazyUnit(println(line))
    def toThunk = () ⇒ println(line)
}

object Console {
    import monad.Monad._
    import Free._

    type ConsoleIO[A] = Free[Console, A]
    def readLn: ConsoleIO[Option[String]] = Suspend(ReadLine)
    def printLn(line: String): ConsoleIO[Unit] = Suspend(PrintLine(line))

    object ConsoleToFunction0 extends Translate[Console, Function0] {
        def apply[A](a: Console[A]) = a.toThunk
    }
    object ConsoleToPar extends Translate[Console, Par.Par] {
        def apply[A](a: Console[A]) = a.toPar
    }
    def runConsoleFunction0[A](a: Free[Console, A]): () ⇒ A = {
        Free.runFree(a)(ConsoleToFunction0)
    }
    def runConsolePar[A](a: Free[Console, A]): Par.Par[A] = {
        Free.runFree(a)(ConsoleToPar)
    }

    /** ex13.4 */
    def runConsole[A](a: Free[Console, A]): A = {
        implicit val freeF0 = freeMonad[Function0]
        runTrampoline(translate(a)(ConsoleToFunction0))
    }
}

