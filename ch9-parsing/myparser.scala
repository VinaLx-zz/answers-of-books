package parsing

import scala.util.matching._
import scala.language.implicitConversions

object MyParser {
    import Parsers._
    type Parser[+A] = Location ⇒ Result[A]

    trait Result[+A] {
        def mapError(f: ParseError ⇒ ParseError): Result[A] = this match {
            case Failure(e, c) ⇒ Failure(f(e), c)
            case _ ⇒ this
        }
        def uncommit: Result[A] = this match {
            case Failure(e, true) ⇒ Failure(e, false)
            case _ ⇒ this
        }
        def addCommit(isCommitted: Boolean): Result[A] = this match {
            case Failure(e, c) ⇒ Failure(e, c || isCommitted)
            case _ ⇒ this
        }
        def advanceSuccess(n: Int): Result[A] = this match {
            case Success(a, m) ⇒ Success(a, m + n)
            case _ ⇒ this
        }
    }
    case class Success[+A](get: A, charsConsumed: Int) extends Result[A]
    case class Failure(get: ParseError, isCommitted: Boolean) extends Result[Nothing]

    object MyParsers extends Parsers[Parser] {
        def scope[A](message: String)(p: Parser[A]): Parser[A] = { s ⇒
            p(s).mapError(_.push(s, message))
        }

        def label[A](message: String)(p: Parser[A]): Parser[A] = { s ⇒
            p(s).mapError(_.label(message))
        }

        def attempt[A](p: Parser[A]): Parser[A] = { s ⇒
            p(s).uncommit
        }

        def or[A](x: Parser[A], y: ⇒ Parser[A]): Parser[A] = { s ⇒
            x(s) match {
                case Failure(e, false) ⇒ y(s)
                case r ⇒ r
            }
        }

        def flatMap[A, B](f: Parser[A])(g: A ⇒ Parser[B]): Parser[B] =
            s ⇒ f(s) match {
                case Success(a, n) ⇒
                    g(a)(s.advanceBy(n)).addCommit(n != 0).advanceSuccess(n)
                case e @ Failure(_, _) ⇒ e
            }

        /** ex9.13 */
        def getInput(loc: Location) = loc.input.slice(loc.offset, loc.input.size)

        def string(s: String): Parser[String] = scope(s"Expect $s") { loc ⇒
            val input = getInput(loc)
            if (input.startsWith(s)) Success[String](s, s.size)
            else Failure(ParseError(List((loc, input))), true)
        }

        def regex(r: Regex): Parser[String] = { loc ⇒
            val input = getInput(loc)
            r.findPrefixOf(input) match {
                case Some(s) ⇒ Success(s, s.size)
                case None ⇒ Failure(ParseError(List((loc, input))), true)
            }
        }

        override def succeed[A](a: A): Parser[A] = _ ⇒ Success[A](a, 0)

        def slice[A](p: Parser[A]): Parser[String] = { loc ⇒
            p(loc) match {
                case Success(_, n) ⇒
                    Success(loc.input.slice(loc.offset, loc.offset + n), n)
                case Failure(err, c) ⇒ Failure(err, c)
            }
        }

        /** ex9.15 */
        def errorLocation(e: ParseError): Location = e.stack.head._1
        def errorMessage(e: ParseError): String = e.stack.head._2

        def run[A](p: Parser[A])(input: String): Either[ParseError, A] = p(Location(input, 0)) match {
            case Success(a, _) ⇒ Right(a)
            case Failure(e, isCommitted) ⇒ Left(e)
        }
    }
}