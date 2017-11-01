package stream_processing

import iomonad._
import scala.io._
import java.io.{ PrintStream, File }

import Process._

object FileProcess {
    def processFile[A, B](
        f: java.io.File, p: Process[String, A], z: B)(
            g: (B, A) ⇒ B): B = {
        @annotation.tailrec
        def go(ss: Iterator[String], cur: Process[String, A], acc: B): B = {
            cur match {
                case Halt() ⇒ acc
                case Await(recv) ⇒
                    val next = if (ss.hasNext) recv(Some(ss.next))
                    else recv(None)
                    go(ss, next, acc)
                case Emit(o, tail) ⇒ go(ss, tail, g(acc, o))
            }
        }
        val s = Source.fromFile(f)
        try go(s.getLines, p, z)
        finally s.close
    }

    def toCelsius(fahrenheit: Double): Double = {
        // (5.0 / 9.0) * (fahrenheit - 32)
        fahrenheit / 2
    }

    /** ex15.9 */
    def main(args: Array[String]): Unit = {
        val printStream = new PrintStream("output.txt")
        val input_file = new File("input.txt")
        def output(u: Unit, s: Double): Unit = {
            printStream.println(s)
        }
        val process = (drop[String](0) map (_.trim)) |> filter[String] { s ⇒
            s.size != 0 && !s.startsWith("#")
        } map (s ⇒ toCelsius(s.toDouble))
        processFile(input_file, process, ())(output)
    }
}