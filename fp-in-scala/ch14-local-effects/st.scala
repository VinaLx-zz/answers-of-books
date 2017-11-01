package local_effects

trait ST[S, A] { self ⇒
    protected def run(s: S): (A, S)
    def map[B](f: A ⇒ B): ST[S, B] = new ST[S, B] {
        def run(s: S) = {
            val (a, s1) = self.run(s)
            // what's the point of the returned `s1`?
            // why don't we just use s
            (f(a), s1)
        }
    }
    def flatMap[B](f: A ⇒ ST[S, B]): ST[S, B] = new ST[S, B] {
        def run(s: S) = {
            val (a, s1) = self.run(s)
            f(a).run(s1)
        }
    }
}

object ST {
    def apply[S, A](a: ⇒ A): ST[S, A] = {
        lazy val memo = a
        new ST[S, A] { def run(s: S) = (memo, s) }
    }

    def runST[A](st: RunnableST[A]): A = {
        st.apply[Unit].run(())._1
    }
}

sealed trait STRef[S, A] {
    protected var cell: A
    def read: ST[S, A] = ST(cell)
    def write(a: A): ST[S, Unit] = new ST[S, Unit] {
        def run(s: S) = {
            cell = a
            ((), s)
        }
    }
}

object STRef {
    def apply[S, A](a: A): ST[S, STRef[S, A]] = {
        ST(new STRef[S, A] { var cell = a })
    }
}

trait RunnableST[A] {
    def apply[S]: ST[S, A]
}

sealed abstract class STArray[S, A](implicit manifest: Manifest[A]) {
    protected def value: Array[A]
    def size: ST[S, Int] = ST(value.size)
    def write(i: Int, a: A): ST[S, Unit] = new ST[S, Unit] {
        def run(s: S) = {
            value(i) = a
            ((), s)
        }
    }
    def read(i: Int): ST[S, A] = ST(value(i))
    def freeze: ST[S, List[A]] = ST(value.toList)

    def swap(i: Int, j: Int): ST[S, Unit] = for {
        x ← read(i); y ← read(j)
        _ ← write(i, y); _ ← write(j, x)
    } yield ()

    /** ex14.1 */
    def fill(xs: Map[Int, A]): ST[S, Unit] = new ST[S, Unit] {
        def run(s: S) = {
            for ((k, v) ← xs) value(k) = v
            ((), s)
        }
    }

    // answer reference use foldRight and write
    def fill2(xs: Map[Int, A]): ST[S, Unit] = {
        xs.foldRight(ST[S, Unit](())) {
            case ((k, v), st) ⇒ st flatMap (_ ⇒ write(k, v))
        }
    }
}

object STArray {
    def apply[S, A: Manifest](sz: Int, v: A): ST[S, STArray[S, A]] = {
        ST(new STArray[S, A] { lazy val value = Array.fill(sz)(v) })
    }

    def fromList[S, A: Manifest](l: List[A]): ST[S, STArray[S, A]] = {
        ST(new STArray[S, A] { lazy val value = l.toArray })
    }
}