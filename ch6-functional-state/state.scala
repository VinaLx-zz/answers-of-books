package functional_state

case class State[S, +A](run: S ⇒ (A, S)) {
    /** ex6.10 */
    def map[B](f: A ⇒ B): State[S, B] = {
        State { s ⇒
            val (a, sn) = run(s)
            (f(a), sn)
        }
    }

    def map2[B, C](sb: State[S, B])(f: (A, B) ⇒ C): State[S, C] = {
        State { s ⇒
            val (a, s1) = run(s)
            val (b, s2) = sb.run(s1)
            (f(a, b), s2)
        }
    }

    def flatMap[B](f: A ⇒ State[S, B]) = {
        State { (s: S) ⇒
            val (a, s1) = run(s)
            val state2 = f(a)
            state2.run(s1)
        }
    }
}

object State {
    def get[S]: State[S, S] = State(s ⇒ (s, s))

    def set[S](s: S): State[S, Unit] = State(_ ⇒ ((), s))

    def modify[S](f: S ⇒ S): State[S, Unit] = for {
        s ← get
        _ ← set(f(s))
    } yield ()

    /** ex6.10 */
    def unit[S, A](a: A): State[S, A] = State(s ⇒ (a, s))

    def sequence[S, A](ls: List[State[S, A]]): State[S, List[A]] = {
        ls.foldRight[State[S, List[A]]](unit(Nil)) {
            (s, sl) ⇒ s.map2(sl)(_ :: _)
        }
    }
}