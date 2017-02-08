package local_effects

import scala.collection.mutable.HashMap

/** ex14.3 */

sealed abstract class STMap[S, K, V] {
    protected def value: HashMap[K, V]
    def size: ST[S, Int] = ST(value.size)
    def apply(k: K): ST[S, V] = ST(value(k))
    def write(k: K, v: V): ST[S, Unit] = ST(value += ((k, v)))
    def read(k: K): ST[S, Option[V]] = ST(value.get(k))
    def remove(k: K): ST[S, Unit] = ST(value.remove(k))
}

object STMap {
    def apply[S, K, V]: ST[S, STMap[S, K, V]] = ST(new STMap[S, K, V] {
        val value = new HashMap[K, V]
    })
}