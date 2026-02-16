// Kotlin MTL: Pragmatic safety with sealed classes
// GF(3) trit: 0 (ERGODIC)

sealed class MTLFormula {
    abstract fun evaluate(trace: List<TimedEvent>, currentTime: Long): Boolean
}

data class Interval(val lower: Long, val upper: Long)
data class TimedEvent(val timestamp: Long, val predicate: String, val value: Boolean)

data class Predicate(val name: String) : MTLFormula() {
    override fun evaluate(trace: List<TimedEvent>, currentTime: Long): Boolean =
        trace
            .filter { it.timestamp <= currentTime && it.predicate == name }
            .lastOrNull()
            ?.value ?: false
}

data class Eventually(val interval: Interval, val formula: MTLFormula) : MTLFormula() {
    override fun evaluate(trace: List<TimedEvent>, currentTime: Long): Boolean {
        val start = currentTime + interval.lower
        val end = currentTime + interval.upper
        return trace
            .filter { it.timestamp in start..end }
            .any { formula.evaluate(trace, it.timestamp) }
    }
}

data class Always(val interval: Interval, val formula: MTLFormula) : MTLFormula() {
    override fun evaluate(trace: List<TimedEvent>, currentTime: Long): Boolean {
        val start = currentTime + interval.lower
        val end = currentTime + interval.upper
        val eventsInInterval = trace.filter { it.timestamp in start..end }
        return eventsInInterval.isNotEmpty() && 
               eventsInInterval.all { formula.evaluate(trace, it.timestamp) }
    }
}

object CRDTProperties {
    fun convergence(tauMix: Long) = 
        Eventually(Interval(0, tauMix), Predicate("replicas_converged"))
    
    fun commutativity() = 
        Always(Interval(0, Long.MAX_VALUE), Predicate("merge_commutative"))
}
