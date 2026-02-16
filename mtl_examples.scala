// Scala MTL: Functional abstractions with case classes
// GF(3) trit: +1 (PLUS generator)

sealed trait MTLFormula {
  def evaluate(trace: Seq[TimedEvent], currentTime: Long): Boolean
}

case class Interval(lower: Long, upper: Long)
case class TimedEvent(timestamp: Long, predicate: String, value: Boolean)

case class Predicate(name: String) extends MTLFormula {
  def evaluate(trace: Seq[TimedEvent], currentTime: Long): Boolean =
    trace
      .filter(_.timestamp <= currentTime)
      .filter(_.predicate == name)
      .lastOption
      .map(_.value)
      .getOrElse(false)
}

case class Eventually(interval: Interval, formula: MTLFormula) extends MTLFormula {
  def evaluate(trace: Seq[TimedEvent], currentTime: Long): Boolean = {
    val start = currentTime + interval.lower
    val end = currentTime + interval.upper
    trace
      .filter(e => e.timestamp >= start && e.timestamp <= end)
      .exists(e => formula.evaluate(trace, e.timestamp))
  }
}

case class Always(interval: Interval, formula: MTLFormula) extends MTLFormula {
  def evaluate(trace: Seq[TimedEvent], currentTime: Long): Boolean = {
    val start = currentTime + interval.lower
    val end = currentTime + interval.upper
    val eventsInInterval = trace.filter(e => e.timestamp >= start && e.timestamp <= end)
    eventsInInterval.nonEmpty && eventsInInterval.forall(e => formula.evaluate(trace, e.timestamp))
  }
}

object CRDTProperties {
  def convergence(tauMix: Long) = 
    Eventually(Interval(0, tauMix), Predicate("replicas_converged"))
  
  def commutativity = 
    Always(Interval(0, Long.MaxValue), Predicate("merge_commutative"))
  
  def associativity = 
    Always(Interval(0, Long.MaxValue), Predicate("merge_associative"))
}
