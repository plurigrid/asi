// Java MTL: OOP with records and streams
// GF(3) trit: 0 (ERGODIC)

public interface MTLFormula {
    boolean evaluate(java.util.List<TimedEvent> trace, long currentTime);
}

public record Interval(long lower, long upper) {}
public record TimedEvent(long timestamp, String predicate, boolean value) {}

public class PredicateFormula implements MTLFormula {
    private final String name;
    
    public PredicateFormula(String name) { this.name = name; }
    
    @Override
    public boolean evaluate(java.util.List<TimedEvent> trace, long currentTime) {
        return trace.stream()
            .filter(e -> e.timestamp() <= currentTime && e.predicate().equals(name))
            .findLast()
            .map(TimedEvent::value)
            .orElse(false);
    }
}

public class EventuallyFormula implements MTLFormula {
    private final Interval interval;
    private final MTLFormula formula;
    
    public EventuallyFormula(Interval interval, MTLFormula formula) {
        this.interval = interval;
        this.formula = formula;
    }
    
    @Override
    public boolean evaluate(java.util.List<TimedEvent> trace, long currentTime) {
        long start = currentTime + interval.lower();
        long end = currentTime + interval.upper();
        return trace.stream()
            .filter(e -> e.timestamp() >= start && e.timestamp() <= end)
            .anyMatch(e -> formula.evaluate(trace, e.timestamp()));
    }
}

public class CRDTProperties {
    public static MTLFormula convergence(long tauMix) {
        return new EventuallyFormula(
            new Interval(0, tauMix),
            new PredicateFormula("replicas_converged")
        );
    }
}
