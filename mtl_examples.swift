// Swift MTL: Protocol-based safety with optionals
// GF(3) trit: +1 (PLUS generator)

struct Interval {
    let lower: UInt64
    let upper: UInt64
}

struct TimedEvent {
    let timestamp: UInt64
    let predicate: String
    let value: Bool
}

protocol MTLFormula {
    func evaluate(trace: [TimedEvent], currentTime: UInt64) -> Bool
}

struct Predicate: MTLFormula {
    let name: String
    
    func evaluate(trace: [TimedEvent], currentTime: UInt64) -> Bool {
        trace
            .filter { /bin/zsh.timestamp <= currentTime && /bin/zsh.predicate == name }
            .last
            .map { /bin/zsh.value } ?? false
    }
}

struct Eventually: MTLFormula {
    let interval: Interval
    let formula: MTLFormula
    
    func evaluate(trace: [TimedEvent], currentTime: UInt64) -> Bool {
        let start = currentTime + interval.lower
        let end = currentTime + interval.upper
        return trace
            .filter { /bin/zsh.timestamp >= start && /bin/zsh.timestamp <= end }
            .contains { formula.evaluate(trace: trace, currentTime: /bin/zsh.timestamp) }
    }
}

struct Always: MTLFormula {
    let interval: Interval
    let formula: MTLFormula
    
    func evaluate(trace: [TimedEvent], currentTime: UInt64) -> Bool {
        let start = currentTime + interval.lower
        let end = currentTime + interval.upper
        let eventsInInterval = trace.filter { /bin/zsh.timestamp >= start && /bin/zsh.timestamp <= end }
        return !eventsInInterval.isEmpty &&
               eventsInInterval.allSatisfy { formula.evaluate(trace: trace, currentTime: /bin/zsh.timestamp) }
    }
}

// CRDT convergence: ◇[0,τ_mix](replicas_converged)
func crdtConvergence(tauMix: UInt64) -> MTLFormula {
    Eventually(
        interval: Interval(lower: 0, upper: tauMix),
        formula: Predicate(name: "replicas_converged")
    )
}
