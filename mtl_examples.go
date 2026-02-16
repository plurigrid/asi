// Go MTL: Interface-based polymorphism for extensibility
// GF(3) trit: 0 (ERGODIC)

package mtl

type Interval struct {
	Lower, Upper uint64
}

type TimedEvent struct {
	Timestamp uint64
	Predicate string
	Value     bool
}

type MTLFormula interface {
	Evaluate(trace []TimedEvent, currentTime uint64) bool
}

type PredicateFormula struct {
	Name string
}

func (p *PredicateFormula) Evaluate(trace []TimedEvent, currentTime uint64) bool {
	for _, event := range trace {
		if event.Predicate == p.Name && event.Timestamp <= currentTime && event.Value {
			return true
		}
	}
	return false
}

type EventuallyFormula struct {
	Interval  Interval
	Formula   MTLFormula
}

func (e *EventuallyFormula) Evaluate(trace []TimedEvent, currentTime uint64) bool {
	start := currentTime + e.Interval.Lower
	end := currentTime + e.Interval.Upper
	for _, event := range trace {
		if event.Timestamp >= start && event.Timestamp <= end {
			if e.Formula.Evaluate(trace, event.Timestamp) {
				return true
			}
		}
	}
	return false
}

// CRDT convergence: ◇[0,τ_mix](replicas_converged)
func CRDTConvergence(tauMix uint64) MTLFormula {
	return &EventuallyFormula{
		Interval: Interval{Lower: 0, Upper: tauMix},
		Formula:  &PredicateFormula{Name: "replicas_converged"},
	}
}
