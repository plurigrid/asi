# Interrupteurs ACSet Schema
# GF(3)-conserved session interrupt tracking

using Catlab.CategoricalAlgebra, ACSets

@present SchInterrupteurs(FreeSchema) begin
    # Objects
    Session::Ob
    Intake::Ob
    Interrupt::Ob
    Trit::Ob
    Concept::Ob
    Balance::Ob
    
    # Trit structure
    TritValue::AttrType
    TritSymbol::AttrType
    trit_value::Attr(Trit, TritValue)      # -1, 0, +1
    trit_symbol::Attr(Trit, TritSymbol)    # MINUS, ERGODIC, PLUS
    
    # Balance structure (GF(3) conservation)
    Count::AttrType
    balance_minus::Attr(Balance, Count)
    balance_ergodic::Attr(Balance, Count)
    balance_plus::Attr(Balance, Count)
    # sum = -1*minus + 0*ergodic + 1*plus (computed)
    
    # Session morphisms
    SessionId::AttrType
    session_start::Attr(Session, SessionId)
    session_end::Attr(Session, SessionId)
    
    # Intake structure
    Name::AttrType
    Color::AttrType
    Clock::AttrType
    intake_session::Hom(Intake, Session)
    intake_trit::Hom(Intake, Trit)
    intake_name::Attr(Intake, Name)
    intake_color::Attr(Intake, Color)      # Gay.jl hex
    intake_clock::Attr(Intake, Clock)      # Logical clock
    
    # Interrupt structure (world/coworld transition)
    InterruptType::AttrType
    GapSeconds::AttrType
    interrupt_ends::Hom(Interrupt, Session)    # ends this session
    interrupt_starts::Hom(Interrupt, Session)  # starts next session
    interrupt_balance::Hom(Interrupt, Balance) # balance at interrupt
    interrupt_type::Attr(Interrupt, InterruptType)
    interrupt_gap::Attr(Interrupt, GapSeconds)
    
    # Concept extraction
    Freq::AttrType
    concept_source::Hom(Concept, Intake)
    concept_name::Attr(Concept, Name)
    concept_freq::Attr(Concept, Freq)
end

@acset_type Interrupteurs(SchInterrupteurs,
    index=[:intake_session, :intake_trit, :interrupt_ends, :interrupt_starts])

# GF(3) conservation check
function is_conserved(db::Interrupteurs, session_id::Int)
    intakes = incident(db, session_id, :intake_session)
    trits = [db[i, :intake_trit] for i in intakes]
    values = [db[t, :trit_value] for t in trits]
    return sum(values) % 3 == 0
end

# Create interrupt with balance snapshot
function create_interrupt!(db::Interrupteurs, 
                           ends_session::Int, 
                           starts_session::Int,
                           itype::String,
                           gap::Float64)
    # Count trits in ending session
    intakes = incident(db, ends_session, :intake_session)
    trits = [db[i, :intake_trit] for i in intakes]
    values = [db[t, :trit_value] for t in trits]
    
    minus = count(==(−1), values)
    ergodic = count(==(0), values)
    plus = count(==(1), values)
    
    # Create balance record
    b = add_part!(db, :Balance; 
        balance_minus=minus, 
        balance_ergodic=ergodic, 
        balance_plus=plus)
    
    # Create interrupt
    add_part!(db, :Interrupt;
        interrupt_ends=ends_session,
        interrupt_starts=starts_session,
        interrupt_balance=b,
        interrupt_type=itype,
        interrupt_gap=gap)
end
