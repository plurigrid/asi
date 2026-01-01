
# Julia ACSets.jl Path Equivalence Test
# Auto-generated from Python test suite

using ACSets

# Schema definition
@present SchBrowserHistory(FreeSchema) begin
    Browser::Ob
    URL::Ob
    Visit::Ob
    Domain::Ob
    String::AttrType
    Int::AttrType
    browser_of::Hom(URL, Browser)
    domain_of::Hom(URL, Domain)
    url_of::Hom(Visit, URL)
    from_visit::Hom(Visit, Visit)
    browser_name::Attr(Browser, String)
    url_text::Attr(URL, String)
    visit_time::Attr(Visit, Int)
    domain_name::Attr(Domain, String)
end

@acset_type BrowserHistoryACSet(SchBrowserHistory)

# Build test data
acs = BrowserHistoryACSet()

# Add browsers
b1 = add_part!(acs, :Browser; browser_name="ChatGPT Atlas")
b2 = add_part!(acs, :Browser; browser_name="Safari")

# Add domains
d1 = add_part!(acs, :Domain; domain_name="github.com")
d2 = add_part!(acs, :Domain; domain_name="ampcode.com")
d3 = add_part!(acs, :Domain; domain_name="chatgpt.com")

# Add URLs
u1 = add_part!(acs, :URL; url_text="https://github.com/bmorphism/Gay.jl", browser_of=b1, domain_of=d1)
u2 = add_part!(acs, :URL; url_text="https://ampcode.com/workspaces/ies", browser_of=b1, domain_of=d2)
u3 = add_part!(acs, :URL; url_text="https://chatgpt.com/", browser_of=b1, domain_of=d3)
u4 = add_part!(acs, :URL; url_text="https://github.com/AlgebraicJulia", browser_of=b2, domain_of=d1)

# Add visits
v1 = add_part!(acs, :Visit; url_of=u1, visit_time=1000)
v2 = add_part!(acs, :Visit; url_of=u2, visit_time=1001, from_visit=v1)
v3 = add_part!(acs, :Visit; url_of=u3, visit_time=1002, from_visit=v2)
v4 = add_part!(acs, :Visit; url_of=u1, visit_time=1003, from_visit=v3)
v5 = add_part!(acs, :Visit; url_of=u4, visit_time=1004)

# Tests
@assert nparts(acs, :Browser) == 2
@assert nparts(acs, :URL) == 4
@assert nparts(acs, :Visit) == 5
@assert nparts(acs, :Domain) == 3

# Subpart lookup
@assert subpart(acs, 1, :browser_of) == 1
@assert subpart(acs, 1, :browser_name) == "ChatGPT Atlas"

# Incident
@assert sort(incident(acs, 1, :browser_of)) == [1, 2, 3]
@assert sort(incident(acs, 1, :domain_of)) == [1, 4]

# Path composition
@assert subpart(acs, 1, :url_of) == 1
@assert subpart(acs, subpart(acs, 1, :url_of), :domain_of) == 1

# Reflexive hom chain
@assert subpart(acs, 2, :from_visit) == 1
@assert subpart(acs, 3, :from_visit) == 2
@assert subpart(acs, 4, :from_visit) == 3

println("✓ All ACSets.jl path equivalence tests passed!")
