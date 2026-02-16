"""
    Login Test Example

Demonstrates:
1. Creating a Playwright skill with deterministic seed
2. Deriving selectors for login form elements
3. Generating and running tripartite tests
4. Verifying GF(3) conservation

Usage:
    julia examples/login_test.jl
"""

include("../lib/playwright_unworld.jl")
include("../lib/tripartite_testing.jl")

using .PlaywrightUnworld
using .TripartitePlaywrightTesting

# ============================================================================
# Example 1: Create Skill and Derive Selectors
# ============================================================================

println("\n" * "="^70)
println("EXAMPLE 1: Login Skill Creation & Selector Derivation")
println("="^70)

# Create a skill for login testing with deterministic seed
genesis_seed = 0x42D  # "Ramanujan"
skill = create_playwright_skill("login-test-skill", genesis_seed, "https://example.com/login")

println("\nSkill created:")
println("  Genesis seed: 0x$(string(genesis_seed; base=16))")
println("  Target URL: $(skill.target_url)")
println("  Browser viewport: $(skill.browser_context.viewport_width)x$(skill.browser_context.viewport_height)")
println("  Device scale: $(skill.browser_context.device_scale_factor)")
println("  Timezone: $(skill.browser_context.timezone)")
println("  Locale: $(skill.browser_context.locale)")

# Define candidate selectors for form elements
email_candidates = [
    "[data-testid=email-input]",
    "[name=email]",
    "[role=textbox]",
    ".email-field",
    "#email"
]

password_candidates = [
    "[data-testid=password-input]",
    "[name=password]",
    "[type=password]",
    ".password-field",
    "#password"
]

submit_candidates = [
    "[data-testid=login-button]",
    "[role=button]:has-text(\"Log in\")",
    "button.login-btn",
    "[type=submit]",
    "#submit"
]

# Derive selectors from candidates
println("\n" * "-"^70)
println("Deriving selectors from candidates...")

add_selector!(skill, "email-input", "textbox", email_candidates)
add_selector!(skill, "password-input", "textbox", password_candidates)
add_selector!(skill, "login-button", "button", submit_candidates)

# Retrieve and display derived selectors
email_sel = get_selector(skill, "email-input", "textbox")
pwd_sel = get_selector(skill, "password-input", "textbox")
btn_sel = get_selector(skill, "login-button", "button")

println("  Email selector: $(email_sel.locator_string) (robustness: $(email_sel.robustness))")
println("  Password selector: $(pwd_sel.locator_string) (robustness: $(pwd_sel.robustness))")
println("  Button selector: $(btn_sel.locator_string) (robustness: $(btn_sel.robustness))")

# ============================================================================
# Example 2: Generate Tripartite Test Suite
# ============================================================================

println("\n" * "-"^70)
println("Generating tripartite test suite for login page...")

page_type = "login"
action_graph = ["fill_email", "fill_password", "click_submit"]

test_suite = generate_tripartite_tests(genesis_seed, page_type, action_graph)

println("\nTest suite generated:")
println("  MINUS tests (refutation): $(length(test_suite.minus_tests))")
println("  ERGODIC tests (neutral): $(length(test_suite.ergodic_tests))")
println("  PLUS tests (confirmation): $(length(test_suite.plus_tests))")
println("  Total tests: $(test_suite.total_tests)")
println("  GF(3) balanced: $(test_suite.gf3_balanced)")

# ============================================================================
# Example 3: Display Sample Tests from Each Category
# ============================================================================

println("\n" * "-"^70)
println("Sample tests from each category:")

if !isempty(test_suite.minus_tests)
    minus_test = test_suite.minus_tests[1]
    println("\n[MINUS] $(minus_test.name)")
    println("  Description: $(minus_test.description)")
    println("  Expected outcome: $(minus_test.expected_outcome)")
    println("  Timeout: $(minus_test.timeout)ms")
    println("  Steps:")
    for step in minus_test.steps[1:min(2, length(minus_test.steps))]
        println("    - $step")
    end
end

if !isempty(test_suite.ergodic_tests)
    ergodic_test = test_suite.ergodic_tests[1]
    println("\n[ERGODIC] $(ergodic_test.name)")
    println("  Description: $(ergodic_test.description)")
    println("  Expected outcome: $(ergodic_test.expected_outcome)")
    println("  Timeout: $(ergodic_test.timeout)ms")
    println("  Steps:")
    for step in ergodic_test.steps[1:min(2, length(ergodic_test.steps))]
        println("    - $step")
    end
end

if !isempty(test_suite.plus_tests)
    plus_test = test_suite.plus_tests[1]
    println("\n[PLUS] $(plus_test.name)")
    println("  Description: $(plus_test.description)")
    println("  Expected outcome: $(plus_test.expected_outcome)")
    println("  Timeout: $(plus_test.timeout)ms")
    println("  Steps:")
    for step in plus_test.steps[1:min(2, length(plus_test.steps))]
        println("    - $step")
    end
end

# ============================================================================
# Example 4: Verify GF(3) Conservation
# ============================================================================

println("\n" * "-"^70)
println("Verifying GF(3) conservation...")

# Manually verify balance
minus_polarity = length(test_suite.minus_tests) * (-1)
ergodic_polarity = length(test_suite.ergodic_tests) * 0
plus_polarity = length(test_suite.plus_tests) * (+1)
total_polarity = minus_polarity + ergodic_polarity + plus_polarity

println("\nPolarity calculation:")
println("  MINUS: $(length(test_suite.minus_tests)) tests × (-1) = $minus_polarity")
println("  ERGODIC: $(length(test_suite.ergodic_tests)) tests × (0) = $ergodic_polarity")
println("  PLUS: $(length(test_suite.plus_tests)) tests × (+1) = $plus_polarity")
println("  Total: $total_polarity")
println("  Modulo 3: $(total_polarity % 3)")
println("  Conserved: $(total_polarity % 3 == 0 ? "✓ YES" : "✗ NO")")

# ============================================================================
# Example 5: Skill Summary
# ============================================================================

println("\n" * "-"^70)
println("Skill Summary")

summary = summarize(skill)

println("\nSkill state:")
println("  Name: $(summary[:name])")
println("  Target URL: $(summary[:target_url])")
println("  Number of selectors: $(summary[:num_selectors])")
println("  Screenshot full page: $(summary[:screenshot_full_page])")
println("  PDF format: $(summary[:pdf_format])")
println("  GF(3) balanced: $(summary[:gf3_balanced])")

browser_ctx = summary[:browser_context]
println("\nBrowser context:")
println("  Viewport: $(browser_ctx[:viewport])")
println("  Timezone: $(browser_ctx[:timezone])")
println("  Locale: $(browser_ctx[:locale])")
println("  Color scheme: $(browser_ctx[:color_scheme])")

# ============================================================================
# Example 6: Pseudocode for Actual Test Execution
# ============================================================================

println("\n" * "="^70)
println("PSEUDOCODE: Actual Test Execution")
println("="^70)

println("""

The following would be actual Playwright API calls (pseudocode):

# Open browser with derived context
context = browser.new_context(
    viewport: {width: $(skill.browser_context.viewport_width),
                height: $(skill.browser_context.viewport_height)},
    timezone_id: "$(skill.browser_context.timezone)",
    locale: "$(skill.browser_context.locale)",
    color_scheme: "$(skill.browser_context.color_scheme)"
)

# Navigate with deterministic timeout
page = context.new_page()
page.goto("$(skill.target_url)", timeout: $(skill.screenshot_params.timeout))

# Test: ERGODIC (happy path)
page.fill("$(email_sel.locator_string)", "user@example.com")
page.fill("$(pwd_sel.locator_string)", "password123")
page.click("$(btn_sel.locator_string)")
expect(page).to have_url("https://example.com/dashboard")

# Test: MINUS (refutation - invalid email)
page.goto("$(skill.target_url)")
page.fill("$(email_sel.locator_string)", "invalid-email")
page.fill("$(pwd_sel.locator_string)", "")
page.click("$(btn_sel.locator_string)")
expect(page.locator("text=Error")).to be visible

# Test: PLUS (confirmation - remember me, session management)
page.goto("$(skill.target_url)")
page.fill("$(email_sel.locator_string)", "user@example.com")
page.fill("$(pwd_sel.locator_string)", "password123")
page.check("[data-testid=remember-me]")
page.click("$(btn_sel.locator_string)")
expect(page.locator("text=Logged in")).to be visible

# Record video with deterministic params
page.video.path() => "login_test_0x$(string(genesis_seed; base=16)).webm"

# Capture screenshots
page.screenshot(
    full_page: $(skill.screenshot_params.full_page),
    path: "login_screenshot.png"
)

# Generate PDF
page.pdf(
    path: "login_report.pdf",
    format: "$(skill.pdf_params.format)",
    margin: {
        top: $(skill.pdf_params.margin_top),
        bottom: $(skill.pdf_params.margin_bottom),
        left: $(skill.pdf_params.margin_left),
        right: $(skill.pdf_params.margin_right)
    },
    print_background: $(skill.pdf_params.print_background)
)

context.close()
""")

println("\n" * "="^70)
println("END EXAMPLE")
println("="^70)
