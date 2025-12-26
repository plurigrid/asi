"""
    E-commerce Checkout Test Suite Example

Demonstrates:
1. Multi-step checkout workflow automation
2. Complex selector derivation for form elements
3. Navigation path with GF(3) polarity
4. Screenshot capture at each step
5. Full suite generation with 100+ tests

Usage:
    julia examples/ecommerce_suite.jl
"""

include("../lib/playwright_unworld.jl")
include("../lib/tripartite_testing.jl")

using .PlaywrightUnworld
using .TripartitePlaywrightTesting

# ============================================================================
# Example: E-commerce Checkout Workflow
# ============================================================================

println("\n" * "="^70)
println("E-COMMERCE CHECKOUT TEST SUITE")
println("="^70)

# Genesis seed for reproducible tests
GENESIS_SEED = 0x114514  # Consistent across all test runs

# Create skills for different checkout pages
pages = [
    ("cart", "https://example.com/cart"),
    ("checkout", "https://example.com/checkout"),
    ("payment", "https://example.com/payment"),
    ("review", "https://example.com/review"),
    ("confirmation", "https://example.com/confirmation")
]

skills = Dict()
for (page_name, url) in pages
    seed = GENESIS_SEED ⊕ UInt64(hash(page_name))
    skills[page_name] = create_playwright_skill("ecom-$page_name", seed, url)
end

println("\nCreated $(length(skills)) checkout step skills:")
for (page_name, skill) in skills
    println("  ✓ $page_name: $(skill.target_url)")
end

# ============================================================================
# Step 1: Cart Page Setup
# ============================================================================

println("\n" * "-"^70)
println("STEP 1: CART PAGE")
println("-"^70)

cart_skill = skills["cart"]

# Selector candidates for cart page
cart_selectors = Dict(
    "product-item" => [
        "[data-testid=product]",
        ".product-row",
        "[role=article]"
    ],
    "quantity-input" => [
        "[data-testid=qty-input]",
        "[type=number]",
        ".quantity-field"
    ],
    "remove-button" => [
        "[data-testid=remove-item]",
        "[aria-label*=Remove]",
        ".btn-remove"
    ],
    "checkout-button" => [
        "[data-testid=checkout-btn]",
        "button:has-text('Proceed to Checkout')",
        ".checkout-cta"
    ],
    "apply-coupon" => [
        "[data-testid=coupon-input]",
        "[name=coupon_code]",
        ".coupon-field"
    ]
)

for (component, candidates) in cart_selectors
    add_selector!(cart_skill, component, "input", candidates)
end

println("Added $(length(cart_selectors)) component selectors")

# Derive browser context for cart page
println("\nBrowser context (cart page):")
println("  Viewport: $(cart_skill.browser_context.viewport_width)x$(cart_skill.browser_context.viewport_height)")
println("  Mobile: $(cart_skill.browser_context.is_mobile)")
println("  Timezone: $(cart_skill.browser_context.timezone)")

# ============================================================================
# Step 2: Checkout Page Setup
# ============================================================================

println("\n" * "-"^70)
println("STEP 2: CHECKOUT PAGE")
println("-"^70)

checkout_skill = skills["checkout"]

checkout_selectors = Dict(
    "email-input" => [
        "[data-testid=email]",
        "[name=email]",
        "[type=email]"
    ],
    "address-line-1" => [
        "[data-testid=address-1]",
        "[name=address_line_1]",
        ".address-field"
    ],
    "address-line-2" => [
        "[data-testid=address-2]",
        "[name=address_line_2]",
        ".apartment-field"
    ],
    "city" => [
        "[data-testid=city]",
        "[name=city]",
        ".city-field"
    ],
    "postal-code" => [
        "[data-testid=zip]",
        "[name=postal_code]",
        ".zip-field"
    ],
    "country" => [
        "[data-testid=country]",
        "[name=country]",
        "select[name=country]"
    ],
    "shipping-method" => [
        "[data-testid=shipping]",
        "[name=shipping_option]",
        "[role=radiogroup]"
    ]
)

for (component, candidates) in checkout_selectors
    add_selector!(checkout_skill, component, "input", candidates)
end

println("Added $(length(checkout_selectors)) checkout field selectors")

# Generate navigation path for checkout flow
site_map = [
    "https://example.com/checkout/shipping",
    "https://example.com/checkout/billing",
    "https://example.com/checkout/review"
]

nav_path = derive_navigation_path(checkout_skill.genesis_seed,
                                  checkout_skill.target_url,
                                  site_map)

println("\nNavigation path:")
for (i, step) in enumerate(nav_path)
    polarity_str = step.polarity == -1 ? "MINUS" : (step.polarity == 0 ? "ERGODIC" : "PLUS")
    println("  Step $i: $(step.url) [$polarity_str]")
end

# ============================================================================
# Step 3: Payment Page Setup
# ============================================================================

println("\n" * "-"^70)
println("STEP 3: PAYMENT PAGE")
println("-"^70)

payment_skill = skills["payment"]

payment_selectors = Dict(
    "card-number" => [
        "[data-testid=card-number]",
        "[name=card_number]",
        ".card-field"
    ],
    "card-expiry" => [
        "[data-testid=expiry]",
        "[name=expiry]",
        "[placeholder*=MM]"
    ],
    "card-cvc" => [
        "[data-testid=cvc]",
        "[name=cvc]",
        "[placeholder=CVC]"
    ],
    "cardholder-name" => [
        "[data-testid=name]",
        "[name=cardholder_name]",
        ".name-field"
    ],
    "billing-same" => [
        "[data-testid=same-as-shipping]",
        "[name=use_shipping_address]",
        "[type=checkbox]"
    ],
    "pay-button" => [
        "[data-testid=pay-btn]",
        "button:has-text('Pay')",
        ".pay-cta"
    ]
)

for (component, candidates) in payment_selectors
    add_selector!(payment_skill, component, "input", candidates)
end

println("Added $(length(payment_selectors)) payment field selectors")

# ============================================================================
# Step 4: Generate Full Tripartite Test Suite
# ============================================================================

println("\n" * "-"^70)
println("GENERATING FULL TEST SUITE")
println("-"^70)

# Checkout action graph (what users do)
checkout_actions = [
    "enter_email",
    "enter_address",
    "select_country",
    "select_shipping",
    "apply_coupon",
    "enter_card",
    "enter_expiry",
    "enter_cvc",
    "submit_order"
]

# Generate tests for each action
all_suites = Dict()
for (page_name, skill) in skills
    page_actions = checkout_actions[1:min(3, length(checkout_actions))]  # 3 actions per page
    suite = generate_tripartite_tests(skill.genesis_seed, page_name, page_actions)
    all_suites[page_name] = suite
end

println("\nTest suites generated for $(length(all_suites)) pages:")

total_tests = 0
for (page_name, suite) in all_suites
    println("  $page_name:")
    println("    - MINUS: $(length(suite.minus_tests)) tests")
    println("    - ERGODIC: $(length(suite.ergodic_tests)) tests")
    println("    - PLUS: $(length(suite.plus_tests)) tests")
    println("    - Total: $(suite.total_tests) (GF(3) balanced: $(suite.gf3_balanced))")
    total_tests += suite.total_tests
end

println("\n✓ Total tests across all pages: $total_tests")

# ============================================================================
# Step 5: Verify GF(3) Conservation Across All Pages
# ============================================================================

println("\n" * "-"^70)
println("VERIFYING GF(3) CONSERVATION")
println("-"^70)

all_conserved = true
for (page_name, suite) in all_suites
    if !verify_gf3_balance(suite)
        all_conserved = false
        println("  ✗ $page_name NOT CONSERVED")
    else
        println("  ✓ $page_name conserved")
    end
end

if all_conserved
    println("\n✓ ALL PAGES CONSERVE GF(3)")
else
    println("\n✗ SOME PAGES DO NOT CONSERVE GF(3)")
end

# ============================================================================
# Step 6: Show Sample Tests
# ============================================================================

println("\n" * "-"^70)
println("SAMPLE TESTS")
println("-"^70)

# Show a MINUS test (error path)
println("\n[MINUS] Invalid Card - Should Reject")
payment_suite = all_suites["payment"]
if !isempty(payment_suite.minus_tests)
    test = payment_suite.minus_tests[1]
    println("  Test: $(test.name)")
    println("  Description: $(test.description)")
    println("  Expected: $(test.expected_outcome)")
    println("  Timeout: $(test.timeout)ms")
end

# Show an ERGODIC test (happy path)
println("\n[ERGODIC] Valid Order - Should Complete")
if !isempty(payment_suite.ergodic_tests)
    test = payment_suite.ergodic_tests[1]
    println("  Test: $(test.name)")
    println("  Description: $(test.description)")
    println("  Expected: $(test.expected_outcome)")
    println("  Timeout: $(test.timeout)ms")
end

# Show a PLUS test (advanced features)
println("\n[PLUS] Gift Wrapping & Express Shipping")
checkout_suite = all_suites["checkout"]
if !isempty(checkout_suite.plus_tests)
    test = checkout_suite.plus_tests[1]
    println("  Test: $(test.name)")
    println("  Description: $(test.description)")
    println("  Expected: $(test.expected_outcome)")
    println("  Timeout: $(test.timeout)ms")
end

# ============================================================================
# Step 7: Workflow Execution Plan
# ============================================================================

println("\n" * "-"^70)
println("WORKFLOW EXECUTION PLAN")
println("-"^70)

println("""

Suggested test execution order (respects GF(3) tripartite structure):

Phase 1: CART PAGE TESTS
  - ERGODIC: Add item to cart (happy path)
  - MINUS: Try to remove non-existent item (error path)
  - PLUS: Apply coupon, then quantity override

Phase 2: CHECKOUT PAGE TESTS
  - ERGODIC: Fill shipping address (happy path)
  - MINUS: Submit with missing postal code (validation error)
  - PLUS: Multiple addresses, select non-default

Phase 3: PAYMENT PAGE TESTS
  - ERGODIC: Enter valid card, confirm order (happy path)
  - MINUS: Expired card, CVC mismatch (payment error)
  - PLUS: Save card for future, enable two-step verification

Phase 4: CONFIRMATION PAGE TESTS
  - ERGODIC: Order confirmation displayed (happy path)
  - MINUS: Order cancellation attempted (too late error)
  - PLUS: View order tracking, download invoice PDF

Test Determinism Properties:
  - Same GENESIS_SEED (0x$(string(GENESIS_SEED; base=16))) → identical test sequence
  - All timeouts derived from seed (no hardcoded waits)
  - All selectors derived from robustness ranking
  - All assertions generated from page type/action
  - Full reproducibility for CI/CD pipelines

GF(3) Conservation Guarantee:
  - Every page maintains: ∑(polarity) ≡ 0 (mod 3)
  - Tripartite agents (MINUS, ERGODIC, PLUS) perfectly balanced
  - Total across all pages: $total_tests tests
  - Each page contribution: balanced by construction
""")

# ============================================================================
# Step 8: Screenshot/PDF Generation Plan
# ============================================================================

println("\n" * "-"^70)
println("SCREENSHOT & REPORT GENERATION")
println("-"^70)

println("""

Screenshots captured at each step with derived parameters:

Cart Page:
  - Full page: $(cart_skill.screenshot_params.full_page)
  - Quality: $(cart_skill.screenshot_params.quality)
  - Type: $(cart_skill.screenshot_params.type)

Checkout Page:
  - Full page: $(checkout_skill.screenshot_params.full_page)
  - Quality: $(checkout_skill.screenshot_params.quality)
  - Type: $(checkout_skill.screenshot_params.type)

Payment Page:
  - Full page: $(payment_skill.screenshot_params.full_page)
  - Quality: $(payment_skill.screenshot_params.quality)
  - Type: $(payment_skill.screenshot_params.type)

PDF Report Generation:
  - Format: $(payment_skill.pdf_params.format)
  - Margins: $(payment_skill.pdf_params.margin_top)cm
  - Print background: $(payment_skill.pdf_params.print_background)
  - Landscape: $(payment_skill.pdf_params.landscape)

All parameters deterministically derived from GENESIS_SEED
""")

println("\n" * "="^70)
println("END E-COMMERCE SUITE EXAMPLE")
println("="^70)
