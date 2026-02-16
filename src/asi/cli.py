#!/usr/bin/env python3
"""
asi - Algebraic Superintelligence CLI

Thin Python wrapper that delegates to Hy implementation.
This allows `uvx asi` to work while keeping core logic in Hy (Lisp).

Usage:
    uvx asi          # Show skills
    uvx asi skills   # List skills with GF(3)
    uvx asi gf3      # Show GF(3) conservation
    uvx asi run bb   # Run babashka tests
"""

def main():
    """Main entry point - delegates to Hy CLI"""
    # Import Hy runtime first
    import hy
    
    # Now import our Hy CLI module
    from asi.cli_hy import main as hy_main
    hy_main()


if __name__ == "__main__":
    main()
