#!/usr/bin/env python3
"""
Generate Zig code from templates and patterns.

This script helps generate common Zig code structures and patterns
based on user requirements, using templates and best practices.
"""

import argparse
import json
import logging
import sys
from pathlib import Path
from typing import Dict, List, Optional

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)

# Code generation templates
TEMPLATES = {
    'error_set': """
const {name}Error = error{{
{errors}
}};
""",

    'struct': """
const {name} = struct {{
{fields}
{methods}
}};
""",

    'enum': """
const {name} = enum {{
{values}
}};
""",

    'union': """
const {name} = union(enum) {{
{fields}
}};
""",

    'test_function': """
test "{description}" {{
{body}
}}
""",

    'allocator_function': """
fn {name}(allocator: std.mem.Allocator{params}) {return_type} {{
{body}
}}
""",

    'error_handling_function': """
fn {name}({params}) !{return_type} {{
{body}
}}
""",

    'generic_function': """
fn {name}(comptime T: type{params}) {return_type} {{
{body}
}}
""",

    'iterator': """
const {name}Iterator = struct {{
    items: []const {item_type},
    index: usize = 0,

    pub fn next(self: *{name}Iterator) ?{item_type} {{
        if (self.index >= self.items.len) return null;
        const item = self.items[self.index];
        self.index += 1;
        return item;
    }}
}};
""",

    'builder_pattern': """
const {name}Builder = struct {{
{fields}

    pub fn init() {name}Builder {{
        return .{{}};
    }}

{setters}

    pub fn build(self: {name}Builder) {name} {{
        return {name}{{
{field_assignments}
        }};
    }}
}};
""",

    'main_with_args': """
const std = @import("std");

pub fn main() !void {{
    var gpa = std.heap.GeneralPurposeAllocator(.{{}}){{}};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    if (args.len < 2) {{
        std.debug.print("Usage: {{s}} <arguments>\\n", .{{args[0]}});
        return;
    }}

{body}
}}
""",

    'cli_parser': """
const std = @import("std");

const Config = struct {{
{config_fields}
}};

fn parseArgs(allocator: std.mem.Allocator, args: [][]const u8) !Config {{
    var config = Config{{}};

    var i: usize = 1;
    while (i < args.len) : (i += 1) {{
{parse_logic}
    }}

    return config;
}}
""",

    'async_function': """
// Note: Async/await removed in Zig 0.11+
// Use threads or event loops instead
fn {name}Async({params}) void {{
    const thread = try std.Thread.spawn(.{{}}, {name}Worker, .{{{args}}});
    thread.join();
}}

fn {name}Worker({params}) void {{
{body}
}}
"""
}


class CodeGenerator:
    """Generate Zig code from templates and patterns."""

    def __init__(self, templates_dir: Optional[Path] = None):
        """Initialize code generator with optional templates directory."""
        self.templates_dir = templates_dir
        self.custom_templates = {}

        if templates_dir and templates_dir.exists():
            self.load_custom_templates()

    def load_custom_templates(self):
        """Load custom templates from templates directory."""
        if not self.templates_dir:
            return

        for template_file in self.templates_dir.glob('*.zig'):
            name = template_file.stem
            content = template_file.read_text(encoding='utf-8')
            self.custom_templates[name] = content
            logger.debug(f"Loaded custom template: {name}")

    def generate_struct(self, name: str, fields: List[Dict], methods: List[Dict] = None) -> str:
        """Generate a struct with fields and methods."""
        field_lines = []
        for field in fields:
            field_type = field.get('type', 'i32')
            field_name = field.get('name', 'field')
            default = field.get('default', '')

            if default:
                field_lines.append(f"    {field_name}: {field_type} = {default},")
            else:
                field_lines.append(f"    {field_name}: {field_type},")

        method_lines = []
        if methods:
            for method in methods:
                method_lines.append("")
                method_lines.append(f"    pub fn {method['name']}({method.get('params', 'self: *const @This()')}) {method.get('return_type', 'void')} {{")
                method_lines.append(f"        {method.get('body', '// TODO: Implement')}")
                method_lines.append("    }")

        return TEMPLATES['struct'].format(
            name=name,
            fields='\n'.join(field_lines),
            methods='\n'.join(method_lines) if method_lines else ''
        )

    def generate_error_set(self, name: str, errors: List[str]) -> str:
        """Generate an error set."""
        error_lines = [f"    {error}," for error in errors]
        return TEMPLATES['error_set'].format(
            name=name,
            errors='\n'.join(error_lines)
        )

    def generate_enum(self, name: str, values: List[str]) -> str:
        """Generate an enum."""
        value_lines = [f"    {value}," for value in values]
        return TEMPLATES['enum'].format(
            name=name,
            values='\n'.join(value_lines)
        )

    def generate_test(self, description: str, test_cases: List[Dict]) -> str:
        """Generate a test function."""
        body_lines = []

        for case in test_cases:
            if case.get('type') == 'expect':
                body_lines.append(f"    try testing.expect({case['condition']});")
            elif case.get('type') == 'expectEqual':
                body_lines.append(f"    try testing.expectEqual({case['expected']}, {case['actual']});")
            elif case.get('type') == 'expectError':
                body_lines.append(f"    try testing.expectError({case['error']}, {case['expression']});")
            else:
                body_lines.append(f"    {case.get('code', '// TODO: Add test case')}")

        return TEMPLATES['test_function'].format(
            description=description,
            body='\n'.join(body_lines)
        )

    def generate_iterator(self, name: str, item_type: str) -> str:
        """Generate an iterator pattern."""
        return TEMPLATES['iterator'].format(
            name=name,
            item_type=item_type
        )

    def generate_builder(self, name: str, fields: List[Dict]) -> str:
        """Generate builder pattern."""
        field_lines = []
        setter_lines = []
        assignment_lines = []

        for field in fields:
            field_name = field['name']
            field_type = field.get('type', 'i32')
            default = field.get('default', 'undefined')

            field_lines.append(f"    {field_name}: {field_type} = {default},")

            setter_lines.append(f"""
    pub fn set{field_name.capitalize()}(self: *{name}Builder, value: {field_type}) *{name}Builder {{
        self.{field_name} = value;
        return self;
    }}""")

            assignment_lines.append(f"            .{field_name} = self.{field_name},")

        return TEMPLATES['builder_pattern'].format(
            name=name,
            fields='\n'.join(field_lines),
            setters='\n'.join(setter_lines),
            field_assignments='\n'.join(assignment_lines)
        )

    def generate_from_spec(self, spec: Dict) -> str:
        """Generate code from a specification dictionary."""
        code_type = spec.get('type', 'struct')

        if code_type == 'struct':
            return self.generate_struct(
                spec['name'],
                spec.get('fields', []),
                spec.get('methods', [])
            )
        elif code_type == 'error_set':
            return self.generate_error_set(
                spec['name'],
                spec.get('errors', [])
            )
        elif code_type == 'enum':
            return self.generate_enum(
                spec['name'],
                spec.get('values', [])
            )
        elif code_type == 'test':
            return self.generate_test(
                spec.get('description', 'test'),
                spec.get('cases', [])
            )
        elif code_type == 'iterator':
            return self.generate_iterator(
                spec['name'],
                spec.get('item_type', 'i32')
            )
        elif code_type == 'builder':
            return self.generate_builder(
                spec['name'],
                spec.get('fields', [])
            )
        else:
            logger.warning(f"Unknown code type: {code_type}")
            return f"// Unknown code type: {code_type}"

    def generate_file(self, specs: List[Dict], imports: List[str] = None) -> str:
        """Generate a complete Zig file from multiple specifications."""
        lines = []

        # Add imports
        if imports:
            for imp in imports:
                if imp == 'std':
                    lines.append('const std = @import("std");')
                else:
                    lines.append(f'const {imp} = @import("{imp}");')
            lines.append('')

        # Generate code for each spec
        for spec in specs:
            code = self.generate_from_spec(spec)
            lines.append(code)
            lines.append('')

        return '\n'.join(lines)


def main():
    """Main entry point for code generator."""
    parser = argparse.ArgumentParser(
        description='Generate Zig code from templates and specifications'
    )
    parser.add_argument(
        'spec_file',
        help='JSON specification file for code generation'
    )
    parser.add_argument(
        '-o', '--output',
        help='Output file path (default: stdout)'
    )
    parser.add_argument(
        '-t', '--templates',
        help='Directory containing custom templates'
    )
    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Enable verbose logging'
    )

    args = parser.parse_args()

    # Configure logging
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    # Load specification
    spec_path = Path(args.spec_file)
    if not spec_path.exists():
        logger.error(f"Specification file not found: {spec_path}")
        sys.exit(1)

    try:
        with open(spec_path, 'r', encoding='utf-8') as f:
            spec = json.load(f)
    except json.JSONDecodeError as e:
        logger.error(f"Invalid JSON in spec file: {e}")
        sys.exit(1)

    # Create generator
    templates_dir = Path(args.templates) if args.templates else None
    generator = CodeGenerator(templates_dir)

    # Generate code
    try:
        if isinstance(spec, list):
            code = generator.generate_file(spec)
        elif 'specs' in spec:
            code = generator.generate_file(
                spec['specs'],
                spec.get('imports', ['std'])
            )
        else:
            code = generator.generate_from_spec(spec)

        # Output code
        if args.output:
            output_path = Path(args.output)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(code, encoding='utf-8')
            logger.info(f"✓ Generated code written to {output_path}")
        else:
            print(code)

    except Exception as e:
        logger.error(f"Code generation failed: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()