#!/usr/bin/env python3
"""
Recipe Query Tool - Search and filter cookbook recipes.

Usage:
    python scripts/query_recipes.py --topic memory
    python scripts/query_recipes.py --tag allocators
    python scripts/query_recipes.py --difficulty beginner
    python scripts/query_recipes.py --search "hash map"
    python scripts/query_recipes.py --recipe 1.1 --full
    python scripts/query_recipes.py --list-topics
    python scripts/query_recipes.py --list-tags

This tool queries the recipes-index.json to find relevant recipes
based on topic, tags, difficulty, or keyword search.
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Optional


def load_index(recipes_dir: Path) -> dict:
    """Load the recipes index JSON."""
    index_path = recipes_dir / "recipes-index.json"
    if not index_path.exists():
        print(f"Error: recipes-index.json not found at {index_path}")
        print("Run 'python build/cookbook_converter.py' first to generate the index.")
        sys.exit(1)

    with open(index_path, encoding="utf-8") as f:
        return json.load(f)


def filter_by_topic(recipes: list[dict], topic: str) -> list[dict]:
    """Filter recipes by topic."""
    topic_lower = topic.lower()
    return [r for r in recipes if r.get("topic", "").lower() == topic_lower]


def filter_by_tag(recipes: list[dict], tag: str) -> list[dict]:
    """Filter recipes that have the specified tag."""
    tag_lower = tag.lower()
    return [r for r in recipes if tag_lower in [t.lower() for t in r.get("tags", [])]]


def filter_by_difficulty(recipes: list[dict], difficulty: str) -> list[dict]:
    """Filter recipes by difficulty level."""
    diff_lower = difficulty.lower()
    return [r for r in recipes if r.get("difficulty", "").lower() == diff_lower]


def filter_by_search(recipes: list[dict], search_term: str) -> list[dict]:
    """Filter recipes by keyword search in title and tags."""
    term_lower = search_term.lower()
    results = []
    for r in recipes:
        title_match = term_lower in r.get("title", "").lower()
        tag_match = any(term_lower in t.lower() for t in r.get("tags", []))
        topic_match = term_lower in r.get("topic", "").lower()
        if title_match or tag_match or topic_match:
            results.append(r)
    return results


def filter_by_id(recipes: list[dict], recipe_id: str) -> Optional[dict]:
    """Get a specific recipe by ID."""
    for r in recipes:
        if r.get("id") == recipe_id:
            return r
    return None


def get_all_tags(recipes: list[dict]) -> dict[str, int]:
    """Get all unique tags with counts."""
    tags: dict[str, int] = {}
    for r in recipes:
        for tag in r.get("tags", []):
            tags[tag] = tags.get(tag, 0) + 1
    return dict(sorted(tags.items(), key=lambda x: (-x[1], x[0])))


def format_recipe_brief(recipe: dict) -> str:
    """Format a recipe as a brief one-liner."""
    return f"[{recipe['id']}] {recipe['title']} ({recipe['difficulty']})"


def format_recipe_summary(recipe: dict) -> str:
    """Format a recipe with more details."""
    lines = [
        f"Recipe {recipe['id']}: {recipe['title']}",
        f"  Topic: {recipe['topic']}",
        f"  Difficulty: {recipe['difficulty']}",
        f"  Tags: {', '.join(recipe.get('tags', [])) or 'none'}",
        f"  Code: {recipe.get('code_file', 'N/A')}",
    ]
    if recipe.get("see_also"):
        lines.append(f"  See Also: {', '.join(recipe['see_also'][:3])}")
    return "\n".join(lines)


def format_recipe_full(recipe: dict, recipes_dir: Path) -> str:
    """Format a recipe with full content from markdown file."""
    lines = [format_recipe_summary(recipe), ""]

    # Try to read the topic markdown file
    topic = recipe.get("topic", "")
    topic_file = recipes_dir / f"{topic}.md"

    if topic_file.exists():
        content = topic_file.read_text(encoding="utf-8")

        # Find the recipe section
        anchor = f"recipe-{recipe['id'].replace('.', '-')}"
        pattern = rf"## Recipe {re.escape(recipe['id'])}:.*?(?=\n## Recipe \d+\.\d+:|\n---\n*$|\Z)"
        match = re.search(pattern, content, re.DOTALL)

        if match:
            lines.append("--- Content ---")
            lines.append(match.group(0).strip())
        else:
            lines.append(f"(Full content in {topic_file.name})")
    else:
        lines.append(f"(Topic file not found: {topic}.md)")

    return "\n".join(lines)


def output_json(data: any) -> None:
    """Output data as JSON."""
    print(json.dumps(data, indent=2))


def main():
    parser = argparse.ArgumentParser(
        description="Search and filter cookbook recipes",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --topic data-structures
  %(prog)s --tag allocators --difficulty beginner
  %(prog)s --search "hash map"
  %(prog)s --recipe 1.1 --full
  %(prog)s --list-topics
  %(prog)s --list-tags
        """,
    )

    # Filter options
    parser.add_argument(
        "--topic", "-t",
        help="Filter by topic (e.g., 'memory-allocators', 'data-structures')",
    )
    parser.add_argument(
        "--tag", "-g",
        help="Filter by tag (e.g., 'allocators', 'hashmap')",
    )
    parser.add_argument(
        "--difficulty", "-d",
        choices=["beginner", "intermediate", "advanced"],
        help="Filter by difficulty level",
    )
    parser.add_argument(
        "--search", "-s",
        help="Search in title and tags",
    )
    parser.add_argument(
        "--recipe", "-r",
        help="Get specific recipe by ID (e.g., '1.1')",
    )

    # List options
    parser.add_argument(
        "--list-topics",
        action="store_true",
        help="List all available topics",
    )
    parser.add_argument(
        "--list-tags",
        action="store_true",
        help="List all available tags with counts",
    )

    # Output options
    parser.add_argument(
        "--full", "-f",
        action="store_true",
        help="Show full recipe content (use with --recipe)",
    )
    parser.add_argument(
        "--json", "-j",
        action="store_true",
        help="Output as JSON",
    )
    parser.add_argument(
        "--brief", "-b",
        action="store_true",
        help="Show brief one-line output",
    )

    # Path option
    parser.add_argument(
        "--recipes-dir",
        type=Path,
        default=Path(__file__).parent.parent / "recipes",
        help="Path to recipes directory",
    )

    args = parser.parse_args()

    recipes_dir = args.recipes_dir.resolve()
    index = load_index(recipes_dir)
    recipes = index.get("recipes", [])

    # Handle list commands
    if args.list_topics:
        topic_info = index.get("topic_info", {})
        if args.json:
            output_json(topic_info)
        else:
            print("Available Topics:")
            for topic, info in sorted(topic_info.items(), key=lambda x: x[1].get("count", 0), reverse=True):
                print(f"  {topic}: {info.get('name', topic)} ({info.get('count', 0)} recipes)")
        return

    if args.list_tags:
        tags = get_all_tags(recipes)
        if args.json:
            output_json(tags)
        else:
            print("Available Tags (sorted by frequency):")
            for tag, count in tags.items():
                print(f"  {tag}: {count}")
        return

    # Handle specific recipe lookup
    if args.recipe:
        recipe = filter_by_id(recipes, args.recipe)
        if not recipe:
            print(f"Recipe '{args.recipe}' not found")
            sys.exit(1)

        if args.json:
            output_json(recipe)
        elif args.full:
            print(format_recipe_full(recipe, recipes_dir))
        else:
            print(format_recipe_summary(recipe))
        return

    # Apply filters
    results = recipes

    if args.topic:
        results = filter_by_topic(results, args.topic)

    if args.tag:
        results = filter_by_tag(results, args.tag)

    if args.difficulty:
        results = filter_by_difficulty(results, args.difficulty)

    if args.search:
        results = filter_by_search(results, args.search)

    # Output results
    if not results:
        print("No recipes found matching criteria")
        sys.exit(0)

    if args.json:
        output_json(results)
    elif args.brief:
        for r in results:
            print(format_recipe_brief(r))
    else:
        print(f"Found {len(results)} recipe(s):\n")
        for r in results:
            print(format_recipe_summary(r))
            print()


if __name__ == "__main__":
    main()
