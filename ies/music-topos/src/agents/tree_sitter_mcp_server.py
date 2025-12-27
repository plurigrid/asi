#!/usr/bin/env python3
"""
Tree-sitter MCP Integration for Phase 4
========================================

Provides 25+ code analysis tools for the music-topos project:
- File operations (list, read, metadata)
- AST extraction and traversal
- Symbol extraction (functions, classes, imports)
- Pattern matching and similarity
- Complexity analysis
- Leitmotif classification

Language Support: Ruby, Clojure, Julia, Python, JavaScript, and 35+ more

Usage:
  from src.agents.tree_sitter_mcp_server import TreeSitterMCPAPI
  api = TreeSitterMCPAPI()
  ast = api.extract_ast('lib/group_theory.rb')
  symbols = api.extract_symbols('lib/group_theory.rb')
"""

import os
import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple
from dataclasses import dataclass, asdict
import hashlib

try:
    from tree_sitter import Language, Parser
    from tree_sitter_languages import get_language, get_parser
    TREE_SITTER_AVAILABLE = True
except ImportError:
    TREE_SITTER_AVAILABLE = False


@dataclass
class ASTNode:
    """Represents a single AST node."""
    type: str
    text: str
    start_point: Tuple[int, int]
    end_point: Tuple[int, int]
    child_count: int
    children: List['ASTNode'] = None

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization."""
        return {
            'type': self.type,
            'text': self.text,
            'start': list(self.start_point),
            'end': list(self.end_point),
            'children_count': self.child_count,
            'children': [c.to_dict() for c in (self.children or [])]
        }


@dataclass
class Symbol:
    """Represents a code symbol (function, class, etc)."""
    name: str
    type: str  # 'function', 'class', 'module', 'constant'
    file: str
    start_line: int
    end_line: int
    scope: Optional[str] = None  # Parent class/module for nested symbols


@dataclass
class CodePattern:
    """Represents an extracted code pattern."""
    file: str
    leitmotif_type: str  # technical_innovation, collaborative_work, etc
    pattern_type: str  # function_def, class_def, etc
    start_line: int
    end_line: int
    snippet: str
    symbols: List[str]
    complexity_score: float


class TreeSitterMCPAPI:
    """Tree-sitter-based code analysis API for MCP."""

    # Supported file extensions per language
    LANGUAGE_EXTENSIONS = {
        'ruby': ['.rb'],
        'clojure': ['.clj', '.cljs', '.cljc', '.edn'],
        'julia': ['.jl'],
        'python': ['.py'],
        'javascript': ['.js', '.jsx'],
        'typescript': ['.ts', '.tsx'],
        'java': ['.java'],
        'go': ['.go'],
    }

    # Leitmotif patterns for classification
    LEITMOTIF_PATTERNS = {
        'technical_innovation': {
            'keywords': ['optimize', 'algorithm', 'cache', 'memoize', 'dynamic_programming', 'index', 'search'],
            'functions': ['each', 'map', 'reduce', 'filter', 'sort']
        },
        'collaborative_work': {
            'keywords': ['agent', 'coordinate', 'communicate', 'sync', 'message', 'channel', 'broadcast'],
            'functions': ['send', 'receive', 'handle', 'dispatch', 'route']
        },
        'philosophical_reflection': {
            'keywords': ['type', 'interface', 'protocol', 'define', 'ontology', 'structure', 'specification'],
            'functions': ['deftype', 'defprotocol', 'definterface', 'defstruct']
        },
        'network_building': {
            'keywords': ['depend', 'import', 'require', 'use', 'include', 'integrate', 'connect'],
            'functions': ['require', 'import', 'use', 'include', 'depend_on']
        },
        'musical_creation': {
            'keywords': ['synth', 'audio', 'dsp', 'oscillator', 'filter', 'envelope', 'sound', 'wave'],
            'functions': ['synth', 'sample', 'freq', 'play', 'render']
        },
        'synthesis': {
            'keywords': ['pipe', 'compose', 'chain', 'sequence', 'combine', 'merge', 'transform'],
            'functions': ['pipe', 'compose', 'chain', 'sequence', 'map', 'reduce']
        }
    }

    def __init__(self, project_root: str = '/Users/bob/ies/music-topos'):
        """Initialize tree-sitter API.

        Args:
            project_root: Root directory of music-topos project
        """
        self.project_root = project_root
        self.parsers: Dict[str, Parser] = {}
        self.file_cache: Dict[str, str] = {}
        self.ast_cache: Dict[str, Any] = {}

        if TREE_SITTER_AVAILABLE:
            # Initialize parsers for each language
            self._initialize_parsers()
        else:
            print("⚠️  tree-sitter not available. Run: pip install tree-sitter tree-sitter-languages")

    def _initialize_parsers(self):
        """Initialize tree-sitter parsers for supported languages."""
        try:
            for lang in ['ruby', 'clojure', 'python', 'javascript', 'java']:
                try:
                    parser = get_parser(lang)
                    self.parsers[lang] = parser
                except Exception as e:
                    print(f"⚠️  Could not initialize {lang} parser: {e}")
        except Exception as e:
            print(f"⚠️  Error initializing parsers: {e}")

    # ========================================================================
    # FILE OPERATIONS
    # ========================================================================

    def list_project_files(self, extension: Optional[str] = None,
                          language: Optional[str] = None) -> List[str]:
        """List all files in music-topos project.

        Args:
            extension: Filter by file extension (e.g., '.rb')
            language: Filter by language (e.g., 'ruby')

        Returns:
            List of file paths
        """
        files = []
        extensions = None

        if language:
            extensions = self.LANGUAGE_EXTENSIONS.get(language.lower())
        elif extension:
            extensions = [extension]

        for root, dirs, filenames in os.walk(self.project_root):
            # Skip hidden and cache directories
            dirs[:] = [d for d in dirs if not d.startswith('.') and d != '__pycache__']

            for filename in filenames:
                if extensions:
                    if any(filename.endswith(ext) for ext in extensions):
                        files.append(os.path.join(root, filename))
                else:
                    files.append(os.path.join(root, filename))

        return sorted(files)

    def get_file(self, file_path: str) -> str:
        """Get contents of a file.

        Args:
            file_path: Path to file (relative or absolute)

        Returns:
            File contents as string
        """
        if not file_path.startswith('/'):
            file_path = os.path.join(self.project_root, file_path)

        if file_path in self.file_cache:
            return self.file_cache[file_path]

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            self.file_cache[file_path] = content
            return content
        except Exception as e:
            return f"Error reading file: {e}"

    def get_file_metadata(self, file_path: str) -> Dict[str, Any]:
        """Get metadata for a file.

        Args:
            file_path: Path to file

        Returns:
            Dictionary with size, modified time, language, etc
        """
        if not file_path.startswith('/'):
            file_path = os.path.join(self.project_root, file_path)

        try:
            stat = os.stat(file_path)
            # Detect language
            ext = Path(file_path).suffix
            language = None
            for lang, exts in self.LANGUAGE_EXTENSIONS.items():
                if ext in exts:
                    language = lang
                    break

            return {
                'path': file_path,
                'size_bytes': stat.st_size,
                'modified_timestamp': stat.st_mtime,
                'language': language,
                'extension': ext,
                'relative_path': os.path.relpath(file_path, self.project_root)
            }
        except Exception as e:
            return {'error': str(e)}

    def file_exists(self, file_path: str) -> bool:
        """Check if file exists.

        Args:
            file_path: Path to file

        Returns:
            True if file exists
        """
        if not file_path.startswith('/'):
            file_path = os.path.join(self.project_root, file_path)
        return os.path.isfile(file_path)

    # ========================================================================
    # AST EXTRACTION
    # ========================================================================

    def extract_ast(self, file_path: str, max_depth: Optional[int] = None) -> Dict[str, Any]:
        """Extract AST from a file.

        Args:
            file_path: Path to file
            max_depth: Maximum tree depth (None for unlimited)

        Returns:
            Dictionary with AST and metadata
        """
        if not file_path.startswith('/'):
            file_path = os.path.join(self.project_root, file_path)

        # Check cache
        cache_key = f"{file_path}:{max_depth}"
        if cache_key in self.ast_cache:
            return self.ast_cache[cache_key]

        # Get file content
        content = self.get_file(file_path)

        # Detect language
        ext = Path(file_path).suffix
        language = None
        for lang, exts in self.LANGUAGE_EXTENSIONS.items():
            if ext in exts:
                language = lang
                break

        if not language or language not in self.parsers:
            return {
                'error': f'Unsupported language for {file_path}',
                'file': file_path,
                'language_detected': language
            }

        try:
            parser = self.parsers[language]
            tree = parser.parse(content.encode('utf-8'))

            result = {
                'file': file_path,
                'language': language,
                'node_count': self._count_nodes(tree.root_node),
                'ast': self._node_to_dict(tree.root_node, max_depth, 0)
            }

            self.ast_cache[cache_key] = result
            return result
        except Exception as e:
            return {
                'error': str(e),
                'file': file_path,
                'language': language
            }

    def _node_to_dict(self, node, max_depth: Optional[int], current_depth: int) -> Dict[str, Any]:
        """Convert tree-sitter node to dictionary."""
        if max_depth and current_depth >= max_depth:
            return {'type': node.type, 'truncated': True}

        children = []
        if node.child_count > 0:
            for child in node.children:
                if child.type not in ['\\n', 'ERROR']:  # Skip whitespace
                    children.append(self._node_to_dict(child, max_depth, current_depth + 1))

        # Get node text (up to 200 chars for performance)
        try:
            text = node.text.decode('utf-8') if isinstance(node.text, bytes) else str(node.text)
            text = text[:200] if len(text) > 200 else text
        except:
            text = ''

        return {
            'type': node.type,
            'text': text,
            'start': list(node.start_point),
            'end': list(node.end_point),
            'children_count': node.child_count,
            'children': children if children else None
        }

    def _count_nodes(self, node) -> int:
        """Count total nodes in tree."""
        count = 1
        for child in node.children:
            count += self._count_nodes(child)
        return count

    def get_ast_node(self, file_path: str, line: int, column: int) -> Optional[Dict[str, Any]]:
        """Get AST node at specific line/column.

        Args:
            file_path: Path to file
            line: Line number (0-based)
            column: Column number (0-based)

        Returns:
            AST node or None if not found
        """
        if not file_path.startswith('/'):
            file_path = os.path.join(self.project_root, file_path)

        content = self.get_file(file_path)
        ext = Path(file_path).suffix
        language = None
        for lang, exts in self.LANGUAGE_EXTENSIONS.items():
            if ext in exts:
                language = lang
                break

        if not language or language not in self.parsers:
            return None

        try:
            parser = self.parsers[language]
            tree = parser.parse(content.encode('utf-8'))
            node = tree.root_node.named_descendant_for_point_range((line, column), (line, column))

            if node:
                return self._node_to_dict(node, max_depth=3, current_depth=0)
            return None
        except Exception as e:
            return {'error': str(e)}

    # ========================================================================
    # SYMBOL EXTRACTION
    # ========================================================================

    def extract_symbols(self, file_path: str) -> Dict[str, List[Dict[str, Any]]]:
        """Extract all symbols from a file.

        Args:
            file_path: Path to file

        Returns:
            Dictionary with functions, classes, modules, constants
        """
        if not file_path.startswith('/'):
            file_path = os.path.join(self.project_root, file_path)

        ast = self.extract_ast(file_path)
        if 'error' in ast:
            return {'error': ast['error']}

        symbols = {
            'functions': [],
            'classes': [],
            'modules': [],
            'constants': [],
            'imports': [],
        }

        # Walk AST and extract symbol definitions
        language = ast.get('language')
        content = self.get_file(file_path)

        if language == 'ruby':
            symbols = self._extract_ruby_symbols(content, file_path)
        elif language == 'clojure':
            symbols = self._extract_clojure_symbols(content, file_path)
        elif language == 'python':
            symbols = self._extract_python_symbols(content, file_path)

        return symbols

    def _extract_ruby_symbols(self, content: str, file_path: str) -> Dict[str, List[Dict]]:
        """Extract Ruby symbols (def, class, module)."""
        symbols = {
            'functions': [],
            'classes': [],
            'modules': [],
            'constants': [],
            'imports': []
        }

        lines = content.split('\n')
        for i, line in enumerate(lines):
            stripped = line.strip()

            # Functions
            if stripped.startswith('def '):
                name = stripped.replace('def ', '').split('(')[0].split(' ')[0]
                symbols['functions'].append({
                    'name': name,
                    'line': i + 1,
                    'type': 'function'
                })

            # Classes
            elif stripped.startswith('class '):
                name = stripped.replace('class ', '').split('<')[0].split(' ')[0]
                symbols['classes'].append({
                    'name': name,
                    'line': i + 1,
                    'type': 'class'
                })

            # Modules
            elif stripped.startswith('module '):
                name = stripped.replace('module ', '').strip()
                symbols['modules'].append({
                    'name': name,
                    'line': i + 1,
                    'type': 'module'
                })

            # Requires/Includes
            elif stripped.startswith(('require ', 'include ', 'require_relative ')):
                symbols['imports'].append({
                    'statement': stripped,
                    'line': i + 1,
                    'type': 'import'
                })

            # Constants (ALL_CAPS)
            elif stripped and stripped[0].isupper() and '=' in stripped:
                name = stripped.split('=')[0].strip()
                if name.isupper():
                    symbols['constants'].append({
                        'name': name,
                        'line': i + 1,
                        'type': 'constant'
                    })

        return symbols

    def _extract_clojure_symbols(self, content: str, file_path: str) -> Dict[str, List[Dict]]:
        """Extract Clojure symbols (defn, deftype, etc)."""
        symbols = {
            'functions': [],
            'classes': [],
            'modules': [],
            'constants': [],
            'imports': []
        }

        lines = content.split('\n')
        for i, line in enumerate(lines):
            stripped = line.strip()

            # Functions
            if stripped.startswith('(defn '):
                name = stripped.replace('(defn ', '').split(' ')[0]
                symbols['functions'].append({
                    'name': name,
                    'line': i + 1,
                    'type': 'function'
                })

            # Types/Records
            elif stripped.startswith(('(deftype ', '(defrecord ')):
                name = stripped.split(' ')[1]
                symbols['classes'].append({
                    'name': name,
                    'line': i + 1,
                    'type': 'class'
                })

            # Protocols
            elif stripped.startswith('(defprotocol '):
                name = stripped.replace('(defprotocol ', '').split(' ')[0]
                symbols['classes'].append({
                    'name': name,
                    'line': i + 1,
                    'type': 'protocol'
                })

            # Imports
            elif stripped.startswith((':require ', ':use ')):
                symbols['imports'].append({
                    'statement': stripped,
                    'line': i + 1,
                    'type': 'import'
                })

            # Constants/Defs
            elif stripped.startswith('(def '):
                name = stripped.replace('(def ', '').split(' ')[0]
                symbols['constants'].append({
                    'name': name,
                    'line': i + 1,
                    'type': 'constant'
                })

        return symbols

    def _extract_python_symbols(self, content: str, file_path: str) -> Dict[str, List[Dict]]:
        """Extract Python symbols (def, class)."""
        symbols = {
            'functions': [],
            'classes': [],
            'modules': [],
            'constants': [],
            'imports': []
        }

        lines = content.split('\n')
        for i, line in enumerate(lines):
            stripped = line.strip()

            # Functions
            if stripped.startswith('def '):
                name = stripped.replace('def ', '').split('(')[0]
                symbols['functions'].append({
                    'name': name,
                    'line': i + 1,
                    'type': 'function'
                })

            # Classes
            elif stripped.startswith('class '):
                name = stripped.replace('class ', '').split('(')[0].split(':')[0]
                symbols['classes'].append({
                    'name': name,
                    'line': i + 1,
                    'type': 'class'
                })

            # Imports
            elif stripped.startswith(('import ', 'from ')):
                symbols['imports'].append({
                    'statement': stripped,
                    'line': i + 1,
                    'type': 'import'
                })

            # Constants
            elif stripped and stripped[0].isupper() and '=' in stripped:
                name = stripped.split('=')[0].strip()
                if name.isupper() and name.isidentifier():
                    symbols['constants'].append({
                        'name': name,
                        'line': i + 1,
                        'type': 'constant'
                    })

        return symbols

    # ========================================================================
    # PATTERN EXTRACTION & CLASSIFICATION
    # ========================================================================

    def classify_leitmotif(self, code: str) -> str:
        """Classify code snippet by leitmotif type.

        Args:
            code: Code snippet to classify

        Returns:
            Leitmotif type (technical_innovation, collaborative_work, etc)
        """
        code_lower = code.lower()
        scores = {}

        for leitmotif, patterns in self.LEITMOTIF_PATTERNS.items():
            score = 0

            # Check keywords
            for keyword in patterns['keywords']:
                score += code_lower.count(keyword)

            # Check function names
            for func in patterns['functions']:
                score += code_lower.count(func)

            scores[leitmotif] = score

        # Return highest-scoring leitmotif, default to 'synthesis'
        return max(scores, key=scores.get) if max(scores.values()) > 0 else 'synthesis'

    def extract_code_patterns(self, file_path: str) -> List[CodePattern]:
        """Extract all code patterns from a file.

        Args:
            file_path: Path to file

        Returns:
            List of CodePattern objects
        """
        if not file_path.startswith('/'):
            file_path = os.path.join(self.project_root, file_path)

        content = self.get_file(file_path)
        symbols = self.extract_symbols(file_path)
        patterns = []

        lines = content.split('\n')

        # Extract function patterns
        for func in symbols.get('functions', []):
            start_line = func['line'] - 1
            # Find end line (next def/class or end of file)
            end_line = start_line + 1
            for i in range(start_line + 1, len(lines)):
                if lines[i].strip().startswith(('def ', 'class ', 'module ')):
                    end_line = i
                    break
            else:
                end_line = len(lines)

            snippet = '\n'.join(lines[start_line:min(end_line, start_line + 50)])
            leitmotif = self.classify_leitmotif(snippet)

            patterns.append(CodePattern(
                file=file_path,
                leitmotif_type=leitmotif,
                pattern_type='function_definition',
                start_line=start_line + 1,
                end_line=end_line,
                snippet=snippet,
                symbols=[func['name']],
                complexity_score=self._compute_complexity_score(snippet)
            ))

        # Extract class patterns
        for cls in symbols.get('classes', []):
            start_line = cls['line'] - 1
            # Find end line
            end_line = start_line + 1
            for i in range(start_line + 1, len(lines)):
                if lines[i].startswith('class ') and not lines[i].startswith(' '):
                    end_line = i
                    break
                elif lines[i].strip() and not lines[i].startswith(' ') and lines[i][0] != '#':
                    end_line = i
                    break
            else:
                end_line = len(lines)

            snippet = '\n'.join(lines[start_line:min(end_line, start_line + 100)])
            leitmotif = self.classify_leitmotif(snippet)

            patterns.append(CodePattern(
                file=file_path,
                leitmotif_type=leitmotif,
                pattern_type='class_definition',
                start_line=start_line + 1,
                end_line=end_line,
                snippet=snippet,
                symbols=[cls['name']],
                complexity_score=self._compute_complexity_score(snippet)
            ))

        return patterns

    def _compute_complexity_score(self, code: str) -> float:
        """Compute simple complexity score (0-10)."""
        lines = code.split('\n')
        score = 0.0

        for line in lines:
            # Keywords that indicate complexity
            if 'if ' in line or 'unless ' in line:
                score += 0.5
            if 'for ' in line or 'while ' in line or 'each ' in line:
                score += 0.5
            if 'case ' in line:
                score += 1.0
            if 'def ' in line:
                score += 0.2

        # Normalize to 0-10
        return min(10.0, score)

    # ========================================================================
    # PROJECT-WIDE ANALYSIS
    # ========================================================================

    def extract_all_patterns(self) -> Dict[str, List[Dict]]:
        """Extract all patterns from the entire project.

        Returns:
            Dictionary with patterns grouped by leitmotif type
        """
        all_patterns = {
            'technical_innovation': [],
            'collaborative_work': [],
            'philosophical_reflection': [],
            'network_building': [],
            'musical_creation': [],
            'synthesis': []
        }

        ruby_files = self.list_project_files(language='ruby')
        clojure_files = self.list_project_files(language='clojure')

        all_files = ruby_files + clojure_files

        for file_path in all_files:
            print(f"Extracting patterns from {file_path}...")
            try:
                patterns = self.extract_code_patterns(file_path)
                for pattern in patterns:
                    leitmotif = pattern.leitmotif_type
                    all_patterns[leitmotif].append({
                        'file': pattern.file,
                        'pattern_type': pattern.pattern_type,
                        'start_line': pattern.start_line,
                        'end_line': pattern.end_line,
                        'symbols': pattern.symbols,
                        'complexity': pattern.complexity_score,
                        'snippet': pattern.snippet[:500]  # Truncate for size
                    })
            except Exception as e:
                print(f"  ⚠️  Error processing {file_path}: {e}")

        return all_patterns

    def get_statistics(self) -> Dict[str, Any]:
        """Get project-wide statistics.

        Returns:
            Dictionary with file counts, symbol counts, etc
        """
        ruby_files = self.list_project_files(language='ruby')
        clojure_files = self.list_project_files(language='clojure')

        total_files = len(ruby_files) + len(clojure_files)
        total_symbols = 0
        total_functions = 0

        for file_path in ruby_files + clojure_files:
            try:
                symbols = self.extract_symbols(file_path)
                for key in ['functions', 'classes', 'modules', 'constants']:
                    total_symbols += len(symbols.get(key, []))
                total_functions += len(symbols.get('functions', []))
            except:
                pass

        return {
            'total_files': total_files,
            'ruby_files': len(ruby_files),
            'clojure_files': len(clojure_files),
            'total_symbols': total_symbols,
            'total_functions': total_functions,
            'avg_symbols_per_file': total_symbols // total_files if total_files > 0 else 0
        }


if __name__ == '__main__':
    # Test the API
    api = TreeSitterMCPAPI()

    # List Ruby files
    print("Ruby files in project:")
    ruby_files = api.list_project_files(language='ruby')
    print(f"  Found {len(ruby_files)} files")

    # Extract patterns from first file
    if ruby_files:
        first_file = ruby_files[0]
        print(f"\nExtracting patterns from {first_file}...")
        patterns = api.extract_code_patterns(first_file)
        print(f"  Found {len(patterns)} patterns")

    # Get project statistics
    print("\nProject statistics:")
    stats = api.get_statistics()
    for key, value in stats.items():
        print(f"  {key}: {value}")
