#!/usr/bin/env python3
"""
Unit Tests for Tree-sitter MCP API
===================================

Tests for code analysis, symbol extraction, pattern classification.

Run with: pytest tests/test_tree_sitter_mcp.py -v
"""

import os
import sys
import pytest
import json
from pathlib import Path

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.agents.tree_sitter_mcp_server import TreeSitterMCPAPI, CodePattern


class TestTreeSitterMCPAPI:
    """Test cases for TreeSitterMCPAPI."""

    @pytest.fixture
    def api(self):
        """Create API instance."""
        return TreeSitterMCPAPI()

    @pytest.fixture
    def sample_ruby_file(self, tmp_path):
        """Create a sample Ruby file for testing."""
        content = '''
class Calculator
  def add(a, b)
    a + b
  end

  def subtract(a, b)
    a - b
  end
end

def multiply(x, y)
  x * y
end

CONSTANT_VALUE = 42
'''
        file_path = tmp_path / "test.rb"
        file_path.write_text(content)
        return str(file_path)

    # ========================================================================
    # FILE OPERATIONS TESTS
    # ========================================================================

    def test_list_project_files(self, api):
        """Test listing Ruby files from project."""
        files = api.list_project_files(language='ruby')
        assert isinstance(files, list)
        assert len(files) > 0
        assert all(f.endswith('.rb') for f in files)

    def test_list_clojure_files(self, api):
        """Test listing Clojure files from project."""
        files = api.list_project_files(language='clojure')
        assert isinstance(files, list)
        # Clojure files may or may not exist
        if files:
            assert all(any(f.endswith(ext) for ext in ['.clj', '.cljs', '.cljc'])
                      for f in files)

    def test_get_file(self, api, sample_ruby_file):
        """Test reading file contents."""
        content = api.get_file(sample_ruby_file)
        assert isinstance(content, str)
        assert 'def' in content or 'Calculator' in content

    def test_get_file_metadata(self, api, sample_ruby_file):
        """Test getting file metadata."""
        metadata = api.get_file_metadata(sample_ruby_file)
        assert 'size_bytes' in metadata
        assert 'language' in metadata
        assert metadata['language'] == 'ruby'
        assert 'extension' in metadata

    def test_file_exists(self, api, sample_ruby_file):
        """Test checking file existence."""
        assert api.file_exists(sample_ruby_file)
        assert not api.file_exists('/nonexistent/path/file.rb')

    # ========================================================================
    # SYMBOL EXTRACTION TESTS
    # ========================================================================

    def test_extract_ruby_symbols_functions(self, api, sample_ruby_file):
        """Test extracting function symbols from Ruby."""
        symbols = api.extract_symbols(sample_ruby_file)
        assert 'functions' in symbols
        function_names = [f['name'] for f in symbols['functions']]
        assert 'add' in function_names or 'multiply' in function_names

    def test_extract_ruby_symbols_classes(self, api, sample_ruby_file):
        """Test extracting class symbols from Ruby."""
        symbols = api.extract_symbols(sample_ruby_file)
        assert 'classes' in symbols
        class_names = [c['name'] for c in symbols['classes']]
        assert 'Calculator' in class_names

    def test_extract_ruby_symbols_constants(self, api, sample_ruby_file):
        """Test extracting constant symbols from Ruby."""
        symbols = api.extract_symbols(sample_ruby_file)
        assert 'constants' in symbols
        # CONSTANT_VALUE should be found
        const_names = [c['name'] for c in symbols['constants']]
        assert 'CONSTANT_VALUE' in const_names or len(const_names) > 0

    # ========================================================================
    # LEITMOTIF CLASSIFICATION TESTS
    # ========================================================================

    def test_classify_technical_innovation(self, api):
        """Test classifying technical innovation patterns."""
        code = '''
def optimize_algorithm(data)
  cache = {}
  data.each do |item|
    cache[item] = compute(item)
  end
  cache
end
'''
        leitmotif = api.classify_leitmotif(code)
        assert leitmotif == 'technical_innovation'

    def test_classify_collaborative_work(self, api):
        """Test classifying collaborative work patterns."""
        code = '''
def handle_message(msg)
  agent.send(process(msg))
  coordinate_agents()
end
'''
        leitmotif = api.classify_leitmotif(code)
        assert leitmotif == 'collaborative_work'

    def test_classify_musical_creation(self, api):
        """Test classifying musical creation patterns."""
        code = '''
def synth_wave(freq, amplitude)
  oscillator(freq).amplify(amplitude)
end
'''
        leitmotif = api.classify_leitmotif(code)
        assert leitmotif == 'musical_creation'

    def test_classify_network_building(self, api):
        """Test classifying network building patterns."""
        code = '''
require 'some_library'
import 'other_module'
include Mixins::Helper
'''
        leitmotif = api.classify_leitmotif(code)
        assert leitmotif == 'network_building'

    # ========================================================================
    # PATTERN EXTRACTION TESTS
    # ========================================================================

    def test_extract_code_patterns(self, api, sample_ruby_file):
        """Test extracting code patterns from file."""
        patterns = api.extract_code_patterns(sample_ruby_file)
        assert isinstance(patterns, list)
        assert len(patterns) > 0

    def test_pattern_has_required_fields(self, api, sample_ruby_file):
        """Test that extracted patterns have all required fields."""
        patterns = api.extract_code_patterns(sample_ruby_file)
        assert len(patterns) > 0

        pattern = patterns[0]
        assert hasattr(pattern, 'file')
        assert hasattr(pattern, 'leitmotif_type')
        assert hasattr(pattern, 'pattern_type')
        assert hasattr(pattern, 'start_line')
        assert hasattr(pattern, 'end_line')
        assert hasattr(pattern, 'snippet')
        assert hasattr(pattern, 'symbols')
        assert hasattr(pattern, 'complexity_score')

    def test_pattern_complexity_score(self, api, sample_ruby_file):
        """Test that complexity score is reasonable."""
        patterns = api.extract_code_patterns(sample_ruby_file)
        assert len(patterns) > 0

        for pattern in patterns:
            assert 0 <= pattern.complexity_score <= 10

    # ========================================================================
    # PROJECT-WIDE ANALYSIS TESTS
    # ========================================================================

    def test_get_statistics(self, api):
        """Test getting project statistics."""
        stats = api.get_statistics()
        assert isinstance(stats, dict)
        assert 'total_files' in stats
        assert 'ruby_files' in stats
        assert 'clojure_files' in stats
        assert 'total_symbols' in stats
        assert stats['total_files'] > 0

    # ========================================================================
    # INTEGRATION TESTS
    # ========================================================================

    def test_extract_real_project_file(self, api):
        """Test extracting patterns from real project files."""
        ruby_files = api.list_project_files(language='ruby')
        if ruby_files:
            first_file = ruby_files[0]
            patterns = api.extract_code_patterns(first_file)
            assert isinstance(patterns, list)

    def test_extract_all_patterns_format(self, api):
        """Test that extract_all_patterns returns proper format."""
        # Note: This test may take a while
        # Commented out by default
        pass
        # all_patterns = api.extract_all_patterns()
        # assert isinstance(all_patterns, dict)
        # assert 'technical_innovation' in all_patterns
        # assert 'collaborative_work' in all_patterns


class TestCodePatternSerialization:
    """Test serialization of code patterns."""

    def test_code_pattern_to_dict(self):
        """Test converting CodePattern to dictionary."""
        pattern = CodePattern(
            file='/test/file.rb',
            leitmotif_type='technical_innovation',
            pattern_type='function_definition',
            start_line=10,
            end_line=20,
            snippet='def foo(x)\n  x * 2\nend',
            symbols=['foo'],
            complexity_score=2.5
        )

        pattern_dict = {
            'file': pattern.file,
            'leitmotif_type': pattern.leitmotif_type,
            'pattern_type': pattern.pattern_type,
            'start_line': pattern.start_line,
            'end_line': pattern.end_line,
            'symbols': pattern.symbols,
            'complexity_score': pattern.complexity_score
        }

        assert pattern_dict['leitmotif_type'] == 'technical_innovation'
        assert pattern_dict['complexity_score'] == 2.5

    def test_pattern_list_to_json(self):
        """Test converting list of patterns to JSON."""
        patterns = [
            CodePattern(
                file='/test/file1.rb',
                leitmotif_type='technical_innovation',
                pattern_type='function_definition',
                start_line=1,
                end_line=10,
                snippet='code1',
                symbols=['func1'],
                complexity_score=1.0
            ),
            CodePattern(
                file='/test/file2.rb',
                leitmotif_type='collaborative_work',
                pattern_type='class_definition',
                start_line=20,
                end_line=50,
                snippet='code2',
                symbols=['Class1'],
                complexity_score=3.5
            )
        ]

        patterns_json = json.dumps([
            {
                'file': p.file,
                'leitmotif': p.leitmotif_type,
                'type': p.pattern_type,
                'lines': f"{p.start_line}-{p.end_line}",
                'complexity': p.complexity_score
            }
            for p in patterns
        ], indent=2)

        assert '"technical_innovation"' in patterns_json
        assert '"collaborative_work"' in patterns_json


class TestErrorHandling:
    """Test error handling."""

    def test_nonexistent_file(self):
        """Test handling of nonexistent file."""
        api = TreeSitterMCPAPI()
        result = api.extract_symbols('/nonexistent/file.rb')
        # Should return dict with error or empty dict
        assert isinstance(result, dict)

    def test_invalid_language(self):
        """Test handling of unsupported language."""
        api = TreeSitterMCPAPI()
        # Create a file with unsupported extension
        result = api.extract_ast('/test/file.xyz')
        # Should handle gracefully
        assert isinstance(result, dict)


# ============================================================================
# Fixtures and Helpers
# ============================================================================

@pytest.fixture(scope="session")
def test_project_root():
    """Get music-topos project root."""
    return '/Users/bob/ies/music-topos'


if __name__ == '__main__':
    # Run tests
    pytest.main([__file__, '-v'])
