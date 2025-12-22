"""
Pytest Configuration for Plurigrid ASI Skills Tests
"""

import pytest


def pytest_configure(config):
    """Configure pytest"""
    config.addinivalue_line(
        "markers", "unit: mark test as a unit test"
    )
    config.addinivalue_line(
        "markers", "integration: mark test as an integration test"
    )
    config.addinivalue_line(
        "markers", "gf3: mark test as a GF(3) conservation test"
    )
    config.addinivalue_line(
        "markers", "performance: mark test as a performance test"
    )


@pytest.fixture
def mock_genesis_seed():
    """Provide a fixed genesis seed for tests"""
    return 0xDEADBEEF


@pytest.fixture
def mock_trajectory():
    """Provide a mock trajectory"""
    import numpy as np
    return np.random.randn(100, 2) * 0.1


@pytest.fixture
def mock_patterns():
    """Provide mock patterns"""
    patterns = []
    for i in range(10):
        patterns.append({
            'index': i,
            'colors': [i % 3, (i + 1) % 3, (i + 2) % 3],
            'gf3_conserved': True
        })
    return patterns
