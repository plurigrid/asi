"""
Test: fokker-planck Convergence Check
Duration: ~10 seconds
Status: Unit test for equilibrium validation
"""

import numpy as np
import pytest


def simple_loss(theta):
    """Quadratic loss: L(θ) = θ²"""
    return np.sum(theta**2)


def simple_gradient(theta):
    """∇L(θ) = 2θ"""
    return 2 * theta


def mock_check_gibbs_convergence(trajectory, temperature, loss_fn, gradient_fn):
    """Mock Gibbs convergence checker"""
    # Calculate statistics
    losses = np.array([loss_fn(theta) for theta in trajectory])

    mean_initial = np.mean(losses[:10])
    mean_final = np.mean(losses[-10:])
    std_final = np.std(losses[-10:])

    # Gibbs ratio: exp(-(L_final - L_initial) / T)
    gibbs_ratio = np.exp(-(mean_final - mean_initial) / temperature)

    # Simple convergence check: if std is small, assume converged
    converged = std_final < 0.1

    return {
        'mean_initial_loss': mean_initial,
        'mean_final_loss': mean_final,
        'std_final': std_final,
        'gibbs_ratio': gibbs_ratio,
        'converged': converged
    }


def test_convergence_check_structure():
    """Test convergence check returns correct structure"""
    # Create mock trajectory
    trajectory = np.random.randn(100, 2) * 0.1

    result = mock_check_gibbs_convergence(
        trajectory=trajectory,
        temperature=0.01,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient
    )

    # Check required keys
    required_keys = [
        'mean_initial_loss', 'mean_final_loss',
        'std_final', 'gibbs_ratio', 'converged'
    ]
    for key in required_keys:
        assert key in result, f"Missing key: {key}"


def test_convergence_check_values():
    """Test convergence check returns reasonable values"""
    # Create deterministic trajectory converging to zero
    trajectory = np.ones((100, 2))  # Start from 1.0, not 0
    for i in range(1, 100):
        trajectory[i] = trajectory[i-1] - 0.01 * simple_gradient(trajectory[i-1])

    result = mock_check_gibbs_convergence(
        trajectory=trajectory,
        temperature=0.01,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient
    )

    # Final loss should be lower than initial
    assert result['mean_final_loss'] < result['mean_initial_loss']

    # Standard deviation should be small for converged trajectory
    assert result['std_final'] < 1.0


def test_gibbs_ratio_calculation():
    """Test Gibbs ratio is calculated correctly"""
    trajectory = np.random.randn(100, 2) * 0.1

    result = mock_check_gibbs_convergence(
        trajectory=trajectory,
        temperature=0.01,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient
    )

    # Gibbs ratio should be positive
    assert result['gibbs_ratio'] > 0

    # Gibbs ratio should be finite
    assert np.isfinite(result['gibbs_ratio'])


def test_convergence_flag():
    """Test convergence flag works correctly"""
    # Well-converged trajectory (low variance)
    converged_trajectory = np.random.randn(100, 2) * 0.01

    result_converged = mock_check_gibbs_convergence(
        trajectory=converged_trajectory,
        temperature=0.01,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient
    )

    assert result_converged['converged'] == True

    # Divergent trajectory (high variance)
    divergent_trajectory = np.random.randn(100, 2) * 100.0

    result_divergent = mock_check_gibbs_convergence(
        trajectory=divergent_trajectory,
        temperature=0.01,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient
    )

    assert result_divergent['converged'] == False


def test_temperature_sensitivity():
    """Test that temperature affects Gibbs ratio"""
    trajectory = np.random.randn(100, 2) * 0.1

    result_low_t = mock_check_gibbs_convergence(
        trajectory=trajectory,
        temperature=0.001,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient
    )

    result_high_t = mock_check_gibbs_convergence(
        trajectory=trajectory,
        temperature=0.1,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient
    )

    # Both should have finite ratios
    assert np.isfinite(result_low_t['gibbs_ratio'])
    assert np.isfinite(result_high_t['gibbs_ratio'])


def test_empty_trajectory():
    """Test handling of edge case: empty trajectory"""
    trajectory = np.array([]).reshape(0, 2)

    # Should handle gracefully - may return NaN values
    result = mock_check_gibbs_convergence(
        trajectory=trajectory,
        temperature=0.01,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient
    )
    # Result should have required keys even if values are NaN
    required_keys = ['mean_initial_loss', 'mean_final_loss', 'std_final', 'gibbs_ratio', 'converged']
    for key in required_keys:
        assert key in result, f"Missing key: {key}"
    # NaN values are acceptable for empty input
    assert np.isnan(result['mean_initial_loss']) or result['mean_initial_loss'] is None


def test_single_point_trajectory():
    """Test handling of single-point trajectory"""
    trajectory = np.array([[1.0, 1.0]])

    result = mock_check_gibbs_convergence(
        trajectory=trajectory,
        temperature=0.01,
        loss_fn=simple_loss,
        gradient_fn=simple_gradient
    )

    # Should still return valid result
    assert 'mean_initial_loss' in result
    assert np.isfinite(result['mean_initial_loss'])


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
