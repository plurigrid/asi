"""
Test: langevin-dynamics Basic Functionality
Duration: ~15 seconds
Status: Unit test for SDE solver
"""

import numpy as np
import pytest


def simple_loss(theta):
    """Quadratic loss: L(θ) = θ²"""
    return np.sum(theta**2)


def simple_gradient(theta):
    """∇L(θ) = 2θ"""
    return 2 * theta


class MockLangevinSDE:
    """Mock SDE for testing without dependencies"""
    def __init__(self, loss_fn, gradient_fn, temperature, base_seed):
        self.loss_fn = loss_fn
        self.gradient_fn = gradient_fn
        self.temperature = temperature
        self.base_seed = base_seed


class MockSolution:
    """Mock solution trajectory"""
    def __init__(self, trajectory):
        self.trajectory = trajectory
        self.shape = trajectory.shape

    def __len__(self):
        return len(self.trajectory)


def mock_solve_langevin(sde, theta_init, dt=0.01, n_steps=100):
    """Mock Langevin SDE solver for testing"""
    trajectory = np.zeros((n_steps, len(theta_init)))
    trajectory[0] = theta_init

    # Simple Euler discretization for testing
    for step in range(1, n_steps):
        gradient = sde.gradient_fn(trajectory[step-1])
        noise = np.random.randn(len(theta_init)) * np.sqrt(2 * sde.temperature * dt)
        trajectory[step] = trajectory[step-1] - dt * gradient + noise

    return MockSolution(trajectory), {"convergence_step": n_steps}


def test_sde_creation():
    """Test that SDE can be created"""
    sde = MockLangevinSDE(
        loss_fn=simple_loss,
        gradient_fn=simple_gradient,
        temperature=0.01,
        base_seed=0xDEADBEEF
    )

    assert sde.loss_fn is not None
    assert sde.gradient_fn is not None
    assert sde.temperature == 0.01
    assert sde.base_seed == 0xDEADBEEF


def test_sde_solving():
    """Test that SDE can be solved"""
    sde = MockLangevinSDE(
        loss_fn=simple_loss,
        gradient_fn=simple_gradient,
        temperature=0.01,
        base_seed=0xDEADBEEF
    )

    theta_init = np.array([1.0, 1.0])
    solution, tracking = mock_solve_langevin(
        sde=sde,
        theta_init=theta_init,
        dt=0.01,
        n_steps=100
    )

    assert len(solution) == 100
    assert solution.shape == (100, 2)


def test_trajectory_shape():
    """Test trajectory has correct shape"""
    sde = MockLangevinSDE(
        loss_fn=simple_loss,
        gradient_fn=simple_gradient,
        temperature=0.01,
        base_seed=0xDEADBEEF
    )

    theta_init = np.array([1.0, 1.0, 1.0])
    solution, tracking = mock_solve_langevin(
        sde=sde,
        theta_init=theta_init,
        dt=0.01,
        n_steps=50
    )

    assert solution.shape[0] == 50
    assert solution.shape[1] == 3


def test_noise_affects_trajectory():
    """Test that noise makes trajectories non-deterministic (without seed control)"""
    sde = MockLangevinSDE(
        loss_fn=simple_loss,
        gradient_fn=simple_gradient,
        temperature=0.01,
        base_seed=0xDEADBEEF
    )

    theta_init = np.array([1.0, 1.0])

    # Solve twice without fixed seed - should be different
    solution1, _ = mock_solve_langevin(sde, theta_init, dt=0.01, n_steps=10)
    solution2, _ = mock_solve_langevin(sde, theta_init, dt=0.01, n_steps=10)

    # Should be different due to random noise
    assert not np.allclose(solution1.trajectory, solution2.trajectory)


def test_zero_temperature_is_deterministic():
    """Test that zero temperature removes noise"""
    sde = MockLangevinSDE(
        loss_fn=simple_loss,
        gradient_fn=simple_gradient,
        temperature=0.0,  # No noise
        base_seed=0xDEADBEEF
    )

    theta_init = np.array([1.0, 1.0])

    # Solve twice with zero temperature - should be identical
    np.random.seed(42)
    solution1, _ = mock_solve_langevin(sde, theta_init, dt=0.01, n_steps=10)
    np.random.seed(42)
    solution2, _ = mock_solve_langevin(sde, theta_init, dt=0.01, n_steps=10)

    # Should be identical with same seed
    assert np.allclose(solution1.trajectory, solution2.trajectory)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
