#!/usr/bin/env python3
"""KOS Robot Controller Quickstart

A minimal example of controlling a robot via KOS gRPC services.
Compatible with both real hardware and simulation backends.

GF(3) Triad: ksim-rl (-1) ⊗ kos-firmware (+1) ⊗ mujoco-scenes (0) = 0 ✓
"""

import asyncio
from dataclasses import dataclass
from typing import Optional

# Mock pykos for demo (replace with `from pykos import KosClient` when available)
@dataclass
class ActuatorCommand:
    actuator_id: int
    position: float
    velocity: Optional[float] = None
    torque: Optional[float] = None

class MockActuatorService:
    async def get_actuators_state(self, ids: list[int]) -> dict:
        return {
            "actuators": [
                {"id": i, "position": 0.0, "velocity": 0.0, "torque": 0.0}
                for i in ids
            ]
        }
    
    async def command_actuators(self, commands: list[dict]) -> dict:
        print(f"  → Commanding {len(commands)} actuators")
        for cmd in commands:
            print(f"    Actuator {cmd['actuator_id']}: pos={cmd['position']:.3f}")
        return {"success": True}
    
    async def configure_actuator(self, actuator_id: int, kp: float, kd: float, torque_enabled: bool) -> dict:
        print(f"  → Configured actuator {actuator_id}: kp={kp}, kd={kd}, enabled={torque_enabled}")
        return {"success": True}

class MockSimService:
    async def reset(self) -> dict:
        print("  → Simulation reset")
        return {"success": True}
    
    async def step(self, dt: float = 0.002) -> dict:
        print(f"  → Simulation step: dt={dt}s")
        return {"time": dt}

class MockKosClient:
    def __init__(self, address: str):
        self.address = address
        self.actuator = MockActuatorService()
        self.sim = MockSimService()
    
    async def __aenter__(self):
        print(f"Connected to KOS at {self.address}")
        return self
    
    async def __aexit__(self, *args):
        print("Disconnected from KOS")

# Use real client when available
try:
    from pykos import KosClient
except ImportError:
    KosClient = MockKosClient


# === Robot Configuration ===
ROBOT_CONFIG = {
    "name": "quickbot",
    "actuators": {
        "left_hip": {"id": 1, "kp": 100.0, "kd": 10.0},
        "left_knee": {"id": 2, "kp": 80.0, "kd": 8.0},
        "right_hip": {"id": 3, "kp": 100.0, "kd": 10.0},
        "right_knee": {"id": 4, "kp": 80.0, "kd": 8.0},
    },
}


async def configure_robot(client: KosClient) -> None:
    """Configure all actuators with PD gains."""
    print("\n[1] Configuring actuators...")
    for name, cfg in ROBOT_CONFIG["actuators"].items():
        await client.actuator.configure_actuator(
            actuator_id=cfg["id"],
            kp=cfg["kp"],
            kd=cfg["kd"],
            torque_enabled=True,
        )


async def stand_pose(client: KosClient) -> None:
    """Command robot to standing pose."""
    print("\n[2] Commanding stand pose...")
    await client.actuator.command_actuators([
        {"actuator_id": 1, "position": 0.0},   # left hip
        {"actuator_id": 2, "position": 0.3},   # left knee (slight bend)
        {"actuator_id": 3, "position": 0.0},   # right hip
        {"actuator_id": 4, "position": 0.3},   # right knee
    ])


async def simple_walk_step(client: KosClient, phase: float) -> None:
    """Execute one walking phase (simplified gait)."""
    import math
    
    # Simple sinusoidal gait
    left_hip = 0.2 * math.sin(phase)
    right_hip = 0.2 * math.sin(phase + math.pi)
    left_knee = 0.3 + 0.1 * abs(math.sin(phase))
    right_knee = 0.3 + 0.1 * abs(math.sin(phase + math.pi))
    
    await client.actuator.command_actuators([
        {"actuator_id": 1, "position": left_hip},
        {"actuator_id": 2, "position": left_knee},
        {"actuator_id": 3, "position": right_hip},
        {"actuator_id": 4, "position": right_knee},
    ])


async def run_simulation(client: KosClient, steps: int = 100) -> None:
    """Run a simple walking simulation."""
    print("\n[3] Running walk simulation...")
    await client.sim.reset()
    
    import math
    for i in range(steps):
        phase = (i / 50) * 2 * math.pi  # Complete cycle every 50 steps
        await simple_walk_step(client, phase)
        await client.sim.step(dt=0.002)
    
    print(f"  → Completed {steps} simulation steps")


async def main():
    print("=" * 50)
    print("KOS Robot Controller Quickstart")
    print("=" * 50)
    
    async with KosClient("localhost:50051") as client:
        # Configure
        await configure_robot(client)
        
        # Stand
        await stand_pose(client)
        
        # Walk (in simulation)
        await run_simulation(client, steps=10)
    
    print("\n✓ Done!")


if __name__ == "__main__":
    asyncio.run(main())
