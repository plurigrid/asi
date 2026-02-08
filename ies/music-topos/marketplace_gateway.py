#!/usr/bin/env python3
"""
Unified API Marketplace Gateway - ALPHA-BETA-GAMMA Integration

Integrates 11 applications:
- Market Maker: Liquidity/pricing queries
- Composer: Generate melody/harmony/rhythm
- Personalizer: Recommendations/user segmentation
- Consensus: Distributed state consensus
- Query Engine: Parallel batch processing
- Color Navigator: GF(3) color space exploration
- World Navigator: Possible world traversal
- Epistemology: Knowledge graph queries
- Active Inference: Free energy minimization
- Pattern Discovery: 5D pattern extraction
- Thread Analysis: Conversation graph analysis

Features:
- HTTP/WebSocket API
- Composition chains: (app1) → (app2) → (app3)
- Async execution with result caching
- API key authentication
- Rate limiting per application
- GF(3) conservation validation
- Audit logging

Usage:
    python marketplace_gateway.py --port 8080

API Examples:
    GET  /apps - List all applications
    POST /execute - Execute single app
    POST /compose - Multi-step composition chain
    GET  /results/{id} - Get async result
    WS   /stream - Real-time streaming
"""

import asyncio
import hashlib
import hmac
import json
import logging
import secrets
import time
from collections import defaultdict
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Callable
from uuid import uuid4

import aiohttp
from aiohttp import web
import numpy as np

# =============================================================================
# GF(3) VALIDATION & COLOR SYSTEM
# =============================================================================

class Trit(Enum):
    """GF(3) trit values"""
    MINUS = -1
    ZERO = 0
    PLUS = 1

def validate_gf3_conservation(data: Any) -> Tuple[bool, str]:
    """
    Validate GF(3) conservation in output data.
    Returns (is_valid, error_message).
    """
    try:
        if isinstance(data, dict):
            # Check if data has explicit GF(3) fields
            if "gf3_trits" in data:
                trits = data["gf3_trits"]
                if isinstance(trits, list):
                    total = sum(trits)
                    if total % 3 != 0:
                        return False, f"GF(3) conservation violated: sum={total} not divisible by 3"

            # Recursively check nested structures
            for value in data.values():
                valid, msg = validate_gf3_conservation(value)
                if not valid:
                    return False, msg

        elif isinstance(data, list):
            for item in data:
                valid, msg = validate_gf3_conservation(item)
                if not valid:
                    return False, msg

        return True, ""

    except Exception as e:
        return False, f"GF(3) validation error: {str(e)}"

def hash_to_gf3_trit(data: str, seed: int = 0) -> Trit:
    """Hash data to GF(3) trit deterministically"""
    h = hashlib.sha256(f"{data}:{seed}".encode()).digest()
    return Trit((int.from_bytes(h[:4], 'big') % 3) - 1)

# =============================================================================
# APPLICATION REGISTRY
# =============================================================================

@dataclass
class ApplicationSpec:
    """Specification for a registered application"""
    name: str
    description: str
    category: str  # "alpha", "beta", "gamma", "baseline"
    input_schema: Dict[str, Any]
    output_schema: Dict[str, Any]
    rate_limit: int  # requests per minute
    handler: Callable
    requires_auth: bool = True
    supports_streaming: bool = False
    gf3_validation: bool = True

@dataclass
class ExecutionResult:
    """Result from application execution"""
    id: str
    app_name: str
    status: str  # "pending", "running", "completed", "failed"
    input_data: Dict[str, Any]
    output_data: Optional[Dict[str, Any]] = None
    error: Optional[str] = None
    started_at: datetime = field(default_factory=datetime.now)
    completed_at: Optional[datetime] = None
    execution_time_ms: float = 0.0
    gf3_valid: bool = False

# =============================================================================
# APPLICATION HANDLERS
# =============================================================================

class MarketMakerApp:
    """Market Maker Application: Liquidity and pricing queries"""

    async def execute(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Execute market maker query"""
        query_type = params.get("query_type", "quote")
        asset = params.get("asset", "PROP")
        amount = params.get("amount", 1000.0)

        # Simulate market making logic
        await asyncio.sleep(0.1)  # Simulate computation

        if query_type == "quote":
            bid = 0.995 + (hash_to_gf3_trit(asset, 0).value * 0.001)
            ask = 1.005 + (hash_to_gf3_trit(asset, 1).value * 0.001)
            spread = ask - bid

            return {
                "asset": asset,
                "amount": amount,
                "bid": bid,
                "ask": ask,
                "spread": spread,
                "mid_price": (bid + ask) / 2,
                "liquidity_score": 0.85,
                "gf3_trits": [
                    hash_to_gf3_trit(asset, 0).value,
                    hash_to_gf3_trit(asset, 1).value,
                    hash_to_gf3_trit(asset, 2).value
                ]
            }

        elif query_type == "liquidity":
            return {
                "asset": asset,
                "available_liquidity": amount * 10,
                "depth_levels": 5,
                "total_volume_24h": amount * 100,
                "gf3_trits": [0, 0, 0]
            }

        else:
            raise ValueError(f"Unknown query_type: {query_type}")

class ComposerApp:
    """Composer Application: Generate melody, harmony, rhythm"""

    async def execute(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Execute music composition"""
        style = params.get("style", "classical")
        length = params.get("length", 8)  # measures
        key = params.get("key", "C")

        await asyncio.sleep(0.2)  # Simulate composition

        # Generate simple melody
        scales = {
            "C": [60, 62, 64, 65, 67, 69, 71, 72],  # C major
            "Am": [69, 71, 72, 74, 76, 77, 79, 81],  # A minor
        }
        scale = scales.get(key, scales["C"])

        melody = [
            {"pitch": scale[i % len(scale)], "duration": 0.5, "velocity": 64}
            for i in range(length * 4)
        ]

        harmony = [
            {"root": scale[0], "quality": "major" if key == "C" else "minor", "inversion": 0}
            for _ in range(length)
        ]

        return {
            "style": style,
            "key": key,
            "length": length,
            "melody": melody,
            "harmony": harmony,
            "tempo": 120,
            "time_signature": "4/4",
            "gf3_trits": [
                hash_to_gf3_trit(f"melody_{style}", 0).value,
                hash_to_gf3_trit(f"harmony_{key}", 1).value,
                -hash_to_gf3_trit(f"rhythm_{length}", 2).value,
            ]
        }

class PersonalizerApp:
    """Personalizer Application: Recommendations and user segmentation"""

    async def execute(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Execute personalization query"""
        user_id = params.get("user_id", "anonymous")
        query_type = params.get("query_type", "recommend")
        context = params.get("context", {})

        await asyncio.sleep(0.15)

        if query_type == "recommend":
            # Generate recommendations
            recommendations = [
                {
                    "item_id": f"item_{i}",
                    "score": 0.9 - (i * 0.05),
                    "reason": f"Based on preference pattern {i % 3}",
                    "gf3_color": hash_to_gf3_trit(f"{user_id}_{i}", i).value
                }
                for i in range(5)
            ]

            return {
                "user_id": user_id,
                "recommendations": recommendations,
                "personalization_score": 0.87,
                "gf3_trits": [r["gf3_color"] for r in recommendations[:3]]
            }

        elif query_type == "segment":
            # User segmentation
            segment = hash_to_gf3_trit(user_id, 0).name.lower()
            return {
                "user_id": user_id,
                "segment": segment,
                "confidence": 0.82,
                "characteristics": [f"trait_{i}" for i in range(3)],
                "gf3_trits": [hash_to_gf3_trit(user_id, i).value for i in range(3)]
            }

        else:
            raise ValueError(f"Unknown query_type: {query_type}")

class ConsensusApp:
    """Consensus Application: Distributed state consensus"""

    async def execute(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Execute consensus query"""
        proposal = params.get("proposal", {})
        agents = params.get("agents", 3)

        await asyncio.sleep(0.2)

        # Simulate consensus voting
        votes = [
            {
                "agent_id": f"agent_{i}",
                "vote": hash_to_gf3_trit(f"{proposal}_{i}", i).value,
                "confidence": 0.7 + (i * 0.05)
            }
            for i in range(agents)
        ]

        vote_sum = sum(v["vote"] for v in votes)
        consensus_reached = abs(vote_sum) >= (agents // 2)

        return {
            "proposal": proposal,
            "agents": agents,
            "votes": votes,
            "consensus_reached": consensus_reached,
            "consensus_value": vote_sum,
            "gf3_trits": [v["vote"] for v in votes[:3]]
        }

class QueryEngineApp:
    """Query Engine Application: Parallel batch processing"""

    async def execute(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Execute parallel queries"""
        queries = params.get("queries", [])
        parallel = params.get("parallel", True)

        if parallel:
            results = await asyncio.gather(*[
                self._execute_single_query(q) for q in queries
            ])
        else:
            results = [await self._execute_single_query(q) for q in queries]

        return {
            "total_queries": len(queries),
            "results": results,
            "parallel": parallel,
            "gf3_trits": [hash_to_gf3_trit(f"q_{i}", i).value for i in range(min(3, len(queries)))]
        }

    async def _execute_single_query(self, query: str) -> Dict[str, Any]:
        """Execute a single query"""
        await asyncio.sleep(0.05)
        return {
            "query": query,
            "result_count": len(query) % 10,
            "gf3_color": hash_to_gf3_trit(query, 0).value
        }

class ColorNavigatorApp:
    """Color Navigator: GF(3) color space exploration"""

    async def execute(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Navigate GF(3) color space"""
        start_color = params.get("start_color", [0, 0, 0])
        steps = params.get("steps", 5)

        await asyncio.sleep(0.1)

        # Generate color trajectory
        trajectory = [start_color]
        current = list(start_color)

        for i in range(steps):
            # Random walk in GF(3) space
            delta = [hash_to_gf3_trit(f"step_{i}_{j}", i).value for j in range(3)]
            current = [(current[j] + delta[j]) % 3 - 1 for j in range(3)]
            trajectory.append(current[:])

        return {
            "start_color": start_color,
            "trajectory": trajectory,
            "steps": steps,
            "final_color": current,
            "gf3_trits": current
        }

class WorldNavigatorApp:
    """World Navigator: Possible world traversal"""

    async def execute(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Navigate possible worlds"""
        current_world = params.get("current_world", "world_0")
        distance = params.get("distance", 2)

        await asyncio.sleep(0.15)

        # Generate reachable worlds
        worlds = [
            {
                "world_id": f"world_{i}",
                "distance": i,
                "entropy": 0.5 + (i * 0.1),
                "gf3_signature": [hash_to_gf3_trit(f"w_{i}_{j}", i).value for j in range(3)]
            }
            for i in range(distance + 1)
        ]

        return {
            "current_world": current_world,
            "reachable_worlds": worlds,
            "max_distance": distance,
            "gf3_trits": worlds[-1]["gf3_signature"] if worlds else [0, 0, 0]
        }

class EpistemologyApp:
    """Epistemology: Knowledge graph queries"""

    async def execute(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Query knowledge graph"""
        concept = params.get("concept", "knowledge")
        depth = params.get("depth", 2)

        await asyncio.sleep(0.1)

        # Generate knowledge graph
        graph = {
            "concept": concept,
            "related_concepts": [f"related_{i}" for i in range(5)],
            "depth": depth,
            "connections": [
                {
                    "from": concept,
                    "to": f"related_{i}",
                    "strength": 0.8 - (i * 0.1),
                    "gf3_color": hash_to_gf3_trit(f"{concept}_{i}", i).value
                }
                for i in range(5)
            ],
            "gf3_trits": [hash_to_gf3_trit(f"{concept}_{i}", i).value for i in range(3)]
        }

        return graph

class ActiveInferenceApp:
    """Active Inference: Free energy minimization"""

    async def execute(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Run active inference"""
        observation = params.get("observation", [0.5, 0.5, 0.5])
        prior = params.get("prior", [0.33, 0.33, 0.34])

        await asyncio.sleep(0.12)

        # Compute free energy
        posterior = [
            (obs * pr) / sum(o * p for o, p in zip(observation, prior))
            for obs, pr in zip(observation, prior)
        ]

        free_energy = -sum(p * np.log(p + 1e-10) for p in posterior)

        return {
            "observation": observation,
            "prior": prior,
            "posterior": posterior,
            "free_energy": float(free_energy),
            "surprise": float(-np.log(sum(observation))),
            "gf3_trits": [hash_to_gf3_trit(f"inf_{i}", i).value for i in range(3)]
        }

class PatternDiscoveryApp:
    """Pattern Discovery: 5D pattern extraction"""

    async def execute(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Discover patterns in data"""
        data = params.get("data", [])
        dimensions = params.get("dimensions", 5)

        await asyncio.sleep(0.18)

        # Extract patterns
        patterns = [
            {
                "pattern_id": f"pattern_{i}",
                "confidence": 0.9 - (i * 0.1),
                "dimensions": [f"dim_{j}" for j in range(dimensions)],
                "gf3_color": hash_to_gf3_trit(f"pat_{i}", i).value
            }
            for i in range(3)
        ]

        return {
            "total_patterns": len(patterns),
            "patterns": patterns,
            "dimensions": dimensions,
            "gf3_trits": [p["gf3_color"] for p in patterns]
        }

class ThreadAnalysisApp:
    """Thread Analysis: Conversation graph analysis"""

    async def execute(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Analyze conversation threads"""
        thread_id = params.get("thread_id", "thread_0")
        analysis_type = params.get("analysis_type", "summary")

        await asyncio.sleep(0.14)

        return {
            "thread_id": thread_id,
            "analysis_type": analysis_type,
            "message_count": 42,
            "participants": 5,
            "key_concepts": ["concept_1", "concept_2", "concept_3"],
            "sentiment": 0.65,
            "gf3_trits": [hash_to_gf3_trit(f"{thread_id}_{i}", i).value for i in range(3)]
        }

# =============================================================================
# APPLICATION REGISTRY INSTANCE
# =============================================================================

class ApplicationRegistry:
    """Central registry for all applications"""

    def __init__(self):
        self.apps: Dict[str, ApplicationSpec] = {}
        self._register_all_apps()

    def _register_all_apps(self):
        """Register all 11 applications"""

        # ALPHA: Market Maker
        self.register(ApplicationSpec(
            name="market_maker",
            description="Liquidity and pricing queries for property stablecoin market",
            category="alpha",
            input_schema={"query_type": "str", "asset": "str", "amount": "float"},
            output_schema={"bid": "float", "ask": "float", "spread": "float"},
            rate_limit=100,
            handler=MarketMakerApp().execute
        ))

        # BETA: Composer
        self.register(ApplicationSpec(
            name="composer",
            description="Generate melody, harmony, and rhythm compositions",
            category="beta",
            input_schema={"style": "str", "length": "int", "key": "str"},
            output_schema={"melody": "list", "harmony": "list", "tempo": "int"},
            rate_limit=50,
            handler=ComposerApp().execute
        ))

        # BETA: Personalizer
        self.register(ApplicationSpec(
            name="personalizer",
            description="Recommendations and user segmentation",
            category="beta",
            input_schema={"user_id": "str", "query_type": "str"},
            output_schema={"recommendations": "list", "segment": "str"},
            rate_limit=200,
            handler=PersonalizerApp().execute
        ))

        # GAMMA: Consensus
        self.register(ApplicationSpec(
            name="consensus",
            description="Distributed state consensus among agents",
            category="gamma",
            input_schema={"proposal": "dict", "agents": "int"},
            output_schema={"consensus_reached": "bool", "votes": "list"},
            rate_limit=80,
            handler=ConsensusApp().execute
        ))

        # GAMMA: Query Engine
        self.register(ApplicationSpec(
            name="query_engine",
            description="Parallel batch processing of queries",
            category="gamma",
            input_schema={"queries": "list", "parallel": "bool"},
            output_schema={"results": "list", "total_queries": "int"},
            rate_limit=150,
            handler=QueryEngineApp().execute
        ))

        # BASELINE: Color Navigator
        self.register(ApplicationSpec(
            name="color_navigator",
            description="GF(3) color space exploration",
            category="baseline",
            input_schema={"start_color": "list", "steps": "int"},
            output_schema={"trajectory": "list", "final_color": "list"},
            rate_limit=300,
            handler=ColorNavigatorApp().execute
        ))

        # BASELINE: World Navigator
        self.register(ApplicationSpec(
            name="world_navigator",
            description="Possible world traversal and exploration",
            category="baseline",
            input_schema={"current_world": "str", "distance": "int"},
            output_schema={"reachable_worlds": "list"},
            rate_limit=200,
            handler=WorldNavigatorApp().execute
        ))

        # BASELINE: Epistemology
        self.register(ApplicationSpec(
            name="epistemology",
            description="Knowledge graph queries and reasoning",
            category="baseline",
            input_schema={"concept": "str", "depth": "int"},
            output_schema={"related_concepts": "list", "connections": "list"},
            rate_limit=250,
            handler=EpistemologyApp().execute
        ))

        # BASELINE: Active Inference
        self.register(ApplicationSpec(
            name="active_inference",
            description="Free energy minimization and predictive processing",
            category="baseline",
            input_schema={"observation": "list", "prior": "list"},
            output_schema={"posterior": "list", "free_energy": "float"},
            rate_limit=180,
            handler=ActiveInferenceApp().execute
        ))

        # BASELINE: Pattern Discovery
        self.register(ApplicationSpec(
            name="pattern_discovery",
            description="5D pattern extraction and clustering",
            category="baseline",
            input_schema={"data": "list", "dimensions": "int"},
            output_schema={"patterns": "list"},
            rate_limit=100,
            handler=PatternDiscoveryApp().execute
        ))

        # BASELINE: Thread Analysis
        self.register(ApplicationSpec(
            name="thread_analysis",
            description="Conversation graph analysis",
            category="baseline",
            input_schema={"thread_id": "str", "analysis_type": "str"},
            output_schema={"key_concepts": "list", "sentiment": "float"},
            rate_limit=120,
            handler=ThreadAnalysisApp().execute
        ))

    def register(self, spec: ApplicationSpec):
        """Register an application"""
        self.apps[spec.name] = spec

    def get(self, name: str) -> Optional[ApplicationSpec]:
        """Get application by name"""
        return self.apps.get(name)

    def list_all(self) -> List[Dict[str, Any]]:
        """List all registered applications"""
        return [
            {
                "name": spec.name,
                "description": spec.description,
                "category": spec.category,
                "input_schema": spec.input_schema,
                "output_schema": spec.output_schema,
                "rate_limit": spec.rate_limit,
                "supports_streaming": spec.supports_streaming
            }
            for spec in self.apps.values()
        ]

# =============================================================================
# COMPOSITION ENGINE
# =============================================================================

@dataclass
class CompositionStep:
    """Single step in a composition chain"""
    app_name: str
    input_mapping: Dict[str, str]  # Maps output fields to input fields
    params: Dict[str, Any]

@dataclass
class CompositionChain:
    """Multi-step composition chain"""
    id: str
    steps: List[CompositionStep]
    results: List[ExecutionResult] = field(default_factory=list)
    status: str = "pending"
    started_at: datetime = field(default_factory=datetime.now)
    completed_at: Optional[datetime] = None

class CompositionEngine:
    """Execute composition chains"""

    def __init__(self, registry: ApplicationRegistry):
        self.registry = registry
        self.chains: Dict[str, CompositionChain] = {}

    async def execute_chain(self, chain: CompositionChain) -> CompositionChain:
        """Execute a composition chain"""
        chain.status = "running"
        chain.started_at = datetime.now()

        try:
            previous_output = {}

            for step in chain.steps:
                # Get application
                app = self.registry.get(step.app_name)
                if not app:
                    raise ValueError(f"Unknown application: {step.app_name}")

                # Map inputs from previous outputs
                step_params = dict(step.params)
                for output_field, input_field in step.input_mapping.items():
                    if output_field in previous_output:
                        step_params[input_field] = previous_output[output_field]

                # Execute step
                result = ExecutionResult(
                    id=str(uuid4()),
                    app_name=step.app_name,
                    status="running",
                    input_data=step_params
                )

                start_time = time.time()
                output = await app.handler(step_params)
                execution_time = (time.time() - start_time) * 1000

                # Validate GF(3) if required
                gf3_valid = True
                if app.gf3_validation:
                    gf3_valid, error_msg = validate_gf3_conservation(output)
                    if not gf3_valid:
                        logging.warning(f"GF(3) validation failed for {step.app_name}: {error_msg}")

                result.output_data = output
                result.status = "completed"
                result.completed_at = datetime.now()
                result.execution_time_ms = execution_time
                result.gf3_valid = gf3_valid

                chain.results.append(result)
                previous_output = output

            chain.status = "completed"
            chain.completed_at = datetime.now()

        except Exception as e:
            chain.status = "failed"
            logging.error(f"Chain execution failed: {e}")
            if chain.results:
                chain.results[-1].error = str(e)
                chain.results[-1].status = "failed"

        return chain

# =============================================================================
# SECURITY & RATE LIMITING
# =============================================================================

class APIKeyManager:
    """Manage API keys and authentication"""

    def __init__(self):
        self.keys: Dict[str, Dict[str, Any]] = {
            "demo_key": {
                "user_id": "demo_user",
                "permissions": ["all"],
                "created_at": datetime.now()
            }
        }

    def validate_key(self, api_key: str) -> Tuple[bool, Optional[str]]:
        """Validate API key, return (valid, user_id)"""
        if api_key in self.keys:
            return True, self.keys[api_key]["user_id"]
        return False, None

    def create_key(self, user_id: str) -> str:
        """Create new API key"""
        key = secrets.token_urlsafe(32)
        self.keys[key] = {
            "user_id": user_id,
            "permissions": ["all"],
            "created_at": datetime.now()
        }
        return key

class RateLimiter:
    """Rate limiting per application and user"""

    def __init__(self):
        self.requests: Dict[str, List[datetime]] = defaultdict(list)

    def check_limit(self, user_id: str, app_name: str, limit: int) -> Tuple[bool, int]:
        """
        Check if request is within rate limit.
        Returns (allowed, remaining).
        """
        key = f"{user_id}:{app_name}"
        now = datetime.now()
        cutoff = now - timedelta(minutes=1)

        # Remove old requests
        self.requests[key] = [
            req_time for req_time in self.requests[key]
            if req_time > cutoff
        ]

        # Check limit
        current_count = len(self.requests[key])
        if current_count >= limit:
            return False, 0

        # Record new request
        self.requests[key].append(now)
        return True, limit - current_count - 1

# =============================================================================
# HTTP/WEBSOCKET SERVER
# =============================================================================

class MarketplaceGateway:
    """Main API gateway server"""

    def __init__(self, host: str = "0.0.0.0", port: int = 8080):
        self.host = host
        self.port = port
        self.registry = ApplicationRegistry()
        self.composition_engine = CompositionEngine(self.registry)
        self.api_keys = APIKeyManager()
        self.rate_limiter = RateLimiter()
        self.results_cache: Dict[str, ExecutionResult] = {}
        self.app = web.Application()
        self._setup_routes()

        # Audit logging
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        )
        self.logger = logging.getLogger("MarketplaceGateway")

    def _setup_routes(self):
        """Setup HTTP routes"""
        self.app.router.add_get('/apps', self.handle_list_apps)
        self.app.router.add_post('/execute', self.handle_execute)
        self.app.router.add_post('/compose', self.handle_compose)
        self.app.router.add_get('/results/{result_id}', self.handle_get_result)
        self.app.router.add_get('/health', self.handle_health)
        self.app.router.add_get('/stream', self.handle_websocket)

    def _authenticate(self, request: web.Request) -> Tuple[bool, Optional[str]]:
        """Authenticate request"""
        api_key = request.headers.get("X-API-Key", "")
        return self.api_keys.validate_key(api_key)

    async def handle_list_apps(self, request: web.Request) -> web.Response:
        """GET /apps - List all applications"""
        authenticated, user_id = self._authenticate(request)
        if not authenticated:
            return web.json_response({"error": "Invalid API key"}, status=401)

        apps = self.registry.list_all()
        return web.json_response({
            "total": len(apps),
            "applications": apps
        })

    async def handle_execute(self, request: web.Request) -> web.Response:
        """POST /execute - Execute single application"""
        authenticated, user_id = self._authenticate(request)
        if not authenticated:
            return web.json_response({"error": "Invalid API key"}, status=401)

        try:
            data = await request.json()
            app_name = data.get("app_name")
            params = data.get("params", {})

            # Get application
            app = self.registry.get(app_name)
            if not app:
                return web.json_response({"error": f"Unknown application: {app_name}"}, status=404)

            # Check rate limit
            allowed, remaining = self.rate_limiter.check_limit(user_id, app_name, app.rate_limit)
            if not allowed:
                return web.json_response({
                    "error": "Rate limit exceeded",
                    "retry_after": 60
                }, status=429)

            # Execute
            result = ExecutionResult(
                id=str(uuid4()),
                app_name=app_name,
                status="running",
                input_data=params
            )

            start_time = time.time()
            output = await app.handler(params)
            execution_time = (time.time() - start_time) * 1000

            # Validate GF(3)
            gf3_valid = True
            if app.gf3_validation:
                gf3_valid, error_msg = validate_gf3_conservation(output)

            result.output_data = output
            result.status = "completed"
            result.completed_at = datetime.now()
            result.execution_time_ms = execution_time
            result.gf3_valid = gf3_valid

            # Cache result
            self.results_cache[result.id] = result

            # Audit log
            self.logger.info(f"Execute {app_name} by {user_id}: {execution_time:.2f}ms")

            return web.json_response({
                "result_id": result.id,
                "status": result.status,
                "output": result.output_data,
                "execution_time_ms": result.execution_time_ms,
                "gf3_valid": result.gf3_valid,
                "rate_limit_remaining": remaining
            })

        except Exception as e:
            self.logger.error(f"Execute error: {e}")
            return web.json_response({"error": str(e)}, status=500)

    async def handle_compose(self, request: web.Request) -> web.Response:
        """POST /compose - Execute composition chain"""
        authenticated, user_id = self._authenticate(request)
        if not authenticated:
            return web.json_response({"error": "Invalid API key"}, status=401)

        try:
            data = await request.json()
            steps_data = data.get("steps", [])

            # Parse steps
            steps = [
                CompositionStep(
                    app_name=step["app_name"],
                    input_mapping=step.get("input_mapping", {}),
                    params=step.get("params", {})
                )
                for step in steps_data
            ]

            # Create chain
            chain = CompositionChain(
                id=str(uuid4()),
                steps=steps
            )

            # Execute chain
            chain = await self.composition_engine.execute_chain(chain)

            # Audit log
            self.logger.info(f"Compose chain {chain.id} by {user_id}: {len(steps)} steps")

            return web.json_response({
                "chain_id": chain.id,
                "status": chain.status,
                "steps": len(steps),
                "results": [
                    {
                        "app_name": r.app_name,
                        "status": r.status,
                        "output": r.output_data,
                        "execution_time_ms": r.execution_time_ms,
                        "gf3_valid": r.gf3_valid
                    }
                    for r in chain.results
                ]
            })

        except Exception as e:
            self.logger.error(f"Compose error: {e}")
            return web.json_response({"error": str(e)}, status=500)

    async def handle_get_result(self, request: web.Request) -> web.Response:
        """GET /results/{result_id} - Get cached result"""
        authenticated, user_id = self._authenticate(request)
        if not authenticated:
            return web.json_response({"error": "Invalid API key"}, status=401)

        result_id = request.match_info['result_id']
        result = self.results_cache.get(result_id)

        if not result:
            return web.json_response({"error": "Result not found"}, status=404)

        return web.json_response({
            "result_id": result.id,
            "app_name": result.app_name,
            "status": result.status,
            "output": result.output_data,
            "execution_time_ms": result.execution_time_ms,
            "gf3_valid": result.gf3_valid
        })

    async def handle_health(self, request: web.Request) -> web.Response:
        """GET /health - Health check"""
        return web.json_response({
            "status": "healthy",
            "apps_count": len(self.registry.apps),
            "cached_results": len(self.results_cache)
        })

    async def handle_websocket(self, request: web.Request) -> web.WebSocketResponse:
        """WebSocket /stream - Real-time streaming"""
        ws = web.WebSocketResponse()
        await ws.prepare(request)

        self.logger.info("WebSocket connection established")

        try:
            async for msg in ws:
                if msg.type == aiohttp.WSMsgType.TEXT:
                    data = json.loads(msg.data)

                    # Authenticate
                    api_key = data.get("api_key", "")
                    valid, user_id = self.api_keys.validate_key(api_key)
                    if not valid:
                        await ws.send_json({"error": "Invalid API key"})
                        continue

                    # Execute command
                    command = data.get("command", "")
                    if command == "execute":
                        app_name = data.get("app_name")
                        params = data.get("params", {})

                        app = self.registry.get(app_name)
                        if app:
                            output = await app.handler(params)
                            await ws.send_json({
                                "type": "result",
                                "app_name": app_name,
                                "output": output
                            })
                        else:
                            await ws.send_json({"error": f"Unknown app: {app_name}"})

                elif msg.type == aiohttp.WSMsgType.ERROR:
                    self.logger.error(f'WebSocket error: {ws.exception()}')

        finally:
            self.logger.info("WebSocket connection closed")

        return ws

    async def start(self):
        """Start the gateway server"""
        runner = web.AppRunner(self.app)
        await runner.setup()
        site = web.TCPSite(runner, self.host, self.port)
        await site.start()

        self.logger.info(f"Marketplace Gateway running on http://{self.host}:{self.port}")
        self.logger.info(f"Registered {len(self.registry.apps)} applications")
        self.logger.info("Endpoints:")
        self.logger.info("  GET  /apps")
        self.logger.info("  POST /execute")
        self.logger.info("  POST /compose")
        self.logger.info("  GET  /results/{id}")
        self.logger.info("  GET  /health")
        self.logger.info("  WS   /stream")

        # Keep running
        try:
            await asyncio.Event().wait()
        except KeyboardInterrupt:
            await runner.cleanup()

# =============================================================================
# MAIN
# =============================================================================

async def main():
    """Main entry point"""
    import argparse

    parser = argparse.ArgumentParser(description="Unified API Marketplace Gateway")
    parser.add_argument("--host", default="0.0.0.0", help="Server host")
    parser.add_argument("--port", type=int, default=8080, help="Server port")
    args = parser.parse_args()

    gateway = MarketplaceGateway(host=args.host, port=args.port)
    await gateway.start()

if __name__ == "__main__":
    asyncio.run(main())
