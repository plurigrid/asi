#!/usr/bin/env python3
"""
Mathematical Extraction MCP Server

Exposes TeglonLabs/mathpix-gem as a Model Context Protocol server.
Provides structured extraction of mathematical content (equations, diagrams, theorems)
from PDF documents with optional semantic constraints from plurigrid ontologies.

Protocol: MCP (Model Context Protocol)
Resources:
  - math-extraction/pdf/{id}/equations
  - math-extraction/pdf/{id}/theorems
  - math-extraction/pdf/{id}/diagrams
  - math-extraction/extract-with-constraints

Tools:
  - extract_from_pdf(pdf_path, constraints)
  - batch_extract(pdf_urls)
  - extract_by_pattern(pdf_path, pattern)
"""

import json
import hashlib
from dataclasses import dataclass, asdict, field
from typing import Dict, List, Optional, Any, Set
from enum import Enum
import re
from pathlib import Path


class MathematicalStructureType(Enum):
    """Types of mathematical structures that can be extracted"""
    EQUATION = "equation"
    THEOREM = "theorem"
    PROOF = "proof"
    DEFINITION = "definition"
    LEMMA = "lemma"
    COROLLARY = "corollary"
    AXIOM = "axiom"
    DIAGRAM = "diagram"
    EXAMPLE = "example"
    REMARK = "remark"
    PROPOSITION = "proposition"


class ExtractionDomain(Enum):
    """Semantic domains for constraint-guided extraction"""
    ALGEBRA = "algebra"
    ANALYSIS = "analysis"
    GEOMETRY = "geometry"
    TOPOLOGY = "topology"
    CATEGORY_THEORY = "category_theory"
    GAME_THEORY = "game_theory"
    MECHANISM_DESIGN = "mechanism_design"
    AUCTION_THEORY = "auction_theory"
    LOGIC = "logic"
    COMBINATORICS = "combinatorics"
    MEASURE_THEORY = "measure_theory"
    FUNCTIONAL_ANALYSIS = "functional_analysis"


@dataclass
class MathematicalObject:
    """Represents a single extracted mathematical structure"""
    id: str
    structure_type: MathematicalStructureType
    latex: str
    parsed_form: Dict[str, Any] = field(default_factory=dict)
    natural_language: str = ""
    page: int = 0
    location: Dict[str, float] = field(default_factory=dict)  # {x, y, width, height}
    confidence: float = 1.0
    related_objects: List[str] = field(default_factory=list)
    properties: Dict[str, Any] = field(default_factory=dict)


@dataclass
class ExtractionConstraint:
    """Constraint for guided extraction"""
    domains: Optional[List[ExtractionDomain]] = None
    structure_types: Optional[List[MathematicalStructureType]] = None
    keywords: Optional[List[str]] = None
    min_complexity: Optional[int] = None  # 0-10 scale
    max_results: Optional[int] = None


@dataclass
class ExtractionResult:
    """Result of mathematical extraction from a document"""
    pdf_id: str
    pdf_path: str
    extracted_at: str
    total_pages: int

    equations: List[MathematicalObject] = field(default_factory=list)
    theorems: List[MathematicalObject] = field(default_factory=list)
    proofs: List[MathematicalObject] = field(default_factory=list)
    definitions: List[MathematicalObject] = field(default_factory=list)
    diagrams: List[MathematicalObject] = field(default_factory=list)

    metadata: Dict[str, Any] = field(default_factory=dict)
    validation_status: str = "pending"  # pending, valid, invalid
    semantic_tags: List[str] = field(default_factory=list)

    def all_objects(self) -> List[MathematicalObject]:
        """Get all extracted mathematical objects"""
        return (self.equations + self.theorems + self.proofs +
                self.definitions + self.diagrams)

    def count_by_type(self) -> Dict[str, int]:
        """Count objects by type"""
        counts = {
            "equations": len(self.equations),
            "theorems": len(self.theorems),
            "proofs": len(self.proofs),
            "definitions": len(self.definitions),
            "diagrams": len(self.diagrams),
        }
        return {k: v for k, v in counts.items() if v > 0}

    def filter_by_domain(self, domains: List[ExtractionDomain]) -> 'ExtractionResult':
        """Filter results to specific domains"""
        keyword_map = {
            ExtractionDomain.ALGEBRA: ["group", "ring", "field", "monoid", "permutation"],
            ExtractionDomain.ANALYSIS: ["limit", "derivative", "integral", "convergence"],
            ExtractionDomain.TOPOLOGY: ["topological", "open", "closed", "manifold"],
            ExtractionDomain.CATEGORY_THEORY: ["functor", "natural", "morphism", "adjoint"],
            ExtractionDomain.GAME_THEORY: ["game", "strategy", "equilibrium", "payoff"],
            ExtractionDomain.AUCTION_THEORY: ["auction", "bidding", "mechanism", "vcg"],
        }

        domain_keywords = set()
        for domain in domains:
            domain_keywords.update(keyword_map.get(domain, []))

        filtered = ExtractionResult(
            pdf_id=self.pdf_id,
            pdf_path=self.pdf_path,
            extracted_at=self.extracted_at,
            total_pages=self.total_pages,
            metadata=self.metadata,
            validation_status=self.validation_status,
        )

        # Filter all objects
        for obj in self.all_objects():
            keywords_present = any(
                keyword.lower() in obj.latex.lower() or
                keyword.lower() in obj.natural_language.lower()
                for keyword in domain_keywords
            )

            if keywords_present or len(domain_keywords) == 0:
                if obj.structure_type == MathematicalStructureType.EQUATION:
                    filtered.equations.append(obj)
                elif obj.structure_type == MathematicalStructureType.THEOREM:
                    filtered.theorems.append(obj)
                elif obj.structure_type == MathematicalStructureType.PROOF:
                    filtered.proofs.append(obj)
                elif obj.structure_type == MathematicalStructureType.DEFINITION:
                    filtered.definitions.append(obj)
                elif obj.structure_type == MathematicalStructureType.DIAGRAM:
                    filtered.diagrams.append(obj)

        return filtered


class MathJSONSchema:
    """Validates mathematical objects against canonical JSON schema"""

    SCHEMA = {
        "structure_type": ["string", list(e.value for e in MathematicalStructureType)],
        "latex": "string",
        "natural_language": "string",
        "page": "integer",
        "confidence": "float_0_1",
        "properties": "object",
    }

    @staticmethod
    def validate(obj: MathematicalObject) -> bool:
        """Check if object matches schema"""
        required_fields = ["latex", "structure_type"]
        return all(hasattr(obj, field) for field in required_fields)

    @staticmethod
    def to_dict(obj: MathematicalObject) -> Dict[str, Any]:
        """Convert to JSON-serializable dict"""
        return {
            "id": obj.id,
            "structure_type": obj.structure_type.value,
            "latex": obj.latex,
            "natural_language": obj.natural_language,
            "page": obj.page,
            "confidence": obj.confidence,
            "properties": obj.properties,
        }


class MockMathpixClient:
    """
    Mock Mathpix client for demonstration.

    In production, this would call the actual Mathpix API:
    https://mathpix.com/docs/api/overview
    """

    def extract(self, pdf_path: str) -> ExtractionResult:
        """
        Extract mathematical content from PDF.

        Simulates mathpix-gem behavior: identify equations, theorems, diagrams, etc.
        """
        pdf_id = hashlib.md5(pdf_path.encode()).hexdigest()[:8]

        # Mock extraction result
        result = ExtractionResult(
            pdf_id=pdf_id,
            pdf_path=pdf_path,
            extracted_at="2025-12-21T00:00:00Z",
            total_pages=10,
        )

        # Mock: Add some sample equations
        eq1 = MathematicalObject(
            id=f"{pdf_id}_eq_1",
            structure_type=MathematicalStructureType.EQUATION,
            latex=r"d(A, C) \leq d(A, B) + d(B, C)",
            natural_language="Triangle inequality: distance from A to C is at most the sum of distances A to B and B to C",
            page=1,
            confidence=0.95,
            properties={"domain": "metric_spaces"},
        )

        # Mock: Add theorem
        thm1 = MathematicalObject(
            id=f"{pdf_id}_thm_1",
            structure_type=MathematicalStructureType.THEOREM,
            latex=r"\text{If } (G, \cdot, e) \text{ is a group, then } a \cdot a^{-1} = e \text{ for all } a \in G",
            natural_language="In any group, composing an element with its inverse gives the identity",
            page=2,
            confidence=0.92,
            properties={"domain": "algebra", "subfield": "group_theory"},
        )

        # Mock: Add definition
        defn1 = MathematicalObject(
            id=f"{pdf_id}_def_1",
            structure_type=MathematicalStructureType.DEFINITION,
            latex=r"A_{\text{efficient}} = \arg\max_a \sum_i v_i(a)",
            natural_language="An allocation is efficient if it maximizes the total value across all participants",
            page=3,
            confidence=0.88,
            properties={"domain": "auction_theory"},
        )

        result.equations.append(eq1)
        result.theorems.append(thm1)
        result.definitions.append(defn1)

        result.metadata = {
            "source": "mathpix_mock_client",
            "version": "1.0",
        }

        return result


class MathExtractionMCPServer:
    """
    MCP Server for Mathematical Content Extraction

    Provides resources for extracting mathematical structures from PDFs
    with optional semantic constraints from plurigrid ontologies.
    """

    def __init__(self):
        self.mathpix_client = MockMathpixClient()
        self.schema = MathJSONSchema()
        self.extraction_cache: Dict[str, ExtractionResult] = {}
        self.constraint_validators: Dict[str, callable] = {}

    def extract_from_pdf(self, pdf_path: str,
                        constraints: Optional[ExtractionConstraint] = None) -> ExtractionResult:
        """
        Extract mathematical structures from PDF.

        Args:
            pdf_path: Path to PDF document
            constraints: Optional filtering constraints

        Returns:
            ExtractionResult with extracted mathematical objects
        """
        # Check cache
        cache_key = pdf_path + (str(constraints) if constraints else "")
        if cache_key in self.extraction_cache:
            return self.extraction_cache[cache_key]

        # Extract
        result = self.mathpix_client.extract(pdf_path)

        # Apply constraints if provided
        if constraints:
            result = self._apply_constraints(result, constraints)

        # Validate
        result.validation_status = self._validate_result(result)

        # Cache
        self.extraction_cache[cache_key] = result

        return result

    def batch_extract(self, pdf_paths: List[str],
                     constraints: Optional[ExtractionConstraint] = None) -> List[ExtractionResult]:
        """Extract from multiple PDFs"""
        return [self.extract_from_pdf(path, constraints) for path in pdf_paths]

    def extract_by_pattern(self, pdf_path: str, pattern: str) -> List[MathematicalObject]:
        """
        Extract mathematical objects matching a regex pattern.

        Useful for finding specific structures (e.g., "group.*homomorphism")
        """
        result = self.extract_from_pdf(pdf_path)

        matching = []
        for obj in result.all_objects():
            if re.search(pattern, obj.latex, re.IGNORECASE):
                matching.append(obj)

        return matching

    def extract_domain(self, pdf_path: str, domain: ExtractionDomain) -> ExtractionResult:
        """Extract only structures from a specific mathematical domain"""
        constraints = ExtractionConstraint(domains=[domain])
        return self.extract_from_pdf(pdf_path, constraints)

    def extract_with_semantic_guidance(self, pdf_path: str,
                                      semantic_query: str,
                                      ontology: Optional[Dict[str, Any]] = None) -> ExtractionResult:
        """
        Extract with guidance from plurigrid ontology.

        Args:
            pdf_path: Path to PDF
            semantic_query: Natural language query (e.g., "Find auction mechanisms")
            ontology: plurigrid ontology for semantic guidance

        Returns:
            Extracted results constrained by semantic query
        """
        # Parse semantic query to constraints
        constraints = self._parse_semantic_query(semantic_query, ontology)

        return self.extract_from_pdf(pdf_path, constraints)

    # Private methods

    def _apply_constraints(self, result: ExtractionResult,
                          constraints: ExtractionConstraint) -> ExtractionResult:
        """Apply filtering constraints to extraction result"""
        filtered = ExtractionResult(
            pdf_id=result.pdf_id,
            pdf_path=result.pdf_path,
            extracted_at=result.extracted_at,
            total_pages=result.total_pages,
            metadata=result.metadata,
        )

        # Filter by structure type
        all_objs = result.all_objects()
        if constraints.structure_types:
            all_objs = [o for o in all_objs if o.structure_type in constraints.structure_types]

        # Filter by keywords
        if constraints.keywords:
            all_objs = [o for o in all_objs
                       if any(kw.lower() in o.latex.lower() for kw in constraints.keywords)]

        # Filter by domains (using keyword mapping)
        if constraints.domains:
            result = result.filter_by_domain(constraints.domains)
            all_objs = result.all_objects()

        # Limit results
        if constraints.max_results:
            all_objs = all_objs[:constraints.max_results]

        # Categorize back
        for obj in all_objs:
            if obj.structure_type == MathematicalStructureType.EQUATION:
                filtered.equations.append(obj)
            elif obj.structure_type == MathematicalStructureType.THEOREM:
                filtered.theorems.append(obj)
            elif obj.structure_type == MathematicalStructureType.PROOF:
                filtered.proofs.append(obj)
            elif obj.structure_type == MathematicalStructureType.DEFINITION:
                filtered.definitions.append(obj)
            elif obj.structure_type == MathematicalStructureType.DIAGRAM:
                filtered.diagrams.append(obj)

        return filtered

    def _validate_result(self, result: ExtractionResult) -> str:
        """Validate extraction result"""
        valid_count = sum(1 for obj in result.all_objects() if self.schema.validate(obj))
        total_count = len(result.all_objects())

        if total_count == 0:
            return "empty"
        elif valid_count == total_count:
            return "valid"
        else:
            return "partial"

    def _parse_semantic_query(self, query: str,
                             ontology: Optional[Dict[str, Any]] = None) -> ExtractionConstraint:
        """Convert semantic query to extraction constraints"""
        constraint = ExtractionConstraint()

        # Simple keyword-based parsing
        query_lower = query.lower()

        if "auction" in query_lower:
            constraint.domains = [ExtractionDomain.AUCTION_THEORY]
            constraint.keywords = ["auction", "bidding", "mechanism", "vcg"]
        elif "game" in query_lower:
            constraint.domains = [ExtractionDomain.GAME_THEORY]
            constraint.keywords = ["game", "strategy", "equilibrium"]
        elif "category" in query_lower or "functor" in query_lower:
            constraint.domains = [ExtractionDomain.CATEGORY_THEORY]
            constraint.keywords = ["functor", "morphism", "natural"]

        return constraint

    def export_to_json(self, result: ExtractionResult) -> Dict[str, Any]:
        """Export extraction result to JSON-serializable format"""
        return {
            "pdf_id": result.pdf_id,
            "pdf_path": result.pdf_path,
            "extracted_at": result.extracted_at,
            "total_pages": result.total_pages,
            "summary": result.count_by_type(),
            "equations": [self.schema.to_dict(obj) for obj in result.equations],
            "theorems": [self.schema.to_dict(obj) for obj in result.theorems],
            "proofs": [self.schema.to_dict(obj) for obj in result.proofs],
            "definitions": [self.schema.to_dict(obj) for obj in result.definitions],
            "diagrams": [self.schema.to_dict(obj) for obj in result.diagrams],
            "metadata": result.metadata,
            "validation_status": result.validation_status,
        }


# ============================================================================
# Demo / Testing
# ============================================================================

def demo():
    """Demonstrate MCP math extraction server"""
    print("=" * 80)
    print("MATHEMATICAL EXTRACTION MCP SERVER DEMO")
    print("=" * 80)

    server = MathExtractionMCPServer()

    # Demo 1: Basic extraction
    print("\n1. BASIC EXTRACTION")
    print("-" * 80)

    result = server.extract_from_pdf("sample_paper.pdf")
    print(f"Extracted from: {result.pdf_path}")
    print(f"Summary: {result.count_by_type()}")

    # Demo 2: Constrained extraction
    print("\n2. DOMAIN-CONSTRAINED EXTRACTION (Algebra)")
    print("-" * 80)

    result = server.extract_domain("sample_paper.pdf", ExtractionDomain.ALGEBRA)
    print(f"Results matching algebra domain: {result.count_by_type()}")

    # Demo 3: Semantic query
    print("\n3. SEMANTIC QUERY (\"Find auction mechanisms\")")
    print("-" * 80)

    result = server.extract_with_semantic_guidance(
        "sample_paper.pdf",
        "Find auction mechanisms and game theoretic properties"
    )
    print(f"Results: {result.count_by_type()}")

    # Demo 4: Export to JSON
    print("\n4. JSON EXPORT")
    print("-" * 80)

    json_result = server.export_to_json(result)
    print(json.dumps(json_result, indent=2)[:500] + "...")

    # Demo 5: Batch processing
    print("\n5. BATCH EXTRACTION")
    print("-" * 80)

    pdfs = ["paper1.pdf", "paper2.pdf", "paper3.pdf"]
    results = server.batch_extract(pdfs)
    print(f"Processed {len(results)} PDFs")
    for res in results:
        print(f"  {res.pdf_path}: {res.count_by_type()}")


if __name__ == "__main__":
    demo()
