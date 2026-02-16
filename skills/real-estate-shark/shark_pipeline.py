#!/usr/bin/env python3
"""
Real Estate Shark Pipeline
Combines ml-sharp 3DGS generation with PropertyPriceOracle valuation.

GF(3) Triad: real-estate-shark(-1) ⊗ duckdb-spatial(0) ⊗ geohash-coloring(+1) = 0 ✓
"""

import subprocess
import json
from pathlib import Path
from dataclasses import dataclass
from typing import Optional
import sys

sys.path.insert(0, str(Path.home() / "ies"))
from addictive_market_dynamics import AdditiveZillowOracle as PropertyPriceOracle, MarketConfig, AdditiveMarketDynamics


@dataclass
class PropertyListing:
    property_id: int
    address: str
    image_path: Path
    base_price: float
    splat_path: Optional[Path] = None
    geohash: Optional[str] = None


class RealEstateShark:
    """
    Pipeline for property visualization and valuation.
    
    Flow:
    1. Image → SHARP → 3DGS splat (trit -1: validation)
    2. Splat + Location → DuckDB Spatial (trit 0: coordination)  
    3. Location → Geohash coloring (trit +1: generation)
    """
    
    def __init__(self, ml_sharp_path: Path = Path.home() / "ies/ml-sharp"):
        self.ml_sharp_path = ml_sharp_path
        self.oracle: Optional[PropertyPriceOracle] = None
        
    def init_oracle(self, listings: list[PropertyListing]):
        """Initialize PropertyPriceOracle with base prices."""
        base_prices = {l.property_id: l.base_price for l in listings}
        self.oracle = PropertyPriceOracle(base_prices)
        
    def generate_splat(
        self, 
        image_path: Path, 
        output_dir: Path,
        device: str = "mps"
    ) -> Path:
        """Generate 3D Gaussian Splat from property image."""
        output_dir.mkdir(parents=True, exist_ok=True)
        
        cmd = [
            str(self.ml_sharp_path / ".venv/bin/sharp"),
            "predict",
            "-i", str(image_path),
            "-o", str(output_dir),
            "--device", device
        ]
        
        subprocess.run(cmd, check=True, capture_output=True)
        
        splat_name = image_path.stem + ".ply"
        return output_dir / splat_name
    
    def batch_generate(
        self,
        listings: list[PropertyListing],
        output_dir: Path,
        device: str = "mps"
    ) -> list[PropertyListing]:
        """Generate splats for all listings."""
        input_dir = output_dir / "images"
        splat_dir = output_dir / "splats"
        input_dir.mkdir(parents=True, exist_ok=True)
        splat_dir.mkdir(parents=True, exist_ok=True)
        
        for listing in listings:
            import shutil
            dest = input_dir / listing.image_path.name
            if not dest.exists():
                shutil.copy(listing.image_path, dest)
        
        cmd = [
            str(self.ml_sharp_path / ".venv/bin/sharp"),
            "predict",
            "-i", str(input_dir),
            "-o", str(splat_dir),
            "--device", device
        ]
        
        subprocess.run(cmd, check=True)
        
        for listing in listings:
            splat_name = listing.image_path.stem + ".ply"
            listing.splat_path = splat_dir / splat_name
            
        return listings
    
    def get_valuation(self, property_id: int) -> dict:
        """Get current valuation with market dynamics."""
        if not self.oracle:
            raise ValueError("Oracle not initialized. Call init_oracle first.")
            
        return {
            "property_id": property_id,
            "price": self.oracle.get_price(property_id),
            "volatility": self.oracle.get_volatility(property_id),
            "sentiment": self.oracle.get_sentiment(property_id),
            "cascade_state": self.oracle.get_cascade_state(property_id)
        }
    
    def analyze_portfolio(self, listings: list[PropertyListing]) -> dict:
        """Analyze entire property portfolio."""
        self.init_oracle(listings)
        
        results = []
        total_value = 0.0
        
        for listing in listings:
            val = self.get_valuation(listing.property_id)
            val["address"] = listing.address
            val["has_splat"] = listing.splat_path is not None and listing.splat_path.exists()
            val["splat_size_mb"] = (
                listing.splat_path.stat().st_size / 1e6 
                if val["has_splat"] else 0
            )
            results.append(val)
            total_value += val["price"]
            
        return {
            "properties": results,
            "total_value": total_value,
            "count": len(listings),
            "avg_volatility": sum(r["volatility"] for r in results) / len(results)
        }


def demo():
    """Demo with neighborhood images."""
    shark = RealEstateShark()
    
    demo_dir = shark.ml_sharp_path / "neighborhood_demo"
    
    listings = [
        PropertyListing(
            property_id=1,
            address="123 Suburban Lane",
            image_path=demo_dir / "input/house1.jpg",
            base_price=450_000,
            splat_path=demo_dir / "output/house1.ply"
        ),
        PropertyListing(
            property_id=2,
            address="456 Modern Ave",
            image_path=demo_dir / "input/house2.jpg",
            base_price=725_000,
            splat_path=demo_dir / "output/house2.ply"
        ),
        PropertyListing(
            property_id=3,
            address="789 Luxury Dr",
            image_path=demo_dir / "input/house3.jpg",
            base_price=1_200_000,
            splat_path=demo_dir / "output/house3.ply"
        ),
    ]
    
    portfolio = shark.analyze_portfolio(listings)
    
    print("=" * 60)
    print("🦈 REAL ESTATE SHARK PORTFOLIO ANALYSIS")
    print("=" * 60)
    print(f"\nTotal Properties: {portfolio['count']}")
    print(f"Portfolio Value: ${portfolio['total_value']:,.2f}")
    print(f"Avg Volatility: {portfolio['avg_volatility']:.2%}")
    print()
    
    for prop in portfolio["properties"]:
        splat_status = f"✓ {prop['splat_size_mb']:.1f}MB" if prop["has_splat"] else "✗"
        print(f"  [{prop['property_id']}] {prop['address']}")
        print(f"      Price: ${prop['price']:,.2f} | Vol: {prop['volatility']:.2%} | 3DGS: {splat_status}")
        print(f"      Sentiment: {prop['sentiment']:.2f} | State: {prop['cascade_state']}")
        print()
    
    print("GF(3) Triad: real-estate-shark(-1) ⊗ duckdb-spatial(0) ⊗ geohash-coloring(+1) = 0 ✓")


if __name__ == "__main__":
    demo()
