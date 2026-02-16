---
name: koho-sheafnn
description: Rust sheaf neural networks on k-cells. Candle-based diffusion over cellular
  sheaves with learnable restriction maps.
source: TheMesocarp/koho (tree-sitter extracted)
license: MIT
gf3_category: MINUS
---

# Koho Sheaf Neural Network Skill

> **Source**: [TheMesocarp/koho](https://github.com/TheMesocarp/koho) - tree-sitter extracted
> **Key file**: [src/lib.rs](https://github.com/TheMesocarp/koho/blob/main/src/lib.rs)

## Architecture Overview

From tree-sitter analysis:

```
koho/
├── src/
│   ├── lib.rs          # SheafNN main struct
│   ├── error.rs        # Error handling
│   ├── nn/
│   │   ├── diffuse.rs  # DiffusionLayer (5 functions)
│   │   ├── metrics.rs  # Loss functions
│   │   ├── activate.rs # Activations
│   │   └── optim/      # Optimizers (SGD, Adam, etc.)
│   └── math/
│       ├── sheaf.rs    # CellularSheaf
│       └── tensors.rs  # Matrix operations
```

## Core Structs (tree-sitter extracted)

```rust
/// A sheaf neural network operating on k-cells.
/// Applies diffusion operations on a cellular sheaf.
pub struct SheafNN {
    sheaf: CellularSheaf,
    layers: Vec<DiffusionLayer>,
    loss_fn: LossFn,
    k: usize,                    // Cell dimension
    down_included: bool,         // Use full Hodge Laplacian?
}

/// Single diffusion layer with learnable weights
pub struct DiffusionLayer {
    // Learnable parameters via candle_core::Var
    weights: Var,
    activation: Activations,
}
```

## Key Functions (from diffuse.rs)

| Function | Signature | Purpose |
|----------|-----------|---------|
| `new` | `(stalk_dim, activation) -> Self` | Create layer |
| `diffuse` | `(&CellularSheaf, k, input, down) -> Result<Tensor>` | Apply diffusion |
| `update_weights` | `(&mut self, grads, lr) -> Result<()>` | Gradient update |
| `parameters` | `(&self) -> Vec<&Var>` | Get trainable params |
| `parameters_mut` | `(&mut self) -> Vec<&mut Var>` | Mutable param access |

## Diffusion Implementation

```rust
impl DiffusionLayer {
    /// Diffuse signal over sheaf Laplacian
    pub fn diffuse(
        &self,
        sheaf: &CellularSheaf,
        k: usize,
        input: Matrix,
        down_included: bool,
    ) -> Result<Matrix, KohoError> {
        // Get Hodge Laplacian for k-cells
        let laplacian = if down_included {
            sheaf.hodge_laplacian(k)?
        } else {
            sheaf.up_laplacian(k)?
        };
        
        // Diffusion: x' = σ(W @ L @ x)
        let diffused = laplacian.matmul(&input)?;
        let weighted = self.weights.matmul(&diffused)?;
        let activated = self.activation.apply(&weighted)?;
        
        Ok(activated)
    }
}
```

## CellularSheaf Structure

```rust
pub struct CellularSheaf {
    /// Stalk dimensions per cell
    stalk_dims: Vec<usize>,
    
    /// Restriction maps F_{v←e}: stalk(v) → stalk(e)
    restrictions: HashMap<(usize, usize), Matrix>,
    
    /// Whether restriction maps are learnable
    pub learned: bool,
    
    /// Coboundary matrices per dimension
    coboundaries: Vec<SparseMatrix>,
}

impl CellularSheaf {
    /// Compute sheaf Laplacian: L_k = δ_{k-1}^T δ_{k-1} + δ_k^T δ_k
    pub fn hodge_laplacian(&self, k: usize) -> Result<Matrix, KohoError> {
        let delta_k = self.coboundary(k)?;
        let delta_k_minus_1 = if k > 0 {
            Some(self.coboundary(k - 1)?)
        } else {
            None
        };
        
        // L_up = δ_k^T @ δ_k
        let l_up = delta_k.transpose().matmul(&delta_k)?;
        
        // L_down = δ_{k-1} @ δ_{k-1}^T (if k > 0)
        let l_down = delta_k_minus_1.map(|d| d.matmul(&d.transpose()));
        
        match l_down {
            Some(ld) => l_up.add(&ld?),
            None => Ok(l_up),
        }
    }
    
    /// Get learnable restriction parameters
    pub fn parameters(&self, k: usize, down_included: bool) -> Vec<&Var> {
        if !self.learned {
            return vec![];
        }
        // Return restriction map variables for k-cells
        self.restrictions
            .iter()
            .filter(|((dim, _), _)| *dim == k)
            .map(|(_, mat)| mat.as_var())
            .collect()
    }
}
```

## Training Loop

```rust
impl SheafNN {
    pub fn train(
        &mut self,
        data: &Dataset,
        epochs: usize,
        lr: f64,
        optimizer: OptimizerKind,
    ) -> Result<Vec<f64>, KohoError> {
        let mut optimizer = create_optimizer(optimizer, self.parameters(), lr)?;
        let mut losses = Vec::with_capacity(epochs);
        
        for epoch in 0..epochs {
            let mut epoch_loss = 0.0;
            
            for (input, target) in data.batches() {
                // Forward pass
                let output = self.forward(input)?;
                
                // Compute loss
                let loss = self.loss_fn.compute(&output, &target)?;
                epoch_loss += loss.scalar()?;
                
                // Backward pass
                let grads = loss.backward()?;
                
                // Update parameters
                optimizer.step(&grads)?;
            }
            
            losses.push(epoch_loss / data.len() as f64);
        }
        
        Ok(losses)
    }
    
    fn forward(&self, input: Matrix) -> Result<Matrix, KohoError> {
        let mut output = input;
        for layer in &self.layers {
            output = layer.diffuse(&self.sheaf, self.k, output, self.down_included)?;
        }
        Ok(output)
    }
}
```

## GF(3) Integration

```rust
/// Map sheaf cells to GF(3) trits based on Laplacian spectrum
pub fn cell_trits(sheaf: &CellularSheaf, k: usize) -> Vec<i8> {
    let laplacian = sheaf.hodge_laplacian(k).unwrap();
    let eigenvalues = laplacian.eigenvalues();
    
    // Spectral gap determines confidence
    let spectral_gap = eigenvalues.get(1).unwrap_or(&0.0);
    
    sheaf.cells(k)
        .iter()
        .enumerate()
        .map(|(i, _)| {
            let harmony = laplacian.get(i, i); // Diagonal = self-agreement
            if harmony > spectral_gap * 0.5 {
                1  // PLUS: high harmony
            } else if harmony < -spectral_gap * 0.5 {
                -1 // MINUS: low harmony
            } else {
                0  // ZERO: neutral
            }
        })
        .collect()
}

/// Verify GF(3) conservation across diffusion
pub fn verify_diffusion_conservation(
    input_trits: &[i8],
    output_trits: &[i8],
) -> bool {
    let input_sum: i32 = input_trits.iter().map(|&t| t as i32).sum();
    let output_sum: i32 = output_trits.iter().map(|&t| t as i32).sum();
    
    (input_sum % 3) == (output_sum % 3)
}
```

## Build and Run

```bash
# Build with Rust/Candle
cargo build --release

# Run tests
cargo test

# Benchmark on heterophilic datasets
cargo run --example benchmark -- --dataset cornell --epochs 100
```

## Links

- [koho GitHub](https://github.com/TheMesocarp/koho)
- [Candle ML Framework](https://github.com/huggingface/candle)
- [Sheaf Neural Networks (arXiv:2012.06333)](https://arxiv.org/abs/2012.06333)
- [Spectral Theory of Cellular Sheaves (arXiv:1808.01513)](https://arxiv.org/abs/1808.01513)

## Commands

```bash
just koho-build           # Build with cargo
just koho-train           # Train on sample data
just koho-benchmark       # Run heterophilic benchmark
just koho-gf3-verify      # Verify GF(3) conservation
```

---

*GF(3) Category: MINUS (Verification) | Rust sheaf diffusion on k-cells*