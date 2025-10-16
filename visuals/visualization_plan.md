# Visualization Plan for Myelin-Induced Gain Control Formalization

This document outlines a plan to visualize the mathematical concepts formalized in `gain-control.lean`, focusing on the key theorems and relationships from the neural network model described in the paper.

## Core Concepts to Visualize

### 1. Axonal Conduction Velocity and Delay Relationship
**Lean Reference**: `axonal_delay`, `delay_inverse_velocity`, `increased_velocity_decreases_delay`

**Visualization Ideas**:
- Plot τ = l/c for fixed l, varying c (showing inverse relationship)
- Demonstrate doubling velocity halves delay
- Show Gamma-distributed delays for different c values (k=2, θ=4/c)

**Lean Enhancement**: Add computable definitions for plotting data points
```lean
def delay_curve_data (l : ℝ) (c_values : List ℝ) : List (ℝ × ℝ) :=
  c_values.map (fun c => (c, axonal_delay l c))
```

### 2. Gain Function Properties
**Lean Reference**: `gain_function`, `gain_monotone`, `gain_limit_neg_inf`, `gain_limit_pos_inf`

**Visualization Ideas**:
- Plot the sigmoid: f(v) = 1/(1 + exp(-β(v - h))) with β=2, h=0.5
- Show monotonicity (derivative > 0)
- Illustrate limits as v → ±∞
- Compare different β values

**Lean Enhancement**: Define parameter-specific gain functions
```lean
def paper_gain_function : MembranePotential → FiringRate :=
  gain_function 2 0.5
```

### 3. Network-Level Effects
**Lean Reference**: `network_mean_firing_rate`, `scaled_delays`, `higher_velocity_shorter_mean_delay`

**Visualization Ideas**:
- Histogram of firing rates across network
- Mean firing rate vs. conduction velocity
- Distribution changes (normal vs. skewed as in figure insets)

**Lean Enhancement**: Define network configurations
```lean
def low_myelination_network : ConductionVelocity := 0.5
def high_myelination_network : ConductionVelocity := 50.0
```

### 4. Gain Control Mechanism
**Lean Reference**: `gain_control_velocity_effect`

**Visualization Ideas**:
- Plot normalized firing rate vs. conduction velocity (red/blue curves from Fig 1e)
- Show amplification effect
- Membrane potential distributions (Fig 1f histograms)

**Lean Enhancement**: Formalize the stimulus-response relationship
```lean
def stimulus_response (c : ConductionVelocity) (stimulus : ℝ) : FiringRate :=
  -- Model the effective firing rate given conduction velocity and stimulus
  sorry
```

## Implementation Strategy

### Lean-First Approach
1. **Extend Formalization**: Add computable functions and data structures in Lean for generating visualization data
2. **Extract Data**: Use Lean to compute numerical values for plots (where possible with current Mathlib)
3. **Python Integration**: Use Python scripts to render plots from Lean-computed data
4. **Theorem Visualization**: Create diagrams showing theorem dependencies and proofs

### Advanced Proof Animation with animate-lean-proofs
A powerful tool for visualizing Lean proofs is [animate-lean-proofs](https://github.com/dwrensha/animate-lean-proofs), which generates Blender animations of proof steps.

**Setup Requirements:**
- Install [Blender](https://www.blender.org/) (v4.0.2 or recent)
- Install Pygments: `pip install pygments`
- Clone the animate-lean-proofs repository

**Usage for Our Theorems:**
```bash
# Generate animation data for a specific theorem
lake exe Animate gain-control.lean MyelinGainControl.higher_myelination_reduces_delay > /tmp/delay_proof.json

# Create Blender animation
blender --python animate_proof.py -- /tmp/delay_proof.json
```

**Key Theorems to Animate:**
- `delay_inverse_velocity`: Shows the mathematical relationship τ ∝ 1/c
- `increased_velocity_decreases_delay`: Demonstrates causality
- `gain_monotone`: Illustrates derivative-based monotonicity
- `higher_myelination_reduces_delay`: Network-level effect

**Benefits:**
- **Step-by-step proof visualization**: See how proofs unfold tactically
- **Mathematical intuition**: Animations reveal the "why" behind theorems
- **Educational value**: Perfect for understanding myelin-gain control mechanisms
- **Formal verification**: Ensures animations reflect actual proven mathematics

**Current Status:**
- ✅ Basic theorems (e.g., `gain_control.test`) animate successfully
- ❌ Complex theorems use unsupported tactics (`ring`, `linarith`, `norm_num`)
- 🔄 Alternative: Python-based conceptual animations

### Python Animation for Complex Relationships
For theorems that can't be animated with Blender, create matplotlib animations of the mathematical relationships:

**Delay-Velocity Relationship Animation:**
```python
import matplotlib.pyplot as plt
import matplotlib.animation as animation
import numpy as np

# Data from Lean data generation functions
c_values = np.linspace(0.1, 100, 100)
delays = 1.0 / c_values  # l/c relationship

fig, ax = plt.subplots()
line, = ax.plot([], [], 'b-', linewidth=2)
ax.set_xlim(0.1, 100)
ax.set_ylim(0, 10)
ax.set_xlabel('Conduction Velocity (m/s)')
ax.set_ylabel('Axonal Delay (ms)')

def animate(frame):
    line.set_data(c_values[:frame], delays[:frame])
    return line,

anim = animation.FuncAnimation(fig, animate, frames=len(c_values), interval=50)
anim.save('delay_velocity_animation.gif', writer='pillow')
```

**Gain Function Evolution:**
- Animate the sigmoid function with different β parameters
- Show how higher β creates sharper transitions (relevant to gain control)
- Illustrate the membrane potential → firing rate mapping

**Network Effects Animation:**
- Show how increasing velocity shifts the firing rate distribution
- Animate the transition from low to high myelination states
- Visualize the amplification effect on stimulus response

### Visualization Types
- **Mathematical Functions**: Plots of delay curves, gain functions, distributions
- **Network Diagrams**: Graph representations with myelin thickness/color coding
- **Time Series**: Firing rate dynamics over time
- **Statistical Comparisons**: Before/after myelination effects

### Tools Integration
- **Lean → Data**: Export computed values to JSON/CSV
- **Python Plotting**: matplotlib/seaborn for statistical plots
- **Interactive**: Consider plotly for dynamic parameter exploration
- **Documentation**: Generate theorem dependency graphs

## Next Steps
1. Enhance Lean code with computable visualization helpers
2. Create Python scripts to consume Lean data and generate plots
3. Develop network visualization showing connectivity and delays
4. Build interactive parameter exploration tools

This plan emphasizes using Lean as the mathematical foundation, with visualization as a way to illustrate the formalized theorems and relationships.