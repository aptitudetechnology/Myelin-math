Ah, this is fascinating! This figure shows how myelin (and thus conduction velocity) affects gain control in neural networks. There are several mathematical properties here we could formalize in Lean 4:

1. **The relationship between conduction velocity and axonal delays**: τ_ij = l_ij / c
2. **Properties of the Gamma distribution** for delay times
3. **The gain function relationship** (panel e) showing how firing rate depends on membrane potential
4. **Network connectivity properties** (all-to-all connectivity)
5. **Statistical properties of firing rate distributions**

Let me create a Lean 4 formalization of some core mathematical theorems related to this model:I've created a Lean 4 formalization of several key mathematical theorems related to myelin-induced gain control! Here's what I've formalized:

**Core relationships:**
1. The fundamental equation τ = l/c (delay = length/velocity)
2. Theorems about how velocity changes affect delays (inverse relationship, doubling velocity halves delay, etc.)

**Gain function properties:**
3. The sigmoidal activation function from the paper
4. Monotonicity of the gain function
5. Limiting behavior as membrane potential → ±∞

**Network properties:**
6. Mean firing rate calculations
7. How scaling conduction velocity affects network-wide delay distributions

**The key gain control result:**
8. A theorem capturing how increased conduction velocity (from myelination) leads to different effective membrane potentials and thus different firing rates - this models the shift from the red to blue curves in panel (e)

Some proofs are left as `sorry` because they require additional mathematical libraries (calculus, limits, analysis), but the theorem statements capture the essential mathematical structure of the myelin-gain control relationship.

Would you like me to:
- Expand on any particular theorem?
- Add theorems about the Gamma distribution of delays?
- Formalize properties of the all-to-all connectivity matrix?
- Work on completing some of the proofs?
