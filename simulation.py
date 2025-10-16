import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import gamma

# Parameters from the paper
N = 100  # network size
c_low = 0.5  # m/s
c_high = 50.0  # m/s
k = 2  # Gamma shape
theta_low = 4 / c_low  # ms
theta_high = 4 / c_high  # ms
beta = 2
h = 0.5
rho = 1  # all-to-all
I = 0
D = 0.05  # noise?

# Axonal lengths - assume some distribution, say exponential
lengths = np.random.exponential(1, (N, N))  # placeholder

# Delays
delays_low = gamma.rvs(k, scale=theta_low, size=(N, N))
delays_high = gamma.rvs(k, scale=theta_high, size=(N, N))

# Synaptic weights
w = np.ones((N, N))  # identical positive

# Activation function
def f(v):
    return 1 / (1 + np.exp(-beta * (v - h)))

# Simulation parameters
T = 1000  # ms
dt = 0.1
steps = int(T / dt)
time = np.arange(0, T, dt)

# Stimulus S(t) - spatially correlated stochastic
S = np.random.normal(0, 1, steps)  # placeholder

# Initialize rates
r_low = np.zeros((N, steps))
r_high = np.zeros((N, steps))

# For simplicity, use a simple Euler integration for rate model
# dr/dt = -r + f( sum_j w_ij r_j(t - tau_ij) + S(t) )

# But with delays, need history
# This is simplified, assume instantaneous for now, or use convolution

# For simplicity, ignore delays for now, or approximate

# Mean field approximation
r_mean_low = np.zeros(steps)
r_mean_high = np.zeros(steps)

# Simple model: dr/dt = -r + f( r_mean(t - delay) + S(t) )
# But to simplify, assume delay affects the coupling strength or something

# Placeholder simulation
for t in range(1, steps):
    # Low c
    input_low = r_mean_low[max(0, t - int(np.mean(delays_low)/dt))] + S[t]
    r_mean_low[t] = r_mean_low[t-1] + dt * (-r_mean_low[t-1] + f(input_low))
    # High c
    input_high = r_mean_high[max(0, t - int(np.mean(delays_high)/dt))] + S[t]
    r_mean_high[t] = r_mean_high[t-1] + dt * (-r_mean_high[t-1] + f(input_high))

# Plot
plt.figure(figsize=(10, 6))
plt.subplot(2, 1, 1)
plt.plot(time, r_mean_low, 'r', label='Low myelination (c=0.5 m/s)')
plt.plot(time, r_mean_high, 'b', label='High myelination (c=50 m/s)')
plt.xlabel('Time (ms)')
plt.ylabel('Mean firing rate (Hz)')
plt.legend()
plt.title('Network response to stimulus S(t)')

plt.subplot(2, 1, 2)
plt.hist(r_low[:, -1], alpha=0.5, color='red', label='Low c')
plt.hist(r_high[:, -1], alpha=0.5, color='blue', label='High c')
plt.xlabel('Firing rate')
plt.ylabel('Count')
plt.legend()
plt.title('Firing rate distribution')

plt.tight_layout()
plt.show()