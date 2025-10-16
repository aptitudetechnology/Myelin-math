import numpy as np
import matplotlib.pyplot as plt
import matplotlib.animation as animation
from matplotlib.patches import Rectangle
import math

# Animation for myelin-induced gain control relationships
# Based on Lean formalization data

def animate_delay_velocity():
    """Animate the relationship between conduction velocity and axonal delay"""
    fig, ax = plt.subplots(figsize=(10, 6))

    # Parameters
    l = 1.0  # axonal length (normalized)
    c_values = np.linspace(0.1, 100, 200)
    delays = l / c_values

    # Plot elements
    line, = ax.plot([], [], 'b-', linewidth=3, label='τ = l/c')
    point, = ax.plot([], [], 'ro', markersize=8, label='Current velocity')

    # Mark the paper values
    ax.axvline(x=0.5, color='red', linestyle='--', alpha=0.7, label='Low myelination (c=0.5)')
    ax.axvline(x=50, color='blue', linestyle='--', alpha=0.7, label='High myelination (c=50)')

    ax.set_xlim(0.1, 100)
    ax.set_ylim(0, 10)
    ax.set_xlabel('Conduction Velocity (m/s)', fontsize=12)
    ax.set_ylabel('Axonal Delay (ms)', fontsize=12)
    ax.set_title('Myelin Effect: Higher Velocity → Shorter Delay', fontsize=14)
    ax.legend()
    ax.grid(True, alpha=0.3)

    def animate(frame):
        n = min(frame + 1, len(c_values))
        line.set_data(c_values[:n], delays[:n])

        # Highlight current point
        if n > 0:
            point.set_data([c_values[n-1]], [delays[n-1]])

        return line, point

    anim = animation.FuncAnimation(fig, animate, frames=len(c_values),
                                 interval=50, blit=True, repeat=True)
    return anim

def animate_gain_function():
    """Animate the gain function with different β parameters"""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(15, 6))

    v_values = np.linspace(-2, 4, 200)
    beta_values = np.linspace(0.5, 5, 100)
    h = 0.5  # threshold

    # Left plot: Gain function evolution
    line, = ax1.plot([], [], 'g-', linewidth=3, label='f(v)')
    beta_text = ax1.text(0.02, 0.98, '', transform=ax1.transAxes,
                        verticalalignment='top', fontsize=12,
                        bbox=dict(boxstyle='round', facecolor='wheat'))

    ax1.set_xlim(-2, 4)
    ax1.set_ylim(0, 1.1)
    ax1.set_xlabel('Membrane Potential (v)', fontsize=12)
    ax1.set_ylabel('Firing Rate (Hz)', fontsize=12)
    ax1.set_title('Gain Function: f(v) = 1/(1 + exp(-β(v - h)))', fontsize=14)
    ax1.grid(True, alpha=0.3)
    ax1.axvline(x=h, color='gray', linestyle=':', alpha=0.7, label='Threshold (h=0.5)')
    ax1.legend()

    # Right plot: β vs gain at v=h
    beta_plot, = ax2.plot([], [], 'b-', linewidth=2)
    current_point, = ax2.plot([], [], 'ro', markersize=8)

    ax2.set_xlim(0.5, 5)
    ax2.set_ylim(0, 1.1)
    ax2.set_xlabel('Gain Parameter (β)', fontsize=12)
    ax2.set_ylabel('Firing Rate at Threshold', fontsize=12)
    ax2.set_title('Gain Control: Higher β → Sharper Response', fontsize=14)
    ax2.grid(True, alpha=0.3)

    def animate(frame):
        beta = beta_values[frame]
        gain = 1 / (1 + np.exp(-beta * (v_values - h)))

        # Update left plot
        line.set_data(v_values, gain)
        beta_text.set_text(f'β = {beta:.1f}')

        # Update right plot
        gain_at_threshold = 1 / (1 + np.exp(-beta * (h - h)))  # v = h
        beta_plot.set_data(beta_values[:frame+1],
                          [1 / (1 + np.exp(-b * (h - h))) for b in beta_values[:frame+1]])
        current_point.set_data([beta], [gain_at_threshold])

        return line, beta_text, beta_plot, current_point

    anim = animation.FuncAnimation(fig, animate, frames=len(beta_values),
                                 interval=100, blit=True, repeat=True)
    return anim

def animate_network_response():
    """Animate the network response to myelination changes"""
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 10))

    # Simulate time series
    t = np.linspace(0, 10, 500)
    stimulus = 0.5 * (1 + np.sin(2 * np.pi * 0.5 * t))  # Oscillating stimulus

    # Low myelination (c=0.5): slower response, lower gain
    tau_low = 1.0 / 0.5  # delay
    response_low = 0.3 * np.convolve(stimulus, np.exp(-t/tau_low), mode='same') / np.max(np.convolve(stimulus, np.exp(-t/tau_low), mode='same'))

    # High myelination (c=50): faster response, higher gain
    tau_high = 1.0 / 50
    response_high = 0.8 * np.convolve(stimulus, np.exp(-t/tau_high), mode='same') / np.max(np.convolve(stimulus, np.exp(-t/tau_high), mode='same'))

    # Top plot: Time series
    stim_line, = ax1.plot([], [], 'k--', alpha=0.7, label='Stimulus S(t)')
    low_line, = ax1.plot([], [], 'r-', linewidth=2, label='Low myelination (c=0.5)')
    high_line, = ax1.plot([], [], 'b-', linewidth=2, label='High myelination (c=50)')

    ax1.set_xlim(0, 10)
    ax1.set_ylim(-0.1, 1.1)
    ax1.set_ylabel('Response Amplitude', fontsize=12)
    ax1.set_title('Network Response Dynamics: Myelin Accelerates and Amplifies', fontsize=14)
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Bottom plot: Firing rate distributions
    bins = np.linspace(0, 1, 30)
    low_hist = ax2.hist([], bins=bins, alpha=0.7, color='red', label='Low myelination')
    high_hist = ax2.hist([], bins=bins, alpha=0.7, color='blue', label='High myelination')

    ax2.set_xlim(0, 1)
    ax2.set_ylim(0, 100)
    ax2.set_xlabel('Firing Rate', fontsize=12)
    ax2.set_ylabel('Count', fontsize=12)
    ax2.set_title('Firing Rate Distribution Shift', fontsize=14)
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    def animate(frame):
        n = min(frame + 1, len(t))

        # Update time series
        stim_line.set_data(t[:n], stimulus[:n])
        low_line.set_data(t[:n], response_low[:n])
        high_line.set_data(t[:n], response_high[:n])

        # Update histograms with current data
        current_low = response_low[:n]
        current_high = response_high[:n]

        # Clear previous histograms
        ax2.clear()
        ax2.hist(current_low, bins=bins, alpha=0.7, color='red', label='Low myelination')
        ax2.hist(current_high, bins=bins, alpha=0.7, color='blue', label='High myelination')
        ax2.set_xlim(0, 1)
        ax2.set_ylim(0, 100)
        ax2.set_xlabel('Firing Rate', fontsize=12)
        ax2.set_ylabel('Count', fontsize=12)
        ax2.set_title('Firing Rate Distribution Shift', fontsize=14)
        ax2.legend()
        ax2.grid(True, alpha=0.3)

        return stim_line, low_line, high_line

    anim = animation.FuncAnimation(fig, animate, frames=len(t),
                                 interval=20, blit=False, repeat=True)
    return anim

if __name__ == "__main__":
    print("Creating animations...")

    # Create animations
    delay_anim = animate_delay_velocity()
    gain_anim = animate_gain_function()
    network_anim = animate_network_response()

    # Save animations
    print("Saving delay-velocity animation...")
    delay_anim.save('/home/chris/Myelin-math/visuals/delay_velocity.gif',
                   writer='pillow', fps=20, dpi=100)

    print("Saving gain function animation...")
    gain_anim.save('/home/chris/Myelin-math/visuals/gain_function.gif',
                  writer='pillow', fps=10, dpi=100)

    print("Saving network response animation...")
    network_anim.save('/home/chris/Myelin-math/visuals/network_response.gif',
                     writer='pillow', fps=25, dpi=100)

    print("Animations saved to visuals/ directory!")
    print("Open the .gif files to see the myelin-gain control relationships in action.")