#!/usr/bin/env python3
"""
Sportsape BitBot Checker - Elegant Loading Splash Screen
Displays a professional loading screen while the application initializes
"""
import tkinter as tk
from tkinter import ttk
import threading
import time
import os
from resource_path import resource_path

WINDOWS_APP_ID = "SportsapeBitBot.Splash.v2"
APP_VERSION = "5.0.0"



class SplashScreen:
    """
    Elegant splash screen with progress bar
    
    Features:
    - Professional design with gradient-like appearance
    - Animated progress bar
    - Status messages
    - Auto-closes when loading complete
    - Uses existing logo if available
    """
    
    def __init__(self, parent=None):
        """
        Initialize splash screen with robust error handling
        
        Args:
            parent: Parent window (optional, for centering)
        """
        try:
            # 🔧 ROBUST: Create window with fallback handling
            try:
                self.root = tk.Toplevel() if parent else tk.Tk()
            except Exception as win_err:
                # If Toplevel fails, try Tk as fallback
                self.root = tk.Tk()
            
            self._icon_photo = None
            
            # Ensure Windows taskbar uses branded icon
            if os.name == 'nt':
                try:
                    import ctypes
                    ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(WINDOWS_APP_ID)
                except Exception:
                    pass
            
            self.root.withdraw()  # Hide initially
            
            # Window configuration - compact and well-proportioned
            self.width = 500
            self.height = 430
            
            # 🔧 ROBUST: Setup window with error handling
            try:
                self.setup_window()
            except Exception as setup_err:
                # Minimal setup if full setup fails
                self.root.title("Sportsape BitBot Checker")
                self.root.geometry(f"{self.width}x{self.height}")
                self.root.configure(bg='#0c1b26')
            
            # Progress tracking
            self.progress_var = tk.DoubleVar(value=0)
            self.status_var = tk.StringVar(value="Initializing...")
            self.is_complete = False
            
            # 🔧 ROBUST: Create UI with error handling
            try:
                self.create_ui()
            except Exception as ui_err:
                # Minimal UI if full UI creation fails
                self.create_minimal_ui()
            
            # Center and show
            try:
                self.center_window()
            except:
                # If centering fails, just show at default position
                pass
            
            # 🔧 CRITICAL: Force immediate display with multiple update calls
            # This ensures splash screen is visible on all systems (Windows/Linux/Mac)
            self.root.deiconify()
            self.root.update_idletasks()  # Process pending events first
            self.root.update()  # Force immediate redraw
            self.root.lift()  # Bring window to front (above other windows)
            try:
                self.root.focus_force()  # Ensure window has focus (may fail on some systems)
            except:
                pass  # focus_force may fail on some systems, that's okay
            
            # Additional visibility updates (handles timing issues on some systems)
            try:
                self.root.after(10, lambda: self.root.update_idletasks())
                self.root.after(20, lambda: self.root.update())
                self.root.after(50, lambda: self.root.lift())
            except:
                pass  # After callbacks are optional
            
        except Exception as e:
            # If initialization completely fails, raise to let caller handle
            raise Exception(f"Splash screen initialization failed: {e}")
    
    def setup_window(self):
        """Configure window properties with robust error handling"""
        try:
            self.root.title("Sportsape BitBot Checker")
        except:
            pass
        
        try:
            self.root.geometry(f"{self.width}x{self.height}")
        except:
            pass
        
        # Remove window decorations for elegant look (optional - continue if fails)
        try:
            self.root.overrideredirect(True)
        except:
            pass  # Some systems may not support this
        
        # Set window properties
        try:
            self.root.configure(bg='#0c1b26')
        except:
            pass
        
        # Keep on top (optional - continue if fails)
        try:
            self.root.attributes('-topmost', True)
        except:
            pass  # Some systems may not support this
        
        # Set icon if available (works in EXE and dev) - CRITICAL for proper branding
        try:
            icon_path = resource_path('Assets/balance_icon.ico')
            if os.path.exists(icon_path):
                try:
                    # Method 1: iconbitmap (Windows .ico file) - for window title bar
                    self.root.iconbitmap(icon_path)
                    
                    # Method 2: iconphoto (more reliable for taskbar on some systems)
                    try:
                        from PIL import Image, ImageTk
                        img = Image.open(icon_path)
                        # Resize to standard taskbar icon size
                        img = img.resize((32, 32), Image.Resampling.LANCZOS)
                        icon_photo = ImageTk.PhotoImage(img)
                        self.root.iconphoto(True, icon_photo)  # True = set as default for all windows
                        # Keep reference to prevent garbage collection
                        self._icon_photo = icon_photo
                    except:
                        pass  # PIL method is optional
                except:
                    pass  # Icon is optional
        except:
            pass  # Resource path may fail, that's okay
    
    def center_window(self):
        """Center window on screen with robust error handling"""
        try:
            self.root.update_idletasks()
            
            # Get screen dimensions
            try:
                screen_width = self.root.winfo_screenwidth()
                screen_height = self.root.winfo_screenheight()
            except:
                # Fallback to default screen size
                screen_width = 1920
                screen_height = 1080
            
            # Calculate position
            x = (screen_width - self.width) // 2
            y = (screen_height - self.height) // 2
            
            # Ensure coordinates are valid
            x = max(0, x)
            y = max(0, y)
            
            try:
                self.root.geometry(f"{self.width}x{self.height}+{x}+{y}")
            except:
                pass  # Geometry setting is optional
        except:
            pass  # Centering is optional - window will appear at default position
    
    def create_ui(self):
        """Create splash screen UI - clean SportPesa branded"""
        N  = '#0c1b26'   # navy bg
        P  = '#14303f'   # panel
        G  = '#ffb200'   # gold accent
        GD = '#d49900'   # gold dark
        W  = '#ffffff'   # white
        M  = '#7d98a8'   # muted

        # Container
        container = tk.Frame(self.root, bg=P, highlightthickness=1,
                             highlightbackground=G, highlightcolor=G)
        container.pack(fill='both', expand=True, padx=2, pady=2)

        inner = tk.Frame(container, bg=N)
        inner.pack(fill='both', expand=True, padx=28, pady=20)

        # Top gold line
        tk.Frame(inner, bg=G, height=2).pack(fill='x', pady=(0, 10))

        # Logo
        self._build_logo(inner, N, G, W)

        # Title
        tk.Label(inner, text="Sportsape BitBot", font=('Segoe UI', 24, 'bold'),
                 bg=N, fg=W).pack(pady=(12, 2))

        # Subtitle
        tk.Label(inner, text="SportPesa Kenya Balance Checker", font=('Segoe UI', 10),
                 bg=N, fg=M).pack(pady=(2, 20))

        # Progress bar
        style = ttk.Style()
        style.theme_use('default')
        style.configure("Splash.Horizontal.TProgressbar",
                         troughcolor=P, bordercolor=G, background=G,
                         lightcolor=G, darkcolor=GD, thickness=14)
        self.progress_bar = ttk.Progressbar(
            inner, style="Splash.Horizontal.TProgressbar",
            variable=self.progress_var, maximum=100, mode='determinate', length=410)
        self.progress_bar.pack(pady=(0, 8))

        # Status
        self.status_label = tk.Label(inner, textvariable=self.status_var,
                                     font=('Consolas', 9),
                                     bg=N, fg=G, wraplength=410, height=2)
        self.status_label.pack(pady=(2, 10))

        # Footer
        tk.Label(inner, text=f"v{APP_VERSION}  ·  API Fast-Path  ·  Secure",
                 font=('Segoe UI', 8), bg=N, fg=M).pack(side='bottom', pady=(4, 0))

        # Bottom gold line
        tk.Frame(inner, bg=G, height=2).pack(side='bottom', fill='x', pady=(6, 0))

    def _build_logo(self, parent, navy, gold, white):
        """Render the app icon or a stylized fallback logo."""
        frame = tk.Frame(parent, bg=navy)
        frame.pack(pady=(6, 0))

        logo_path = resource_path('Assets/balance_icon.png')
        if os.path.exists(logo_path):
            try:
                from PIL import Image, ImageTk
                img = Image.open(logo_path)
                img.thumbnail((88, 88), Image.Resampling.LANCZOS)
                photo = ImageTk.PhotoImage(img)

                ring = tk.Frame(frame, bg=gold, highlightbackground=gold, highlightthickness=1)
                ring.pack(ipadx=4, ipady=4)
                lbl = tk.Label(ring, image=photo, bg=navy, borderwidth=0, highlightthickness=0)
                lbl.image = photo
                lbl.pack(padx=3, pady=3)
                return
            except (ImportError, Exception):
                pass

        # Stylized fallback
        c = tk.Frame(frame, bg=navy)
        c.pack()
        tk.Label(c, text="SB", font=('Arial Black', 36, 'bold'),
                 bg=navy, fg='#06233a').place(x=2, y=2)
        tk.Label(c, text="SB", font=('Arial Black', 36, 'bold'),
                 bg=navy, fg=gold).pack()
        tk.Frame(c, bg=gold, height=2).pack(fill='x', pady=4)

    
    def update_progress(self, value, status=""):
        """
        Update progress bar and status with robust error handling
        
        Args:
            value: Progress value (0-100)
            status: Status message
        """
        try:
            # Safely update progress variable
            if hasattr(self, 'progress_var'):
                try:
                    self.progress_var.set(value)
                except:
                    pass
            
            # Safely update status
            if status and hasattr(self, 'status_var'):
                try:
                    self.status_var.set(status)
                except:
                    pass
            
            # Safely update UI
            if hasattr(self, 'root') and self.root:
                try:
                    self.root.update()
                except:
                    # If update fails, try update_idletasks as fallback
                    try:
                        self.root.update_idletasks()
                    except:
                        pass
        except:
            pass  # Fail silently - progress update is not critical
    
    def complete(self, delay=0.5):
        """
        Mark loading as complete and close splash
        
        Args:
            delay: Delay before closing (seconds)
        """
        self.is_complete = True
        self.update_progress(100, "✅ Ready!")
        time.sleep(delay)
        self.close()
    
    def create_minimal_ui(self):
        """Create minimal UI if full UI creation fails (fallback)"""
        try:
            N, G = '#0c1b26', '#ffb200'
            tk.Label(self.root, text="Sportsape BitBot", font=('Segoe UI', 20, 'bold'),
                     bg=N, fg=G).pack(pady=50)
            self.status_label = tk.Label(self.root, textvariable=self.status_var,
                                         font=('Segoe UI', 10), bg=N, fg='#ffffff')
            self.status_label.pack(pady=20)
            self.progress_bar = ttk.Progressbar(self.root, variable=self.progress_var,
                                                maximum=100, length=300)
            self.progress_bar.pack(pady=10)
        except:
            pass
    
    def close(self):
        """Close splash screen with robust error handling"""
        try:
            if hasattr(self, 'root') and self.root:
                try:
                    # Only destroy, don't quit (quit would affect parent window if it's Tk())
                    # Since this is a Toplevel, destroy is safe and won't affect main window
                    self.root.destroy()
                except:
                    pass
        except:
            pass  # Fail silently - splash close is not critical
    
    def animate_loading(self, duration=3.0, steps=None):
        """
        Animate progress bar smoothly
        
        Args:
            duration: Total duration in seconds
            steps: List of (progress, status) tuples
        """
        if steps is None:
            # Default loading steps
            steps = [
                (15, "Loading core modules..."),
                (30, "Initializing AI engine..."),
                (45, "Loading configuration..."),
                (60, "Setting up session manager..."),
                (75, "Preparing UI components..."),
                (90, "Finalizing initialization..."),
                (100, "✅ Ready!")
            ]
        
        total_steps = len(steps)
        step_duration = duration / total_steps
        
        for progress, status in steps:
            if self.is_complete:
                break
            
            # Smooth animation to target progress
            current = self.progress_var.get()
            increment = (progress - current) / 10
            
            for _ in range(10):
                if self.is_complete:
                    break
                current += increment
                self.update_progress(current, status)
                time.sleep(step_duration / 10)
        
        if not self.is_complete:
            self.complete()


def show_splash_screen(loading_function=None, duration=3.0):
    """
    Show splash screen while loading application
    
    Args:
        loading_function: Optional function to run during loading
        duration: Loading duration in seconds (if no loading_function)
    
    Returns:
        The function's return value (if loading_function provided)
    """
    splash = SplashScreen()
    result = None
    
    def loading_worker():
        nonlocal result
        if loading_function:
            # Run actual loading function
            result = loading_function()
            splash.complete()
        else:
            # Just animate for specified duration
            splash.animate_loading(duration)
    
    # Start loading in background thread
    loading_thread = threading.Thread(target=loading_worker, daemon=True)
    loading_thread.start()
    
    # Run splash screen event loop
    splash.root.mainloop()
    
    # Wait for loading to complete
    loading_thread.join(timeout=10)
    
    return result


# Example usage for testing
if __name__ == "__main__":
    def mock_loading():
        """Mock loading function for testing"""
        import time
        steps = [
            (20, "Loading modules..."),
            (40, "Initializing AI..."),
            (60, "Setting up database..."),
            (80, "Preparing UI..."),
            (100, "✅ Complete!")
        ]
        
        for progress, status in steps:
            # Get splash instance and update
            # (In real use, you'd pass splash as parameter)
            time.sleep(0.5)
        
        return "Loading Complete!"
    
    # Test splash screen
    print("Showing splash screen...")
    result = show_splash_screen(duration=4.0)
    print(f"Result: {result}")
    print("Splash screen closed!")
