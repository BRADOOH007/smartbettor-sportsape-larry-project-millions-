#!/usr/bin/env python3
"""
Winbetin Balance Checker - Elegant Loading Splash Screen
Displays a professional loading screen while the application initializes
"""
import tkinter as tk
from tkinter import ttk
import threading
import time
import os
from resource_path import resource_path

WINDOWS_APP_ID = "WinbetinBalanceChecker.Splash.v5"



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
            self.width = 480
            self.height = 380
            
            # 🔧 ROBUST: Setup window with error handling
            try:
                self.setup_window()
            except Exception as setup_err:
                # Minimal setup if full setup fails
                self.root.title("Winbetin Balance Checker")
                self.root.geometry(f"{self.width}x{self.height}")
                self.root.configure(bg='#0a0a0a')
            
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
            self.root.title("Winbetin Balance Checker")
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
            self.root.configure(bg='#0a0a0a')
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
        """Create splash screen UI"""
        # Main container with border
        container = tk.Frame(
            self.root,
            bg='#1a1a1a',
            highlightthickness=2,
            highlightbackground='#00ff00',
            highlightcolor='#00ff00'
        )
        container.pack(fill='both', expand=True, padx=2, pady=2)
        
        # Inner frame
        inner_frame = tk.Frame(container, bg='#0a0a0a')
        inner_frame.pack(fill='both', expand=True, padx=20, pady=15)
        
        # Logo section - smaller to make room for text
        self.create_logo_section(inner_frame)
        
        # Title - compact size
        title_label = tk.Label(
            inner_frame,
            text="⚡ WINBETIN",
            font=('Arial', 22, 'bold'),
            bg='#0a0a0a',
            fg='#00ff00'
        )
        title_label.pack(pady=(10, 5))
        
        # Subtitle - more visible color
        subtitle_label = tk.Label(
            inner_frame,
            text="Automated Balance Checking",
            font=('Arial', 9),
            bg='#0a0a0a',
            fg='#00aa00'
        )
        subtitle_label.pack(pady=(0, 15))
        
        # Progress bar frame
        progress_frame = tk.Frame(inner_frame, bg='#0a0a0a')
        progress_frame.pack(fill='x', pady=(0, 10))
        
        # Custom styled progress bar
        style = ttk.Style()
        style.theme_use('default')
        style.configure(
            "Elegant.Horizontal.TProgressbar",
            troughcolor='#1a1a1a',
            bordercolor='#00ff00',
            background='#00ff00',
            lightcolor='#00ff00',
            darkcolor='#00aa00',
            thickness=25
        )
        
        self.progress_bar = ttk.Progressbar(
            progress_frame,
            style="Elegant.Horizontal.TProgressbar",
            variable=self.progress_var,
            maximum=100,
            mode='determinate',
            length=400
        )
        self.progress_bar.pack(pady=10)
        
        # Status label - LARGER and BRIGHTER for visibility with more space
        self.status_label = tk.Label(
            inner_frame,
            textvariable=self.status_var,
            font=('Arial', 10, 'bold'),
            bg='#0a0a0a',
            fg='#00ff00',  # Bright green
            wraplength=420,  # Wrap text if too long
            height=2  # Reserve space for 2 lines
        )
        self.status_label.pack(pady=(5, 15))
        
        # Footer with version - brighter text
        footer_label = tk.Label(
            inner_frame,
            text="v5.0.0 | AI-Powered | Secure",
            font=('Arial', 8),
            bg='#0a0a0a',
            fg='#00aa00'
        )
        footer_label.pack(side='bottom', pady=(5, 0))
    
    def create_logo_section(self, parent):
        """Create professional logo section (image or stylized text)"""
        logo_frame = tk.Frame(parent, bg='#0a0a0a')
        logo_frame.pack(pady=(0, 0))
        
        # Try to load logo image (works in EXE and dev)
        logo_path = resource_path('Assets/balance_icon.png')
        if os.path.exists(logo_path):
            try:
                from PIL import Image, ImageTk
                img = Image.open(logo_path)
                
                # Resize to fit professionally (very small to leave room for text)
                max_size = (60, 60)
                img.thumbnail(max_size, Image.Resampling.LANCZOS)
                
                # Create a circular mask effect (optional)
                photo = ImageTk.PhotoImage(img)
                
                # Display with minimal padding
                logo_container = tk.Frame(logo_frame, bg='#0a0a0a')
                logo_container.pack(pady=2)
                
                logo_label = tk.Label(
                    logo_container,
                    image=photo,
                    bg='#0a0a0a',
                    borderwidth=0,
                    highlightthickness=0
                )
                logo_label.image = photo  # Keep reference
                logo_label.pack()
                
                # Add glow effect with border
                border_frame = tk.Frame(
                    logo_frame, 
                    bg='#00ff00',
                    width=160,
                    height=160
                )
                border_frame.place(x=-5, y=-5)
                border_frame.lower()
                
                return
            except ImportError:
                # PIL not available, use stylized text logo
                pass
            except Exception as e:
                # Image loading failed, use fallback
                pass
        
        # Fallback: Professional stylized logo
        # Create multi-layer logo for depth
        logo_container = tk.Frame(logo_frame, bg='#0a0a0a')
        logo_container.pack(pady=10)
        
        # Shadow layer (creates depth)
        shadow_label = tk.Label(
            logo_container,
            text="⚡ WINBETIN",
            font=('Arial Black', 36, 'bold'),
            bg='#0a0a0a',
            fg='#003300'
        )
        shadow_label.place(x=2, y=2)
        
        # Main logo
        logo_main = tk.Label(
            logo_container,
            text="⚡ WINBETIN",
            font=('Arial Black', 36, 'bold'),
            bg='#0a0a0a',
            fg='#00ff00'
        )
        logo_main.pack()
        
        # Glow effect border
        glow_frame = tk.Frame(
            logo_container,
            bg='#00ff00',
            height=2
        )
        glow_frame.pack(fill='x', pady=5)
    
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
            # Minimal title
            title = tk.Label(
                self.root,
                text="⚡ WINBETIN",
                font=('Arial', 20, 'bold'),
                bg='#0a0a0a',
                fg='#00ff00'
            )
            title.pack(pady=50)
            
            # Minimal status
            self.status_label = tk.Label(
                self.root,
                textvariable=self.status_var,
                font=('Arial', 10),
                bg='#0a0a0a',
                fg='#00ff00'
            )
            self.status_label.pack(pady=20)
            
            # Minimal progress bar
            self.progress_bar = ttk.Progressbar(
                self.root,
                variable=self.progress_var,
                maximum=100,
                length=300
            )
            self.progress_bar.pack(pady=10)
        except:
            # If even minimal UI fails, just create empty window
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
