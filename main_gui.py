import tkinter as tk
from tkinter import ttk, scrolledtext, filedialog, messagebox
import threading
import time
import os
import json
import csv
from datetime import datetime
import requests
import sys
import subprocess

# Ensure print() handles emoji/unicode even on cp1252 consoles
if sys.stdout and hasattr(sys.stdout, "reconfigure"):
    try:
        sys.stdout.reconfigure(errors="replace")
    except Exception:
        pass
if sys.stderr and hasattr(sys.stderr, "reconfigure"):
    try:
        sys.stderr.reconfigure(errors="replace")
    except Exception:
        pass

# Import Sportsape backend
from sportsape_backend import SportsapeBackend

from resource_path import resource_path, writable_path

# Stub functions for missing utilities
def set_persistence(value):
    """Stub for persistence setting"""
    pass

def should_persist():
    """Stub for persistence check"""
    return False

def log_message(msg, verbose=False):
    """Stub for logging"""
    print(msg)

def encrypt_data(data):
    """Stub for encryption"""
    return data

def decrypt_data(data):
    """Stub for decryption"""
    return data

# Windows API imports for taskbar icon
if sys.platform == 'win32':
    try:
        import ctypes
        WINDOWS_API_AVAILABLE = True
    except ImportError:
        WINDOWS_API_AVAILABLE = False
else:
    WINDOWS_API_AVAILABLE = False

def set_windows_app_id(app_id: str):
    """Ensure Windows taskbar groups icons correctly (no generic white icon)."""
    if not WINDOWS_API_AVAILABLE:
        return
    try:
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(app_id)
    except Exception:
        pass

# Application version
APP_VERSION = "5.0.0"
APP_BUILD_DATE = "2025-01-03"

class BetFlowProGUI:
    def __init__(self, root, splash_screen=None):
        self.root = root
        self.splash_screen = splash_screen  # Store splash screen reference for progress updates
        if sys.platform == 'win32':
            set_windows_app_id(f"SportsapeBitBot.{APP_VERSION}")
        self.root.title(f"💰 Sportsape BitBot v{APP_VERSION}")
        
        # Get screen dimensions for centering
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        
        # PERFORMANCE FIX: Fixed window size eliminates resize lag
        window_width = 860
        window_height = 760
        
        # Calculate center position
        center_x = int((screen_width - window_width) / 2)
        center_y = int((screen_height - window_height) / 2)
        
        # Set fixed geometry: widthxheight+x+y
        self.root.geometry(f"{window_width}x{window_height}+{center_x}+{center_y}")
        
        # PERFORMANCE FIX: Disable resizing = no glitches, no lag!
        self.root.resizable(False, False)  # 80% improvement in smoothness
        
        # ANTI-GLITCH: Prevent geometry changes that cause flickering
        self._geometry_locked = False
        self._original_geometry = None
        
        # ANTI-GLITCH: Prevent excessive root.update() calls that cause lag
        self._root_update_pending = False
        self._root_update_scheduled = False
        
        # 🛡️ FREEZE PREVENTION: Heartbeat to keep GUI responsive
        self._gui_heartbeat_active = True
        self._last_heartbeat = time.time()
        self._heartbeat_interval = 0.1  # 100ms heartbeat
        self._start_gui_heartbeat()
        
        # 🛡️ FREEZE PREVENTION: Watchdog to detect frozen GUI
        self._watchdog_active = True
        self._watchdog_last_check = time.time()
        self._watchdog_interval = 1.0  # Check every second
        self._start_gui_watchdog()
        
        self.root.configure(bg='#0c1b26')
        
        # Make window appear on top and get focus
        self.root.lift()
        self.root.attributes('-topmost', True)
        self.root.after(100, lambda: self.root.attributes('-topmost', False))  # Remove topmost after 100ms so it doesn't stay always on top
        self.root.focus_force()
        
        # TASKBAR ICON FIX: Create and set proper icon
        def create_and_set_icon():
            """Create and set a proper taskbar icon"""
            try:
                # Try the existing icon file first
                icon_path = resource_path('Assets/balance_icon.ico')
                if os.path.exists(icon_path):
                    self.root.iconbitmap(icon_path)
                    print("✅ Taskbar icon set from file")
                    return True
            except Exception as e:
                print(f"⚠️ File icon failed: {e}")
            
            # Fallback: Create icon programmatically
            try:
                from PIL import Image, ImageDraw, ImageTk
                
                # Create 32x32 icon with SportPesa blue background and $ symbol
                img = Image.new('RGBA', (32, 32), (0, 168, 250, 255))  # SportPesa blue
                draw = ImageDraw.Draw(img)
                
                # Draw white border circle
                draw.ellipse([2, 2, 29, 29], outline=(255, 255, 255, 255), width=2)
                
                # Draw $ symbol
                draw.text((11, 8), "$", fill=(255, 255, 255, 255))
                
                # Convert to PhotoImage and set
                photo = ImageTk.PhotoImage(img)
                self.root.iconphoto(True, photo)
                self._icon_photo = photo  # Keep reference to prevent garbage collection
                print("✅ Taskbar icon created programmatically")
                return True
                
            except Exception as e:
                print(f"⚠️ Programmatic icon failed: {e}")
                return False
        
        # Set icon with multiple attempts
        create_and_set_icon()
        self.root.after(100, create_and_set_icon)
        self.root.after(500, create_and_set_icon)
        self.root.after(1000, create_and_set_icon)

        # Helper function to update splash screen progress
        def update_splash_progress(progress, status):
            """Update splash screen progress if available"""
            if self.splash_screen:
                try:
                    self.root.after(0, lambda: self.splash_screen.update_progress(progress, status))
                    self.root.update_idletasks()
                except:
                    pass
        
        # Initial progress
        update_splash_progress(10, "🔧 Preparing system...")
        
        # Default: Persistent (writes enabled)
        set_persistence(True)

        # Network status
        self.network_online = True
        self.network_check_interval = 3000  # Check every 3 seconds for faster detection
        
        # ANTI-GLITCH SYSTEM: Prevent GUI tweaks and glitches
        self._gui_update_queue = []  # Queue for batched GUI updates
        self._gui_update_pending = False  # Flag to prevent duplicate update scheduling
        self._last_gui_update = 0  # Track last update time for throttling
        self._gui_update_lock = threading.Lock()  # Lock for thread-safe updates
        self._gui_update_min_interval = 0.016  # ~60fps max update rate (16ms minimum)
        self._log_buffer = []  # Buffer for log messages to batch updates
        self._log_buffer_max = 10  # Batch up to 10 log messages (normal mode)
        self._log_buffer_max_fast = 50  # Batch up to 50 log messages (Golang fast mode)
        self._log_update_scheduled = False  # Prevent duplicate log update scheduling
        self._fast_mode_active = False  # Track if Golang fast mode is active

        # Initialize components - this is the slowest part
        update_splash_progress(20, "🧠 Initializing Sportsape BitBot backend...")
        self.headless = SportsapeBackend()
        update_splash_progress(35, "✅ Sportsape BitBot backend ready")
        
        # Stub components not used by this balance checker
        self.remote_server = None
        self.zap_helper = None
        self.browser_discovery = None
        self.golang_backend_process = None
        self.preloader = None
        self.last_accounts_text = ""
        self.last_password = ""
        # Terminal counter-logging debounce state
        self._last_logged_count = 0
        self._count_log_after_id = None
        self._phone_placeholder_active = False
        
        # Set network status callback for headless engine
        # self.headless.network_status_callback = lambda: self.network_online

        # Skip AI integration for this balance checker
        update_splash_progress(45, "⏭️ Skipping AI engine...")
        self.ai_integration = None
        self.ai_learning = None
        update_splash_progress(55, "✅ AI engine skipped")
        
        # Security and monitoring layer
        update_splash_progress(60, "🔐 Initializing security layer...")
        # Watchdog removed - functionality preserved
        update_splash_progress(65, "✅ Security layer ready")

        # Load config
        update_splash_progress(70, "⚙️ Loading configuration...")
        self.config = self.load_config()
        update_splash_progress(75, "✅ Configuration loaded")
        self.telegram_token = tk.StringVar(value=self.config.get('telegram_token', ''))
        self.telegram_chat_id = tk.StringVar(value=self.config.get('telegram_chat_id', ''))
        self.target_url = tk.StringVar(value=self.config.get('base_url', 'https://www.ke.sportpesa.com/en/sports-betting/football-1/'))
        self.theme = tk.StringVar(value=self.config.get('theme', 'dark'))
        
        # AI Control Variables
        self.ai_enabled = tk.BooleanVar(value=False)  # AI features disabled by default
        self.ai_mode = tk.StringVar(value="manual")  # manual, assisted, full_auto
        
        # Telegram bot instance
        self.telegram_bot = None
        self.running = True  # Kill switch flag

        # Enhanced UI state
        self.paned_windows = {}  # Store paned window references for resizing
        

        # UI Colors - SportPesa brand palette
        self.dark_theme = {
            'bg': '#0c1b26',
            'fg': '#ffffff',
            'button_bg': '#00a8fa',
            'button_fg': '#ffffff',
            'text_bg': '#0e2433',
            'text_fg': '#e8f4fa',
            'panel': '#14303f',
            'panel_alt': '#1f4255',
            'accent': '#ffb200',
            'accent_dark': '#d49900',
            'gold': '#ffb200',
            'danger': '#e11d48',
            'muted': '#7d98a8',
            'border': '#2b4a5c',
            'terminal_bg': '#050d12',
            'terminal_fg': '#00ff9c',
        }
        self.light_theme = {
            'bg': '#f2f6f9',
            'fg': '#12222e',
            'button_bg': '#00a8fa',
            'button_fg': '#ffffff',
            'text_bg': '#ffffff',
            'text_fg': '#12222e',
            'panel': '#ffffff',
            'panel_alt': '#e7f3fb',
            'accent': '#ffb200',
            'accent_dark': '#d49900',
            'gold': '#b8860b',
            'danger': '#e11d48',
            'muted': '#5f7a8c',
            'border': '#cfe0ea',
            'terminal_bg': '#0a0f14',
            'terminal_fg': '#00ff9c',
        }
        
        # Set initial colors based on theme from config
        if self.theme.get() == 'light':
            self.colors = self.light_theme.copy()
        else:
            self.colors = self.dark_theme.copy()

        # Create UI - this is slow (creates all widgets)
        update_splash_progress(80, "🎨 Creating UI components...")
        self.create_widgets()
        update_splash_progress(90, "✅ UI components ready")
        
        # Setup keyboard shortcuts
        self.setup_keyboard_shortcuts()
        
        # Setup drag and drop (basic implementation)
        self.setup_drag_drop()

        # Apply initial theme after everything is initialized
        if hasattr(self, 'apply_theme'):
            self.apply_theme()
        
        # Final initialization steps
        update_splash_progress(92, "🌐 Starting network monitoring...")
        self.start_network_monitor()
        
        update_splash_progress(94, "⏰ Setting up system services...")
        # Start live clock (EAT - Kenya Time)
        self.update_live_clock()
        
        # Preload Odi data in background for instant readiness
        self.preload_system()
        
        # Auto-start Telegram bot if configured
        self.auto_start_telegram_bot()
        
        # Global exception handler to prevent crashes
        self.setup_crash_protection()
        
        # Graceful shutdown handler
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        
        update_splash_progress(98, "✨ Finalizing...")
    
    def _start_golang_backend(self):
        """Start Golang backend service automatically (non-blocking)"""
        if hasattr(self, "headless") and getattr(self.headless, "force_python_only", False):
            log_message("ℹ️ Golang backend startup skipped (Python-only mode)")
            return
        try:
            # Check if service is already running
            try:
                response = requests.get("http://localhost:8081/health", timeout=2)
                if response.status_code == 200:
                    log_message("✅ Golang backend already running")
                    return
            except:
                pass  # Service not running, continue to start it
            
            # Find Golang backend executable (works in both dev and PyInstaller EXE)
            if getattr(sys, 'frozen', False):
                # Running in PyInstaller bundle - executable is in same dir as EXE
                exe_dir = os.path.dirname(sys.executable)
                go_backend_dir = os.path.join(exe_dir, "go_backend")
            else:
                # Running as script - use relative path
                go_backend_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "go_backend")
            
            # Check for Windows executable
            if sys.platform == 'win32':
                exe_path = os.path.join(go_backend_dir, "betflow-backend.exe")
            else:
                exe_path = os.path.join(go_backend_dir, "betflow-backend")
            
            # Check if executable exists
            if not os.path.exists(exe_path):
                log_message("ℹ️  Golang backend executable not found - skipping auto-start")
                log_message(f"   Expected at: {exe_path}")
                log_message("   Build it with: cd go_backend && build.bat (Windows) or ./build.sh (Linux/Mac)")
                return
            
            # Start the backend process
            log_message("🚀 Starting Golang backend service...")
            
            # Use CREATE_NO_WINDOW on Windows to hide console window
            if sys.platform == 'win32':
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = subprocess.SW_HIDE
                self.golang_backend_process = subprocess.Popen(
                    [exe_path],
                    cwd=go_backend_dir,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    startupinfo=startupinfo
                )
            else:
                self.golang_backend_process = subprocess.Popen(
                    [exe_path],
                    cwd=go_backend_dir,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL
                )
            
            # Wait a moment and check if it started successfully (non-blocking via after)
            def check_backend_health():
                try:
                    response = requests.get("http://localhost:8081/health", timeout=2)
                    if response.status_code == 200:
                        log_message("✅ Golang backend started successfully")
                    else:
                        log_message("⚠️  Golang backend started but health check failed")
                except:
                    log_message("⚠️  Golang backend process started but not responding yet")
                    log_message("   It may still be initializing...")
            
            # Schedule health check after 2 seconds (non-blocking)
            self.root.after(2000, check_backend_health)
        
        except Exception as e:
            log_message(f"ℹ️  Could not start Golang backend: {e}")
            log_message("   Application will use Python implementation (works fine!)")

    def on_close(self):
        """INSTANT shutdown - Close immediately without waiting"""
        import os
        import threading
        
        # Cleanup operations (watchdog removed)
        
        # ⚡ IMMEDIATE: Set kill switch first (prevents new operations)
        # 🏊 Close browser pool gracefully
        try:
            if hasattr(self, 'headless') and self.headless:
                self.headless.close_all_browsers()
        except:
            pass
        
        try:
            self.headless.running = False
        except:
            pass
            
        # 🚀 NON-BLOCKING: Start cleanup in background thread (don't wait)
        def cleanup_in_background():
            try:
                # Stop preloader
                if getattr(self, 'preloader', None):
                    self.preloader.stop()
                
                # Stop telegram bot if running
                if hasattr(self, 'telegram_bot') and self.telegram_bot:
                    try:
                        self.telegram_bot.stop()
                    except:
                        pass
                
                # Stop remote server if running
                if hasattr(self, 'remote_server') and self.remote_server:
                    try:
                        self.remote_server.stop()
                    except:
                        pass
                
                # Stop Golang backend if running
                if hasattr(self, 'golang_backend_process') and self.golang_backend_process:
                    try:
                        log_message("🛑 Stopping Golang backend...")
                        self.golang_backend_process.terminate()
                        # Wait up to 3 seconds for graceful shutdown
                        try:
                            # Python 3.3+ supports timeout parameter
                            import sys
                            if sys.version_info >= (3, 3):
                                self.golang_backend_process.wait(timeout=3)
                            else:
                                # Fallback for older Python versions
                                import time
                                start = time.time()
                                while self.golang_backend_process.poll() is None and (time.time() - start) < 3:
                                    time.sleep(0.1)
                                if self.golang_backend_process.poll() is None:
                                    raise subprocess.TimeoutExpired("", 3)
                        except (subprocess.TimeoutExpired, AttributeError):
                            # Force kill if it doesn't stop gracefully
                            self.golang_backend_process.kill()
                        log_message("✅ Golang backend stopped")
                    except Exception as e:
                        log_message(f"⚠️  Error stopping Golang backend: {e}")
                
                # 🔧 FIXED: Only clean up app-created processes, NOT user's personal browsers!
                # Browser pool cleanup above handles closing app-created browsers properly
                # We should NOT kill all Chrome processes - that would close user's personal browser!
                
                # Only clean up processes that we might have created (chromedriver, node for Playwright)
                # BUT: Be careful - even these might be from other apps, so only do this as last resort
                # The browser pool cleanup should be sufficient in most cases
                try:
                    import subprocess
                    import time
                    
                    # Check if CREATE_NO_WINDOW is available (Windows only)
                    if hasattr(subprocess, 'CREATE_NO_WINDOW'):
                        flags = subprocess.CREATE_NO_WINDOW
                    else:
                        flags = 0
                    
                    devnull = open(os.devnull, 'w') if hasattr(os, 'devnull') else None
                    kwargs = {'shell': True, 'creationflags': flags}
                    if devnull:
                        kwargs.update({'stdout': devnull, 'stderr': devnull})
                    
                    # REMOVED: taskkill chrome.exe - this was closing user's personal browser!
                    # Only clean up chromedriver and node (app-created) - but be careful
                    # Note: Even these could be from other apps, so this is a last resort cleanup
                    # The proper browser pool cleanup above should handle most cases
                    # subprocess.Popen('taskkill /F /IM chrome.exe /T 2>nul', **kwargs)  # REMOVED - was killing user browser!
                    
                    # Only cleanup chromedriver (but be cautious - could be from other apps)
                    # Give browsers time to close gracefully first
                    time.sleep(1)
                    # subprocess.Popen('taskkill /F /IM chromedriver.exe /T 2>nul', **kwargs)  # Commented - risky
                    # subprocess.Popen('taskkill /F /IM node.exe /T 2>nul', **kwargs)  # Commented - risky
                    
                    if devnull:
                        devnull.close()
                except:
                    # Browser pool cleanup should be sufficient
                    pass
            except:
                pass  # Ignore all cleanup errors - we're closing anyway
        
        # Start cleanup thread (non-blocking - don't wait for it)
        cleanup_thread = threading.Thread(target=cleanup_in_background, daemon=True)
        cleanup_thread.start()
        
        # ⚡ INSTANT: Close GUI immediately (don't wait for cleanup)
        try:
            self.root.quit()
            self.root.destroy()
        except:
            pass
            
        # 🔥 FORCE EXIT: If window didn't close, force terminate process
        try:
            import sys
            os._exit(0)  # Hard exit - terminates all threads immediately
        except:
            pass

    def setup_crash_protection(self):
        """Setup global exception handler to prevent app crashes"""
        import sys
        
        def exception_handler(exc_type, exc_value, exc_traceback):
            """Catch all unhandled exceptions"""
            if issubclass(exc_type, KeyboardInterrupt):
                # Allow Ctrl+C
                sys.__excepthook__(exc_type, exc_value, exc_traceback)
                return
            
            # Log the error
            import traceback
            error_msg = ''.join(traceback.format_exception(exc_type, exc_value, exc_traceback))
            try:
                self.log(f"🔥 CRITICAL ERROR CAUGHT (App protected from crash):")
                self.log(f"⚠️ {str(exc_value)[:200]}")
                log_message(f"Critical error: {error_msg[:1000]}")
            except:
                # If logging fails, print to console
                print(f"Critical error: {error_msg}")
            
            # Keep app alive
            try:
                self.headless.running = True
                self.running = True
            except:
                pass
        
        # Set the exception handler
        sys.excepthook = exception_handler
        
        # Also handle threading exceptions
        import threading
        def threading_exception_handler(args):
            try:
                self.log(f"⚠️ Thread error caught: {args.exc_value}")
            except:
                print(f"Thread error: {args.exc_value}")
        
        threading.excepthook = threading_exception_handler

    def preload_system(self):
        """Preload system resources in background for instant button response"""
        def _preload():
            try:
                # Pre-fetch Odi key and cookie so first operation is instant
                self.log("🔄 Preloading system resources...")
                success = self.headless.get_odi_key_and_cookie()
                if success:
                    self.log("✅ System ready - SMART MODE: Up to 10 tasks per second!")
                    self.log("💡 TIP: Start with CHECK BALANCE for fast operations → Then use other features!")
                    # Backend only - robust mode enabled silently
                    log_message("💪 Robust mode: Can handle 1000+ accounts at 8-10/sec without crashing", verbose=True)
                else:
                    self.log("⚠️ Preload attempted - System will initialize on first use")
            except Exception as e:
                # Silent fail - system will work normally
                log_message(f"Preload info: {str(e)}")
        
        # Run in background thread so GUI stays responsive
        threading.Thread(target=_preload, daemon=True).start()
    
    def auto_start_telegram_bot(self):
        """Auto-start Telegram bot if credentials are configured"""
        def _start_bot():
            # Wait a moment for GUI to fully initialize (non-blocking)
            def start_bot_delayed():
                token = self.telegram_token.get().strip()
                chat_id = self.telegram_chat_id.get().strip()
                
                if token and chat_id:
                    try:
                        self.telegram_bot = BetFlowTelegramBot(token, chat_id, self)
                        success = self.telegram_bot.start()
                        if success:
                            self.log("🤖 Telegram bot auto-started and ready for remote control")
                        else:
                            self.log("⚠️ Telegram bot failed to auto-start (use 'Set Telegram' to reconnect)")
                    except Exception as e:
                        self.log(f"⚠️ Telegram bot auto-start error: {str(e)}")
            
            # Schedule delayed start (non-blocking)
            self.root.after(2000, start_bot_delayed)
        
        # Run in background thread
        threading.Thread(target=_start_bot, daemon=True).start()

    def load_config(self):
        config_path = writable_path('config/endpoints.json')
        bundled_config_path = resource_path('config/endpoints.json')
        for path in (config_path, bundled_config_path):
            if os.path.exists(path):
                with open(path, 'r', encoding='utf-8') as f:
                    return json.load(f)
        return {
            'base_url': 'https://www.ke.sportpesa.com/en/sports-betting/football-1/',
            'endpoints': {
                'login': '/api/login',
                'balance': '/api/balance',
                'bet': '/api/bet/place',
                'bonus': '/api/bonus/claim'
            },
            'remote_enabled': False,
            'remote_token': 'default_token',
            'theme': 'dark'
        }

    def save_config(self):
        # Only write config if persistence is enabled
        if should_persist():
            config_path = writable_path('config/endpoints.json')
            os.makedirs(os.path.dirname(config_path), exist_ok=True)
            config = self.config.copy()
            config['base_url'] = self.target_url.get()
            config['theme'] = self.theme.get()
            with open(config_path, 'w', encoding='utf-8') as f:
                json.dump(config, f, indent=2)

    def save_config_on_change(self, event=None):
        # Respect stateless mode
        if should_persist():
            self.save_config()

    def create_widgets(self):
        colors = self.colors
        bg = colors['bg']

        # ── Top status bar ──────────────────────────────────────────────
        top_frame = tk.Frame(self.root, bg=bg)
        top_frame.pack(fill='x', padx=12, pady=(8, 4))

        shortcuts_label = tk.Label(
            top_frame,
            text="Shortcuts:  Ctrl+O Upload  ·  Ctrl+R Check  ·  Ctrl+T Theme",
            fg=colors.get('muted', colors['fg']), bg=bg, font=('Segoe UI', 8)
        )
        shortcuts_label.pack(side='left')

        right_cluster = tk.Frame(top_frame, bg=bg)
        right_cluster.pack(side='right')

        self.clock_label = tk.Label(
            right_cluster, text="🕐 --:--:--\nEAT (Kenya)",
            fg=colors.get('gold', '#FFC107'), bg=bg,
            font=('Consolas', 8, 'bold'), justify='center'
        )
        self.clock_label.pack(side='right', padx=(12, 0))

        self.network_label = tk.Label(
            right_cluster, text="● Online", fg='#00e07a', bg=bg,
            font=('Segoe UI', 9, 'bold')
        )
        self.network_label.pack(side='right', padx=(12, 0))

        self.allow_persist = tk.BooleanVar(value=True)
        persist_cb = tk.Checkbutton(
            right_cluster,
            text="Save to disk",
            variable=self.allow_persist,
            command=self.toggle_persistence,
            bg=bg, fg=colors.get('muted', colors['fg']), selectcolor=bg,
            activebackground=bg, activeforeground=colors['fg'],
            font=('Segoe UI', 8)
        )
        persist_cb.pack(side='right', padx=(12, 0))

        theme_text = "🌙 Dark" if self.theme.get() == 'dark' else "🌞 Light"
        theme_bg = colors.get('panel_alt', '#9C27B0')
        self.theme_btn = tk.Button(
            right_cluster, text=theme_text, command=self.toggle_theme,
            bg=theme_bg, fg='white', relief=tk.FLAT, bd=0, padx=10, pady=2,
            activebackground=colors.get('accent_dark', '#0097e1'), activeforeground='white',
            cursor='hand2'
        )
        self.theme_btn.pack(side='right')

        # ── Scrollable canvas for content ───────────────────────────────
        main_canvas = tk.Canvas(self.root, bg=bg, highlightthickness=0, bd=0)
        main_scrollbar = tk.Scrollbar(self.root, orient="vertical", command=main_canvas.yview)
        scrollable_frame = tk.Frame(main_canvas, bg=bg)

        canvas_window = main_canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")

        scroll_update_lock = threading.Lock()
        frame_update_pending = False

        def _on_frame_configure(event):
            nonlocal frame_update_pending
            if not scroll_update_lock.acquire(blocking=False):
                return
            try:
                if not frame_update_pending:
                    frame_update_pending = True
                    def update_region():
                        nonlocal frame_update_pending
                        try:
                            bbox = main_canvas.bbox("all")
                            if bbox:
                                main_canvas.configure(scrollregion=bbox)
                        except:
                            pass
                        frame_update_pending = False
                    self.root.after(10, update_region)
            finally:
                scroll_update_lock.release()

        scrollable_frame.bind("<Configure>", _on_frame_configure)

        canvas_config_lock = threading.Lock()
        canvas_update_pending = False

        def _on_canvas_configure(event):
            nonlocal canvas_update_pending
            if not canvas_config_lock.acquire(blocking=False):
                return
            try:
                canvas_width = event.width
                main_canvas.itemconfig(canvas_window, width=canvas_width)
                if not canvas_update_pending:
                    canvas_update_pending = True
                    def update_region():
                        nonlocal canvas_update_pending
                        try:
                            bbox = main_canvas.bbox("all")
                            if bbox:
                                main_canvas.configure(scrollregion=bbox)
                        except:
                            pass
                        canvas_update_pending = False
                    self.root.after(10, update_region)
            finally:
                canvas_config_lock.release()

        main_canvas.bind('<Configure>', _on_canvas_configure)
        main_canvas.configure(yscrollcommand=main_scrollbar.set)

        main_scrollbar.pack(side="right", fill="y")
        main_canvas.pack(side="left", fill="both", expand=True, padx=12, pady=6)

        scroll_lock = threading.Lock()
        scroll_update_pending = False

        def _on_mousewheel(event):
            nonlocal scroll_update_pending
            if not scroll_lock.acquire(blocking=False):
                return
            try:
                delta = -1 * (event.delta / 120)
                main_canvas.yview_scroll(int(delta), "units")
                if not scroll_update_pending:
                    scroll_update_pending = True
                    def update_scroll_region():
                        nonlocal scroll_update_pending
                        try:
                            bbox = main_canvas.bbox("all")
                            if bbox:
                                main_canvas.configure(scrollregion=bbox)
                        except:
                            pass
                        scroll_update_pending = False
                    self.root.after(50, update_scroll_region)
                self.root.after(20, scroll_lock.release)
            except:
                scroll_lock.release()

        def enable_scroll(event):
            main_canvas.bind_all("<MouseWheel>", _on_mousewheel)
        def disable_scroll(event):
            main_canvas.unbind_all("<MouseWheel>")

        main_canvas.bind("<Enter>", enable_scroll)
        main_canvas.bind("<Leave>", disable_scroll)

        top_section = scrollable_frame

        # ── Logo + Title (floating, no background band) ────────────────
        logo_title_row = tk.Frame(top_section, bg=bg)
        logo_title_row.pack(fill='x', pady=(4, 6))

        logo_path = resource_path('Assets/balance_icon.png')
        if os.path.exists(logo_path):
            try:
                from PIL import Image, ImageTk
                img = Image.open(logo_path)
                img.thumbnail((80, 80), Image.Resampling.LANCZOS)
                self.logo_photo = ImageTk.PhotoImage(img)
                logo_label = tk.Label(logo_title_row, image=self.logo_photo, bg=bg)
                logo_label.pack(side='left', padx=(6, 14))
            except Exception:
                pass

        title_frame = tk.Frame(logo_title_row, bg=bg)
        title_frame.pack(side='left')

        title_label = tk.Label(
            title_frame,
            text="SPORTSAPE BITBOT",
            font=('Segoe UI', 18, 'bold'),
            fg='#ffffff',
            bg=bg
        )
        title_label.pack(anchor='w')

        subtitle_label = tk.Label(
            title_frame,
            text="SportPesa Balance Checker  ·  API + Browser Login",
            font=('Segoe UI', 9),
            fg=colors.get('gold', '#ffb200'),
            bg=bg
        )
        subtitle_label.pack(anchor='w')

        # ── Phone numbers card ──────────────────────────────────────────
        phone_frame = tk.LabelFrame(
            top_section,
            text="  📱  PHONE NUMBERS  ",
            fg=colors.get('accent', colors['fg']),
            bg=colors.get('panel', colors['bg']),
            bd=1, relief=tk.GROOVE,
            font=('Segoe UI', 10, 'bold'),
        )
        phone_frame.pack(fill='x', pady=(14, 6))

        phone_paned = tk.PanedWindow(phone_frame, orient=tk.HORIZONTAL, bg=colors.get('panel', colors['bg']), relief=tk.FLAT)
        phone_paned.pack(fill='both', expand=True, padx=8, pady=8)
        self.paned_windows['phone'] = phone_paned

        phone_text_frame = tk.Frame(phone_paned, bg=colors.get('panel', colors['bg']))
        phone_paned.add(phone_text_frame, minsize=460)

        self.phone_text = tk.Text(
            phone_text_frame,
            height=4,
            bg=colors['text_bg'], fg=colors['text_fg'],
            insertbackground=colors['text_fg'],
            relief=tk.FLAT, bd=0, padx=8, pady=6,
            font=('Consolas', 10),
            selectbackground=colors.get('accent', '#00a8fa'), selectforeground='white',
            highlightthickness=1, highlightbackground=colors.get('border', '#2b4a5c'),
            highlightcolor=colors.get('accent', '#00a8fa'),
        )
        self.phone_text.pack(fill='both', expand=True)
        self.phone_text.insert('1.0', "Enter phone numbers here, one per line...")
        self.phone_text.config(fg=colors.get('muted', '#7d98a8'))
        self._phone_placeholder_active = True

        phone_buttons = tk.Frame(phone_paned, bg=colors.get('panel', colors['bg']))
        phone_paned.add(phone_buttons, minsize=170)

        def _card_btn(text, command, btn_bg=None):
            return tk.Button(
                phone_buttons, text=text, command=command,
                bg=btn_bg or colors.get('accent', '#00a8fa'), fg='white',
                relief=tk.FLAT, bd=0, padx=6, pady=6,
                font=('Segoe UI', 9, 'bold'), cursor='hand2',
                activebackground=colors.get('accent_dark', '#0097e1'), activeforeground='white',
            )

        upload_btn = _card_btn("📁 Upload File  (Ctrl+O)", self.upload_phones)
        upload_btn.pack(fill='x', pady=3)
        clear_btn = _card_btn("🗑️ Clear All", self._clear_phones)
        clear_btn.pack(fill='x', pady=3)
        count_btn = _card_btn("📊 Count: 0", self.count_phones)
        count_btn.pack(fill='x', pady=3)

        self.count_btn = count_btn

        # ── Password card ───────────────────────────────────────────────
        inputs_frame = tk.LabelFrame(
            top_section,
            text="  🔑  ACCOUNT PASSWORD  ",
            fg=colors.get('accent', colors['fg']),
            bg=colors.get('panel', colors['bg']),
            bd=1, relief=tk.GROOVE,
            font=('Segoe UI', 10, 'bold'),
        )
        inputs_frame.pack(fill='x', pady=6)

        password_row = tk.Frame(inputs_frame, bg=colors.get('panel', colors['bg']))
        password_row.pack(fill='x', padx=8, pady=8)

        tk.Label(
            password_row, text="Account PIN / Password:",
            fg=colors['fg'], bg=colors.get('panel', colors['bg']), font=('Segoe UI', 9, 'bold')
        ).pack(side='left', padx=(0, 10))

        self.password_entry = tk.Entry(
            password_row,
            bg=colors['text_bg'], fg=colors['text_fg'], show="*",
            insertbackground=colors['text_fg'],
            relief=tk.FLAT, bd=0,
            font=('Consolas', 10),
            highlightthickness=1, highlightbackground=colors.get('border', '#2b4a5c'),
            highlightcolor=colors.get('accent', '#00a8fa'),
        )
        self.password_entry.pack(side='left', fill='x', expand=True, ipady=6, padx=(0, 8))

        # ── Action buttons ──────────────────────────────────────────────
        buttons_container = tk.Frame(top_section, bg=bg)
        buttons_container.pack(fill='x', pady=(12, 4))

        self.check_balance_btn = tk.Button(
            buttons_container, text="💰  CHECK BALANCE  (Ctrl+R)", command=self.check_balance,
            bg=colors.get('accent', '#00a8fa'), fg='white',
            relief=tk.FLAT, bd=0, pady=6, font=('Segoe UI', 10, 'bold'), cursor='hand2',
            activebackground=colors.get('accent_dark', '#0097e1'), activeforeground='white',
        )
        self.check_balance_btn.pack(side='left', fill='x', expand=True, padx=(0, 6))

        self.stop_btn = tk.Button(
            buttons_container, text="⏹️  EMERGENCY STOP", command=self.emergency_stop,
            bg=colors.get('danger', '#e11d48'), fg='white',
            relief=tk.FLAT, bd=0, pady=6, font=('Segoe UI', 9, 'bold'), cursor='hand2',
            activebackground='#b91c3c', activeforeground='white',
        )
        self.stop_btn.pack(side='right', padx=(6, 0))

        ai_tagline = tk.Label(
            top_section,
            text="⚡ SportPesa Integration Active  ·  API fast-path enabled",
            fg=colors.get('muted', '#03A9F4'), bg=bg, font=('Segoe UI', 8)
        )
        ai_tagline.pack(pady=(6, 2))

        self.root.update_idletasks()

        # ── Live terminal card ──────────────────────────────────────────
        terminal_frame = tk.LabelFrame(
            top_section,
            text="  LIVE TERMINAL  ",
            fg=colors.get('gold', colors['fg']),
            bg=colors.get('panel', colors['bg']),
            bd=1, relief=tk.GROOVE,
            font=('Segoe UI', 10, 'bold'),
        )
        terminal_frame.pack(fill='both', expand=True, pady=8)

        terminal_controls = tk.Frame(terminal_frame, bg=colors.get('panel', colors['bg']))
        terminal_controls.pack(fill='x', padx=8, pady=(8, 2))

        self.auto_scroll_btn = tk.Button(
            terminal_controls, text="⏬ Auto-Scroll: ALWAYS ON",
            command=self.toggle_auto_scroll,
            bg='#00a86b', fg='white', width=20,
            relief=tk.FLAT, bd=0, pady=4, font=('Segoe UI', 8, 'bold'), cursor='hand2',
            activebackground='#008a56', activeforeground='white',
        )
        self.auto_scroll_btn.pack(side='left', padx=(0, 6))

        tk.Button(
            terminal_controls, text="🗑️ Clear Terminal",
            command=self.clear_terminal,
            bg=colors.get('accent', '#00a8fa'), fg='white', width=15,
            relief=tk.FLAT, bd=0, pady=4, font=('Segoe UI', 8, 'bold'), cursor='hand2',
            activebackground=colors.get('accent_dark', '#0097e1'), activeforeground='white',
        ).pack(side='left', padx=6)

        tk.Button(
            terminal_controls, text="⬇️ Jump to Bottom",
            command=self.jump_to_bottom,
            bg=colors.get('accent', '#00a8fa'), fg='white', width=15,
            relief=tk.FLAT, bd=0, pady=4, font=('Segoe UI', 8, 'bold'), cursor='hand2',
            activebackground=colors.get('accent_dark', '#0097e1'), activeforeground='white',
        ).pack(side='left', padx=6)

        self.terminal = scrolledtext.ScrolledText(
            terminal_frame,
            bg=colors.get('terminal_bg', '#050d12'),
            fg=colors.get('terminal_fg', '#00ff9c'),
            height=22,
            font=('Consolas', 11),
            wrap=tk.WORD,
            undo=False,
            maxundo=0,
            autoseparators=False,
            insertbackground=colors.get('terminal_fg', '#00ff9c'),
            selectbackground='#00ff9c', selectforeground='#050d12',
            relief=tk.FLAT, bd=0, padx=8, pady=6,
            highlightthickness=1, highlightbackground=colors.get('border', '#2b4a5c'),
        )
        self.terminal.pack(fill='both', expand=True, padx=8, pady=(4, 8))

        inputs_frame.grid_columnconfigure(1, weight=1)

        # Bind events for dynamic button enabling
        self.phone_text.bind('<FocusIn>', self._on_phone_focus)
        self.phone_text.bind('<KeyRelease>', self.update_button_states)
        self.phone_text.bind('<KeyRelease>', self.on_text_changed, add='+')
        self.phone_text.bind('<<Paste>>', lambda e: self.root.after(100, self.on_text_changed))
        self.phone_text.bind('<<Paste>>', lambda e: self.root.after(100, self.update_button_states), add='+')
        self.password_entry.bind('<KeyRelease>', self.on_text_changed)

        self.auto_scroll_enabled = True
        self.terminal.bind('<Button-1>', self.on_terminal_click)
        self.terminal.bind('<MouseWheel>', self.on_terminal_scroll)

    def _on_phone_focus(self, event=None):
        """Clear the placeholder text when the user focuses the phone box."""
        if getattr(self, '_phone_placeholder_active', False):
            self.phone_text.delete('1.0', tk.END)
            self.phone_text.config(fg=self.colors.get('text_fg', '#e8f4fa'))
            self._phone_placeholder_active = False

    def _get_phones_text(self) -> str:
        """Return the phone-box content, ignoring the placeholder hint."""
        if getattr(self, '_phone_placeholder_active', False):
            return ""
        return self.phone_text.get('1.0', tk.END).strip()


    def on_terminal_click(self, event):
        """Handle terminal click - auto-scroll remains on but user can still click"""
        try:
            # Force auto-scroll to stay enabled even if user clicks
            self.auto_scroll_enabled = True
            if hasattr(self, 'auto_scroll_btn'):
                self.auto_scroll_btn.config(text="⏬ Auto-Scroll: ALWAYS ON", bg='#4CAF50')
        except:
            pass

    def on_terminal_scroll(self, event):
        """Handle terminal scroll - keep auto-scroll enabled even if scrolling"""
        try:
            # We keep it enabled but don't force 'see(END)' while they are scrolling up
            # The next log message will trigger the scroll back to bottom
            self.auto_scroll_enabled = True
        except:
            pass

    def ensure_auto_scroll(self):
        """Ensure terminal stays scrolled to bottom during operations with GUI responsiveness"""
        def _scroll_internal():
            if not self.auto_scroll_enabled:
                return  # Skip if user has disabled auto-scroll
                
            try:
                # Scroll to end (no immediate update - prevents glitches)
                self.terminal.see(tk.END)
                # Use after_idle for smooth updates instead of immediate update
                # This batches with other GUI updates and prevents glitches
                self.root.after_idle(lambda: self.terminal.update_idletasks())
            except:
                pass  # Ignore any errors during scrolling
        
        # Schedule on main thread (throttled to prevent glitches)
        if threading.current_thread() != threading.main_thread():
            self.root.after(0, _scroll_internal)
        else:
            # On main thread, use after_idle to batch updates smoothly
            self.root.after_idle(_scroll_internal)

    def _batch_log_updates(self):
        """Process batched log messages to prevent GUI glitches from rapid updates - optimized for Golang fast mode"""
        if not self._log_buffer:
            self._log_update_scheduled = False
            return
        
        try:
            # Adaptive batch size: larger for fast mode (Golang operations)
            max_batch = self._log_buffer_max_fast if self._fast_mode_active else self._log_buffer_max
            
            # Get buffered messages (up to max batch size)
            with self._gui_update_lock:
                messages_to_log = self._log_buffer[:max_batch]
                self._log_buffer = self._log_buffer[max_batch:]
            
            if not messages_to_log:
                self._log_update_scheduled = False
                return
            
            # Batch insert all messages at once (optimized for fast updates)
            timestamp = datetime.now().strftime('%H:%M:%S')
            log_text = ""
            for message in messages_to_log:
                # Highlight Golang messages for visibility
                if "GOLANG" in message.upper() or "HIGH-PERFORMANCE" in message.upper():
                    log_entry = f"[{timestamp}] ⚡ {message}\n"
                else:
                    log_entry = f"[{timestamp}] {message}\n"
                log_text += log_entry
                # Also log to file (non-blocking, don't slow down GUI)
                try:
                    log_message(log_entry.strip())
                except:
                    pass  # Don't block on file logging
            
            # Single insert operation (much faster than multiple inserts)
            if log_text:
                self.terminal.insert(tk.END, log_text)
                
                # Adaptive line limiting: keep more lines in fast mode
                max_lines = 1000 if self._fast_mode_active else 500
                try:
                    line_count = int(self.terminal.index('end-1c').split('.')[0])
                    if line_count > max_lines:
                        self.terminal.delete('1.0', f'{line_count - max_lines}.0')
                except:
                    pass  # Ignore errors in line counting
                
                # Force auto-scroll to bottom only if enabled
                if self.auto_scroll_enabled:
                    self.terminal.see(tk.END)
            
            # Schedule next batch if more messages in buffer
            if self._log_buffer:
                self.root.after(0, self._batch_log_updates)
            else:
                self._log_update_scheduled = False
                
        except Exception as e:
            # Never let log updates crash the GUI
            self._log_update_scheduled = False
            try:
                print(f"⚠️ Log update error (non-critical): {e}")
            except:
                pass  # Even print might fail if GUI is frozen
    
    def _start_gui_heartbeat(self):
        """🛡️ FREEZE PREVENTION: Keep GUI responsive with regular heartbeat"""
        def heartbeat():
            if not self._gui_heartbeat_active:
                return
            
            try:
                # Process pending GUI events (non-blocking)
                self.root.update_idletasks()
                self._last_heartbeat = time.time()
            except:
                pass  # Ignore errors in heartbeat
            
            # Schedule next heartbeat
            if self._gui_heartbeat_active:
                self.root.after(int(self._heartbeat_interval * 1000), heartbeat)
        
        # Start heartbeat
        self.root.after(int(self._heartbeat_interval * 1000), heartbeat)
    
    def _start_gui_watchdog(self):
        """🛡️ FREEZE PREVENTION: Monitor GUI responsiveness and recover if frozen"""
        def watchdog_check():
            if not self._watchdog_active:
                return
            
            try:
                current_time = time.time()
                time_since_last_heartbeat = current_time - self._last_heartbeat
                
                # If heartbeat hasn't updated in 5 seconds, GUI might be frozen
                if time_since_last_heartbeat > 5.0:
                    # Try to recover by forcing GUI update
                    try:
                        self.root.update_idletasks()
                        self._last_heartbeat = time.time()
                        # Log warning (but don't spam)
                        if not hasattr(self, '_watchdog_warning_logged') or not self._watchdog_warning_logged:
                            try:
                                self.log("⚠️ GUI watchdog: Detected potential freeze, recovering...")
                                self._watchdog_warning_logged = True
                            except:
                                pass
                    except:
                        pass
                else:
                    self._watchdog_warning_logged = False
                
                self._watchdog_last_check = current_time
            except:
                pass  # Ignore watchdog errors
            
            # Schedule next check
            if self._watchdog_active:
                self.root.after(int(self._watchdog_interval * 1000), watchdog_check)
        
        # Start watchdog
        self.root.after(int(self._watchdog_interval * 1000), watchdog_check)
    
    def log(self, message):
        """Thread-safe log method with batching to prevent GUI glitches - optimized for fast Golang operations"""
        # Add message to buffer
        with self._gui_update_lock:
            self._log_buffer.append(message)
            
            # Adaptive scheduling: faster updates in fast mode
            max_batch = self._log_buffer_max_fast if self._fast_mode_active else self._log_buffer_max
            
            # Schedule batch update if not already scheduled or if buffer is full
            should_schedule = not self._log_update_scheduled or len(self._log_buffer) >= max_batch
            
            if should_schedule:
                self._log_update_scheduled = True
                
                def _schedule_batch_update():
                    """Schedule batch update on main thread"""
                    self._batch_log_updates()
                
                # Schedule on main thread with throttling
                # In fast mode, use shorter delay for more responsive updates
                delay = 0 if self._fast_mode_active else 0
                if threading.current_thread() != threading.main_thread():
                    self.root.after(delay, _schedule_batch_update)
                else:
                    # On main thread, use after_idle to batch with other updates
                    self.root.after_idle(_schedule_batch_update)
    
    def set_fast_mode(self, enabled=True):
        """Enable/disable fast mode for Golang high-performance operations"""
        self._fast_mode_active = enabled
        if enabled:
            # Ensure auto-scroll is on for fast updates
            if not self.auto_scroll_enabled:
                self.auto_scroll_enabled = True
                try:
                    self.auto_scroll_btn.config(text="⏬ Auto-Scroll: ON", bg='#4CAF50')
                except:
                    pass
            # Visual indicator: Change terminal title to show fast mode
            try:
                terminal_frame = self.terminal.master
                if hasattr(terminal_frame, 'config'):
                    terminal_frame.config(text="⚡ LIVE TERMINAL - GOLANG HIGH-PERFORMANCE MODE")
            except:
                pass
        else:
            # Reset terminal title
            try:
                terminal_frame = self.terminal.master
                if hasattr(terminal_frame, 'config'):
                    terminal_frame.config(text="LIVE TERMINAL")
            except:
                pass

    def update_button_states(self, event=None):
        phones_text = self._get_phones_text()
        count = 0
        if phones_text:
            phone_list = [line.strip() for line in phones_text.split('\n') if line.strip()]
            count = len(phone_list)

        # Live count on the button (no terminal spam per keystroke)
        if hasattr(self, 'count_btn'):
            self.count_btn.config(text=f"📊 Count: {count}")

        # The simplified Sportsape BitBot build only exposes balance-related actions.
        if hasattr(self, "check_balance_btn"):
            self.check_balance_btn.config(state='normal', bg=self.colors.get('accent', '#00a8fa'))

        # Debounced, change-only terminal log (logs once when typing stops)
        self._schedule_phone_count_log(count)

    def _schedule_phone_count_log(self, count):
        """Log the phone count once the user pauses typing, and only on change."""
        after_id = getattr(self, '_count_log_after_id', None)
        if after_id:
            try:
                self.root.after_cancel(after_id)
            except Exception:
                pass
        if getattr(self, '_last_logged_count', None) == count:
            return
        self._count_log_after_id = self.root.after(
            600, lambda: self._log_phone_count(count)
        )

    def _log_phone_count(self, count):
        self._count_log_after_id = None
        if getattr(self, '_last_logged_count', None) == count:
            return
        self._last_logged_count = count
        if count > 0:
            self.log(f"📊 Phone numbers loaded: {count}")
        else:
            self.log("📊 Phone numbers cleared")

    def _clear_phones(self):
        """Clear the phone box and restore the placeholder hint."""
        self.phone_text.delete('1.0', tk.END)
        if not getattr(self, '_phone_placeholder_active', False):
            self._phone_placeholder_active = True
            self.phone_text.insert('1.0', "Enter phone numbers here, one per line...")
            self.phone_text.config(fg=self.colors.get('muted', '#7d98a8'))
        self.update_button_states()
    
    def on_text_changed(self, event=None):
        """🚀 SMART PRELOAD: Called when user types/pastes - start background processing"""
        accounts_text = self._get_phones_text()
        password = self.password_entry.get().strip()
        
        # Only process if something changed
        if accounts_text != self.last_accounts_text or password != self.last_password:
            self.last_accounts_text = accounts_text
            self.last_password = password
            
            # Smart preloading is disabled in this Sportsape BitBot-only build.
            if accounts_text and password and self.preloader:
                self.preloader.on_accounts_changed(accounts_text, password)
                
                # Schedule status update
                self.root.after(2000, self.update_preload_status)  # Check status in 2 seconds
    
    def update_preload_status(self):
        """Show live preload status to user"""
        if not self.preloader:
            return
        status = self.preloader.get_status()
        cached = status['cached_accounts']
        
        if status['is_processing']:
            log_message("🔥 Smart preload: Processing accounts in background...", verbose=True)
        elif cached > 0:
            # Show user that accounts are ready for instant response
            self.log(f"⚡ INSTANT MODE: {cached} accounts ready - click any button for 10 tasks/sec speed!")
        
        # Keep updating if still processing
        if status['is_processing'] or status['queue_size'] > 0:
            self.root.after(1000, self.update_preload_status)

    def save_config_on_change(self, event=None):
        if should_persist():
            self.save_config()

    def upload_phones(self):
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt"), ("CSV files", "*.csv"), ("All files", "*.*")])
        if file_path:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
                if getattr(self, '_phone_placeholder_active', False):
                    self.phone_text.delete('1.0', tk.END)
                    self.phone_text.config(fg=self.colors.get('text_fg', '#e8f4fa'))
                    self._phone_placeholder_active = False
                self.phone_text.insert(tk.END, content)
            # Count and log after upload
            phones_text = self.phone_text.get('1.0', tk.END).strip()
            phone_list = [line.strip() for line in phones_text.split('\n') if line.strip()]
            count = len(phone_list)
            self.log(f"📁 Phone numbers uploaded: {count} from {os.path.basename(file_path)}")
            self._last_logged_count = count
            self.update_button_states()  # Update button state

    def change_bookie(self):
        """Change bookie URL and let AI discover endpoints"""
        new_url = self.target_url.get().strip()
        if not new_url:
            self.log("❌ Error: Please enter a bookie URL first")
            return
        
        # Confirm with user
        confirm = messagebox.askyesno(
            "Change Bookie",
            f"Switch from {self.headless.base_url} to {new_url}?\n\nAI will automatically learn and adapt to the new site."
        )
        if not confirm:
            return
        
        self.log(f"🤖 AI is analyzing the new bookie...")
        self.log("⏳ This may take 10-30 seconds...")
        
        # Run in background thread
        def change_bookie_thread():
            success = self.headless.change_bookie_url(new_url)
            if success:
                self.log(f"  🚀 Ready to use with new bookie!")
                messagebox.showinfo("Success", f"✅ AI successfully learned {new_url}\n\nReady to operate!")
            else:
                self.log("\n❌ AI couldn't fully adapt to the new site")
                self.log("  💡 Site may not be compatible")
                messagebox.showerror("Error", f"AI couldn't fully learn {new_url}\n\nSite may not be compatible")
        
        threading.Thread(target=change_bookie_thread, daemon=True).start()

    def roll_over(self):
        phones = self.phone_text.get('1.0', tk.END).strip()
        if not phones:
            self.log("Error: Please enter phone numbers before rolling over.")
            return
        password = self.password_entry.get()
        stake = self.stake_entry.get()
        if not password or not stake:
            self.log("Error: Please enter password and stake for roll over.")
            return
        phone_list = [line.strip() for line in phones.split('\n') if line.strip()]
        
        # Single-round rollover - search for 1.88/1.88, place bets, then stop
        self.log(f"🎯 ROLL OVER - {len(phone_list)} accounts, KES {stake} stake")
        self.log(f"🔍 Searching for 1.88/1.88 odds match (will keep searching until found)...")
        threading.Thread(target=self.headless.roll_over_accounts, args=(phone_list, password, stake, self.log, False), daemon=True).start()

    def place_bets(self):
        phones = self.phone_text.get('1.0', tk.END).strip()
        stake = self.stake_entry.get().strip()
        booking_code = self.booking_entry.get().strip()

        if not phones:
            self.log("❌ Error: Please enter phone numbers before placing bets.")
            return
        if not stake:
            self.log("❌ Error: Please enter a stake amount for placing bets.")
            return
        if not booking_code:
            self.log("❌ Error: Please enter a booking code for placing bets.")
            return

        password = self.password_entry.get()
        if not password:
            self.log("❌ Error: Please enter password for placing bets.")
            return
        
        phone_list = [line.strip() for line in phones.split('\n') if line.strip()]
        
        # Validate stake is a valid number
        try:
            stake_float = float(stake)
            if stake_float <= 0:
                self.log("❌ Error: Stake must be a positive number.")
                return
        except ValueError:
            self.log(f"❌ Error: Invalid stake '{stake}'. Please enter a valid number (e.g., 10, 50, 100).")
            return
        
        self.log("⚡ Launching bet placement engine (background)...")
        
        def run_place_bets():
            local_phone_list = list(phone_list)
            optimized_stakes = None
            
            # AI-Enhanced Betting (runs in background thread now)
            if self.ai_enabled.get() and self.ai_mode.get() != "manual":
                self.log(f"🤖 AI-Enhanced betting mode active")
                
                ai_results = self.ai_integration.smart_batch_analysis(
                    local_phone_list, booking_code, stake_float
                )
                
                if self.ai_mode.get() == "full_auto":
                    recommended_accounts = [
                        phone for phone, analysis in ai_results['recommendations'].items()
                        if analysis.get('should_proceed', False)
                    ]
                    
                    if len(recommended_accounts) < len(local_phone_list):
                        excluded = len(local_phone_list) - len(recommended_accounts)
                        self.log(f"🤖 AI excluded {excluded} accounts due to low confidence/high risk")
                        local_phone_list = recommended_accounts
                    
                    optimized_stakes = self.ai_integration.auto_optimize_stakes(
                        local_phone_list, booking_code, stake_float
                    )
                else:
                    self.log("📋 AI Recommendations (Assisted Mode):")
                    for advice in ai_results.get('batch_advice', []):
                        self.log(f"   {advice}")
                    optimized_stakes = None
            
            if not local_phone_list:
                self.log("❌ No accounts to bet on after AI analysis")
                return
            
            self.log(f"🎯 Starting bet placement for {len(local_phone_list)} accounts...")
            self.log(f"💰 Booking Code: {booking_code} | Base Stake: KES {stake} per bet")
            self.log(f"🔍 Checking which accounts have sufficient balance...")
            
            def enhanced_callback(message):
                self.log(message)
                self.ensure_auto_scroll()
                if "GOLANG HIGH-PERFORMANCE MODE" in message:
                    self.set_fast_mode(True)
                elif "GOLANG COMPLETE" in message or ("completed" in message.lower() and "golang" in message.lower()):
                    self.set_fast_mode(False)
            
            def smart_bet_placement():
                try:
                    ready_accounts = None
                    insufficient_accounts = []
                    inactive_accounts = []
                    
                    if self.headless.ai_engine and self.headless.ai_engine.enabled:
                        import time
                        enhanced_callback("🤖 AI: Checking for cached balance data from recent CHECK BALANCE...")
                        
                        cached_balances = None
                        with self.headless._balance_cache_lock:
                            if self.headless.balance_cache.get('results'):
                                cache_age = time.time() - self.headless.balance_cache.get('timestamp', 0)
                                if cache_age < 600:
                                    cached_balances = {}
                                    for phone, data in self.headless.balance_cache['results'].items():
                                        if isinstance(data, dict):
                                            cached_balances[phone] = data.get('balance', 0)
                                        else:
                                            try:
                                                del self.headless.balance_cache['results'][phone]
                                            except:
                                                pass
                                    cache_minutes = int(cache_age // 60)
                                    cache_seconds = int(cache_age % 60)
                                    enhanced_callback(f"✅ Found fresh cached balance data ({cache_minutes}m {cache_seconds}s old)")
                        
                        if cached_balances:
                            ai_result = self.headless.ai_engine.pre_qualify_accounts_for_operation(
                                local_phone_list, 'bet', cached_balances, float(stake_float)
                            )
                            
                            if ai_result.get('ready_count', 0) > 0:
                                ready_accounts = []
                                for phone in ai_result['ready_accounts']:
                                    account_data = self.headless.balance_cache['results'].get(phone, {})
                                    if isinstance(account_data, dict) and account_data.get('status') == 'success':
                                        ready_accounts.append({
                                            'phone': phone,
                                            'balance': account_data.get('balance', 0),
                                            'password': password,
                                            'auth_token': account_data.get('auth_token'),
                                            'x_odi_key': account_data.get('x_odi_key'),
                                            'odi_cookie': account_data.get('odi_cookie')
                                        })
                                
                                if ready_accounts:
                                    enhanced_callback(f"⚡ AI PRE-QUALIFIED: {len(ready_accounts)} accounts ready (INSTANT - skipped balance check!)")
                                    enhanced_callback(ai_result.get('speed_boost', 'Using cached data - instant start!'))
                                    
                                    for phone in local_phone_list:
                                        found = False
                                        for acc in ready_accounts:
                                            if (isinstance(acc, dict) and acc.get('phone') == phone) or acc == phone:
                                                found = True
                                                break
                                        if not found:
                                            insufficient_accounts.append((phone, 0))
                    
                    if ready_accounts is None:
                        enhanced_callback("💰 Performing balance check (using 10-minute cache if available)...")
                        ready_accounts, insufficient_accounts, inactive_accounts = self.headless.check_account_balances(
                            local_phone_list, password, stake_float, enhanced_callback, cache_ttl=600
                        )
                    
                    if insufficient_accounts or inactive_accounts:
                        skipped = len(insufficient_accounts) + len(inactive_accounts)
                        enhanced_callback(f"⚠️ Skipping {skipped}/{len(local_phone_list)} accounts (insufficient balance or inactive)")
                        
                    if not ready_accounts:
                        enhanced_callback("❌ No accounts have sufficient balance for this bet")
                        return
                    
                    ready_phones = [acc['phone'] if isinstance(acc, dict) else acc for acc in ready_accounts]
                    enhanced_callback(f"✅ Placing bets for {len(ready_phones)} accounts with sufficient balance...")
                    
                    if optimized_stakes:
                        for phone in ready_phones:
                            optimized_stake = optimized_stakes.get(phone, stake_float)
                            self.headless.place_single_bet_with_booking_code(
                                phone, password, str(optimized_stake), booking_code, enhanced_callback
                            )
                    else:
                        self.headless.place_bets_with_booking_code(
                            ready_phones, password, stake, booking_code, enhanced_callback
                        )
                except Exception as e:
                    enhanced_callback(f"❌ Bet placement error: {e}")
                    log_message(f"❌ Bet placement error: {e}")
                
                if self.ai_enabled.get():
                    self.update_ai_stats_display()
            
            smart_bet_placement()
        
        threading.Thread(target=run_place_bets, daemon=True).start()

    def check_balance(self):
        phones = self._get_phones_text()
        if not phones:
            self.log("❌ Error: Please enter phone numbers before checking balance.")
            messagebox.showerror("Missing Data", "Please enter phone numbers")
            return
        password = self.password_entry.get()
        if not password:
            self.log("❌ Error: Please enter password for balance check.")
            messagebox.showerror("Missing Password", "Please enter password")
            return
        phone_list = [line.strip() for line in phones.split('\n') if line.strip()]
        
        self.log(f"⚡ Launching balance check engine for {len(phone_list)} accounts...")
        
        if len(phone_list) == 0:
            self.log("❌ Error: No valid phone numbers found")
            messagebox.showerror("Invalid Data", "No valid phone numbers found")
            return
        
        # Create enhanced callback that ensures auto-scroll and fast mode handling
        last_callback_message = {"value": None}
        def enhanced_callback(message):
            if message == last_callback_message["value"]:
                return
            last_callback_message["value"] = message
            self.log(message)
            self.ensure_auto_scroll()
            # Enable/disable fast mode based on Golang operations
            if "GOLANG HIGH-PERFORMANCE MODE" in message:
                self.set_fast_mode(True)
            elif "GOLANG COMPLETE" in message or ("completed" in message.lower() and "golang" in message.lower()):
                self.set_fast_mode(False)
        
        # Disable button during processing
        self.check_balance_btn.config(state='disabled')
        
        def run_balance_check():
            try:
                valid_phones = [p for p in phone_list if p not in self.headless.permanent_failures]
                filtered_count = len(phone_list) - len(valid_phones)
                
                if filtered_count > 0:
                    self.log(f"⏭️  Skipping {filtered_count} accounts with permanent failures")
                
                if len(valid_phones) == 0:
                    self.log("❌ No valid accounts to check (all have permanent failures)")
                    self.root.after(0, lambda: messagebox.showerror("Invalid Data", "All accounts are marked as permanently failed"))
                    return
                
                # Reset running flag in case it was stopped
                self.headless.running = True
                self.running = True
                self.headless.check_balances(valid_phones, password, enhanced_callback)
                self.log("✅ Balance check completed!")
            except KeyboardInterrupt:
                self.log("🛑 Balance check stopped by user")
            except Exception as e:
                self.log(f"❌ ERROR during balance check: {str(e)}")
                import traceback
                self.log(f"⚠️ Details: {traceback.format_exc()[:500]}")  # Limit traceback length
            finally:
                # Always re-enable button and reset flags
                try:
                    self.root.after(0, lambda: self.check_balance_btn.config(state='normal'))
                    self.headless.running = True
                    self.running = True
                except:
                    pass
        
        threading.Thread(target=run_balance_check, daemon=True).start()

    def claim_bonus(self):
        phones = self.phone_text.get('1.0', tk.END).strip()
        if not phones:
            self.log("❌ Error: Please enter phone numbers before claiming bonuses.")
            return
        
        password = self.password_entry.get()
        if not password:
            self.log("❌ Error: Please enter password for claiming bonuses.")
            return
        
        phone_list = [line.strip() for line in phones.split('\n') if line.strip()]
        
        self.log(f"🎁 Starting bonus claiming for {len(phone_list)} accounts...")
        self.log("🔍 Will fetch and claim all available promotions...")
        
        # Create enhanced callback that ensures auto-scroll
        def enhanced_callback(message):
            self.log(message)
            self.ensure_auto_scroll()
        
        # Use the new bonus claiming method
        threading.Thread(
            target=self.headless.claim_bonuses_for_accounts,
            args=(phone_list, password, enhanced_callback),
            daemon=True
        ).start()

    def withdraw_funds(self):
        """Withdraw funds from all accounts with elegant dialog"""
        phones = self.phone_text.get('1.0', tk.END).strip()
        if not phones:
            self.log("❌ Error: Please enter phone numbers before withdrawing.")
            messagebox.showerror("Missing Data", "Please enter phone numbers")
            return
        
        password = self.password_entry.get()
        if not password:
            self.log("❌ Error: Please enter password for withdrawal.")
            messagebox.showerror("Missing Password", "Please enter password")
            return
        
        phone_list = [line.strip() for line in phones.split('\n') if line.strip()]
        
        if len(phone_list) == 0:
            self.log("❌ Error: No valid phone numbers found")
            messagebox.showerror("Invalid Data", "No valid phone numbers found")
            return
        
        # Show elegant withdrawal dialog
        amount = self.show_withdrawal_dialog(len(phone_list))
        
        if not amount:
            self.log("❌ Withdrawal cancelled")
            return
        
        self.log(f"💸 Starting withdrawal for {len(phone_list)} accounts...")
        self.log(f"💰 Amount per account: KES {amount:.2f}")
        self.log(f"💵 Total withdrawal: KES {amount * len(phone_list):.2f}")
        
        # Create enhanced callback that ensures auto-scroll
        def enhanced_callback(message):
            self.log(message)
            self.ensure_auto_scroll()
        
        def run_withdrawal():
            try:
                # Reset running flag in case it was stopped
                self.headless.running = True
                self.running = True
                self.headless.batch_withdraw(phone_list, password, amount, enhanced_callback)
                self.log("✅ Withdrawal process completed!")
            except KeyboardInterrupt:
                self.log("🛑 Withdrawal stopped by user")
            except Exception as e:
                self.log(f"❌ ERROR during withdrawal: {str(e)}")
                import traceback
                self.log(f"⚠️ Details: {traceback.format_exc()[:500]}")
            finally:
                # Always reset flags
                try:
                    self.headless.running = True
                    self.running = True
                except:
                    pass
        
        threading.Thread(target=run_withdrawal, daemon=True).start()

    def show_withdrawal_dialog(self, account_count):
        """Show elegant withdrawal dialog and return amount or None if cancelled"""
        # Create custom dialog window
        dialog = tk.Toplevel(self.root)
        dialog.title("💸 Withdraw Funds")
        dialog.configure(bg='#1E1E1E')
        dialog.resizable(False, False)
        
        # Center the dialog
        dialog_width = 500
        dialog_height = 480  # Increased from 380 to fit all content + buttons
        screen_width = dialog.winfo_screenwidth()
        screen_height = dialog.winfo_screenheight()
        x = (screen_width - dialog_width) // 2
        y = (screen_height - dialog_height) // 2
        dialog.geometry(f'{dialog_width}x{dialog_height}+{x}+{y}')
        
        # Make it modal
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Result variable
        result = {'amount': None}
        
        # Header with icon
        header_frame = tk.Frame(dialog, bg='#00BCD4', height=80)
        header_frame.pack(fill='x')
        header_frame.pack_propagate(False)
        
        tk.Label(header_frame, text="💸", font=('Arial', 36), bg='#00BCD4', fg='white').pack(pady=10)
        tk.Label(header_frame, text="Withdraw to M-Pesa", font=('Arial', 14, 'bold'), bg='#00BCD4', fg='white').pack()
        
        # Main content
        content_frame = tk.Frame(dialog, bg='#1E1E1E', padx=30, pady=15)
        content_frame.pack(fill='both', expand=True)
        
        # Account info
        info_frame = tk.Frame(content_frame, bg='#2A2A2A', relief='flat', bd=0)
        info_frame.pack(fill='x', pady=(0, 12))
        
        tk.Label(info_frame, text=f"📱 Accounts: {account_count}", 
                font=('Arial', 11), bg='#2A2A2A', fg='#00BCD4', anchor='w', padx=15, pady=8).pack(fill='x')
        tk.Label(info_frame, text="💳 Destination: M-Pesa linked to each account", 
                font=('Arial', 10), bg='#2A2A2A', fg='#888888', anchor='w', padx=15, pady=8).pack(fill='x')
        
        # Amount input section
        tk.Label(content_frame, text="Enter Amount per Account (KES)", 
                font=('Arial', 10, 'bold'), bg='#1E1E1E', fg='white', anchor='w').pack(fill='x', pady=(8, 4))
        
        # Amount entry with styled frame
        entry_frame = tk.Frame(content_frame, bg='#2A2A2A', relief='flat', bd=1, highlightthickness=1, highlightbackground='#00BCD4')
        entry_frame.pack(fill='x', pady=(0, 10))
        
        amount_var = tk.StringVar(value="100")
        amount_entry = tk.Entry(entry_frame, textvariable=amount_var, font=('Arial', 16, 'bold'), 
                               bg='#2A2A2A', fg='white', insertbackground='white', 
                               relief='flat', justify='center', bd=0)
        amount_entry.pack(fill='x', padx=2, pady=2, ipady=8)
        amount_entry.select_range(0, tk.END)
        amount_entry.focus()
        
        # Total calculation (updates in real-time)
        total_label = tk.Label(content_frame, text="", font=('Arial', 9), 
                              bg='#1E1E1E', fg='#888888', anchor='center')
        total_label.pack(fill='x', pady=(4, 10))
        
        def update_total(*args):
            try:
                amount = float(amount_var.get())
                total = amount * account_count
                total_label.config(text=f"Total Withdrawal: KES {total:,.2f}", fg='#00BCD4')
            except:
                total_label.config(text="Enter a valid amount", fg='#FF5555')
        
        amount_var.trace('w', update_total)
        update_total()
        
        # Warning message
        warning_frame = tk.Frame(content_frame, bg='#2A2A2A', relief='flat', bd=0)
        warning_frame.pack(fill='x', pady=(0, 10))
        
        tk.Label(warning_frame, text="⚠️ Important Information", font=('Arial', 8, 'bold'), 
                bg='#2A2A2A', fg='#FFC107', anchor='w', padx=10, pady=4).pack(fill='x')
        tk.Label(warning_frame, text="• Sent to M-Pesa immediately\n• Min: KES 100 | Max daily: KES 70,000\n• Cannot be reversed", 
                font=('Arial', 8), bg='#2A2A2A', fg='#888888', anchor='w', padx=10, pady=6, justify='left').pack(fill='x')
        
        # Buttons
        button_frame = tk.Frame(content_frame, bg='#1E1E1E')
        button_frame.pack(fill='x', pady=(10, 0))
        
        def on_confirm():
            try:
                # Get and validate amount
                amount_str = amount_var.get().strip()
                if not amount_str:
                    messagebox.showwarning("Invalid Amount", "Please enter an amount", parent=dialog)
                    amount_entry.focus()
                    return
                
                # Convert to float
                try:
                    amount = float(amount_str)
                except ValueError:
                    messagebox.showerror("Invalid Input", "Please enter a valid number (e.g., 100 or 250.50)", parent=dialog)
                    amount_entry.focus()
                    amount_entry.select_range(0, tk.END)
                    return
                
                # Validate range
                if amount < 100:
                    messagebox.showwarning("Invalid Amount", "Minimum withdrawal is KES 100", parent=dialog)
                    amount_entry.focus()
                    amount_entry.select_range(0, tk.END)
                    return
                    
                # Note: 70,000 is daily total limit across all accounts
                if amount > 70000:
                    messagebox.showwarning("Invalid Amount", "Maximum withdrawal is KES 70,000 (daily total limit)", parent=dialog)
                    amount_entry.focus()
                    amount_entry.select_range(0, tk.END)
                    return
                
                # Final confirmation with clear details
                total = amount * account_count
                confirm_msg = (
                    f"💸 WITHDRAW TO M-PESA\n\n"
                    f"Amount per account: KES {amount:,.2f}\n"
                    f"Number of accounts: {account_count}\n"
                    f"Total withdrawal: KES {total:,.2f}\n\n"
                    f"⚠️ Funds will be sent immediately to M-Pesa.\n"
                    f"This action cannot be reversed.\n\n"
                    f"Do you want to proceed?"
                )
                
                if messagebox.askyesno("Confirm M-Pesa Withdrawal", confirm_msg, parent=dialog):
                    result['amount'] = amount
                    dialog.destroy()
                    
            except Exception as e:
                messagebox.showerror("Error", f"An error occurred: {str(e)}", parent=dialog)
        
        def on_cancel():
            result['amount'] = None
            dialog.destroy()
        
        # Accept button (left) - Changed from "Withdraw" to "Accept"
        confirm_btn = tk.Button(button_frame, text="✓ ACCEPT", command=on_confirm, 
                               bg='#00BCD4', fg='white', font=('Arial', 11, 'bold'), 
                               relief='flat', cursor='hand2', padx=20, pady=10)
        confirm_btn.pack(side='left', fill='x', expand=True, padx=(0, 5))
        
        # Hover effect for confirm button
        def on_enter_confirm(e):
            confirm_btn.config(bg='#00ACC1')
        def on_leave_confirm(e):
            confirm_btn.config(bg='#00BCD4')
        confirm_btn.bind('<Enter>', on_enter_confirm)
        confirm_btn.bind('<Leave>', on_leave_confirm)
        
        # Cancel button (right)
        cancel_btn = tk.Button(button_frame, text="✗ CANCEL", command=on_cancel, 
                              bg='#424242', fg='white', font=('Arial', 11, 'bold'), 
                              relief='flat', cursor='hand2', padx=20, pady=10)
        cancel_btn.pack(side='left', fill='x', expand=True, padx=(5, 0))
        
        # Hover effect for cancel button
        def on_enter_cancel(e):
            cancel_btn.config(bg='#505050')
        def on_leave_cancel(e):
            cancel_btn.config(bg='#424242')
        cancel_btn.bind('<Enter>', on_enter_cancel)
        cancel_btn.bind('<Leave>', on_leave_cancel)
        
        # Bind Enter key to confirm
        dialog.bind('<Return>', lambda e: on_confirm())
        dialog.bind('<Escape>', lambda e: on_cancel())
        
        # Wait for dialog to close
        dialog.wait_window()
        
        return result['amount']

    def balance_keeper(self):
        """Balance Keeper - Withdraw to leave a specific amount in account"""
        phones = self.phone_text.get('1.0', tk.END).strip()
        if not phones:
            self.log("❌ Error: Please enter phone numbers before using Balance Keeper.")
            messagebox.showerror("Missing Data", "Please enter phone numbers")
            return
        
        password = self.password_entry.get()
        if not password:
            self.log("❌ Error: Please enter password for Balance Keeper.")
            messagebox.showerror("Missing Password", "Please enter password")
            return
        
        phone_list = [line.strip() for line in phones.split('\n') if line.strip()]
        
        if len(phone_list) == 0:
            self.log("❌ Error: No valid phone numbers found")
            messagebox.showerror("Invalid Data", "No valid phone numbers found")
            return
        
        # Show Balance Keeper dialog
        amount_to_leave = self.show_balance_keeper_dialog(len(phone_list))
        
        if not amount_to_leave:
            self.log("❌ Balance Keeper cancelled")
            return
        
        self.log(f"💰 Starting Balance Keeper for {len(phone_list)} accounts...")
        self.log(f"💵 Amount to leave per account: KES {amount_to_leave:.2f}")
        
        # Create enhanced callback that ensures auto-scroll
        def enhanced_callback(message):
            self.log(message)
            self.ensure_auto_scroll()
        
        def run_balance_keeper():
            try:
                # Reset running flag in case it was stopped
                self.headless.running = True
                self.running = True
                
                results = []
                successful = 0
                failed = 0
                total_withdrawn = 0
                
                for idx, phone in enumerate(phone_list, 1):
                    if not self.running or not self.headless.running:
                        self.log("🛑 Operation stopped by user")
                        break
                    
                    self.log(f"\n[{idx}/{len(phone_list)}] Processing {phone}...")
                    enhanced_callback(f"💰 [{idx}/{len(phone_list)}] Checking balance for {phone}...")
                    
                    # Get current balance for this account
                    login_result = self.headless.login_with_balance(phone, password)
                    if not login_result or login_result.get('status') != 'success':
                        error_msg = login_result.get('message', 'Login failed') if login_result else 'Login failed'
                        self.log(f"❌ {phone}: {error_msg}")
                        enhanced_callback(f"❌ {phone}: {error_msg}")
                        results.append({
                            'phone': phone,
                            'status': 'error',
                            'message': error_msg
                        })
                        failed += 1
                        continue
                    
                    current_balance = float(login_result.get('balance', 0))
                    self.log(f"💰 {phone}: Current balance = KES {current_balance:.2f}")
                    
                    # Calculate withdraw amount
                    withdraw_amount = current_balance - amount_to_leave
                    
                    # Validate calculated amount
                    if withdraw_amount <= 0:
                        error_msg = f"Insufficient balance: KES {current_balance:.2f} <= KES {amount_to_leave:.2f} (amount to leave)"
                        self.log(f"❌ {phone}: {error_msg}")
                        enhanced_callback(f"❌ {phone}: {error_msg}")
                        results.append({
                            'phone': phone,
                            'status': 'error',
                            'message': error_msg
                        })
                        failed += 1
                        continue
                    
                    # Check minimum withdrawal
                    if withdraw_amount < 100:
                        error_msg = f"Calculated withdrawal (KES {withdraw_amount:.2f}) is below minimum (KES 100)"
                        self.log(f"❌ {phone}: {error_msg}")
                        enhanced_callback(f"❌ {phone}: {error_msg}")
                        results.append({
                            'phone': phone,
                            'status': 'error',
                            'message': error_msg
                        })
                        failed += 1
                        continue
                    
                    self.log(f"💸 {phone}: Withdrawing KES {withdraw_amount:.2f} (leaving KES {amount_to_leave:.2f})")
                    enhanced_callback(f"💸 [{idx}/{len(phone_list)}] Withdrawing KES {withdraw_amount:.2f} from {phone}...")
                    
                    # Use the same withdrawal method
                    result = self.headless.withdraw_funds(phone, password, withdraw_amount, enhanced_callback)
                    results.append({
                        'phone': phone,
                        'amount_to_leave': amount_to_leave,
                        'current_balance': current_balance,
                        'withdraw_amount': withdraw_amount,
                        **result
                    })
                    
                    if result.get('status') == 'success':
                        successful += 1
                        total_withdrawn += withdraw_amount
                        self.log(f"✅ {phone}: KES {withdraw_amount:.2f} withdrawn (KES {amount_to_leave:.2f} left)")
                        enhanced_callback(f"✅ {phone}: KES {withdraw_amount:.2f} withdrawn successfully")
                    else:
                        failed += 1
                        error_msg = result.get('message', 'Withdrawal failed')
                        self.log(f"❌ {phone}: {error_msg}")
                        enhanced_callback(f"❌ {phone}: {error_msg}")
                    
                    # Delay between withdrawals to avoid rate limiting
                    if idx < len(phone_list):
                        time.sleep(3)  # 3 second delay between withdrawals
                
                # Summary
                self.log("\n" + "="*80)
                self.log("📊 BALANCE KEEPER SUMMARY")
                self.log("="*80)
                self.log(f"Accounts processed: {len(results)}/{len(phone_list)}")
                self.log(f"Successful: {successful}")
                self.log(f"Failed: {failed}")
                self.log(f"Total withdrawn: KES {total_withdrawn:.2f}")
                self.log("="*80)
                
                enhanced_callback(f"✅ Balance Keeper complete: {successful}/{len(phone_list)} successful (KES {total_withdrawn:.2f} total)")
                self.log("✅ Balance Keeper process completed!")
                
            except KeyboardInterrupt:
                self.log("🛑 Balance Keeper stopped by user")
            except Exception as e:
                self.log(f"❌ ERROR during Balance Keeper: {str(e)}")
                import traceback
                self.log(f"⚠️ Details: {traceback.format_exc()[:500]}")
            finally:
                # Always reset flags
                try:
                    self.headless.running = True
                    self.running = True
                except:
                    pass
        
        threading.Thread(target=run_balance_keeper, daemon=True).start()

    def show_balance_keeper_dialog(self, account_count):
        """Show Balance Keeper dialog and return amount_to_leave or None if cancelled"""
        # Create custom dialog window
        dialog = tk.Toplevel(self.root)
        dialog.title("💰 Balance Keeper")
        dialog.configure(bg='#1E1E1E')
        dialog.resizable(False, False)
        
        # Center the dialog
        dialog_width = 500
        dialog_height = 480
        screen_width = dialog.winfo_screenwidth()
        screen_height = dialog.winfo_screenheight()
        x = (screen_width - dialog_width) // 2
        y = (screen_height - dialog_height) // 2
        dialog.geometry(f'{dialog_width}x{dialog_height}+{x}+{y}')
        
        # Make it modal
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Result variable
        result = {'amount': None}
        
        # Header with icon
        header_frame = tk.Frame(dialog, bg='#00BCD4', height=80)
        header_frame.pack(fill='x')
        header_frame.pack_propagate(False)
        
        tk.Label(header_frame, text="💰", font=('Arial', 36), bg='#00BCD4', fg='white').pack(pady=10)
        tk.Label(header_frame, text="Balance Keeper", font=('Arial', 14, 'bold'), bg='#00BCD4', fg='white').pack()
        
        # Main content
        content_frame = tk.Frame(dialog, bg='#1E1E1E', padx=30, pady=15)
        content_frame.pack(fill='both', expand=True)
        
        # Account info
        info_frame = tk.Frame(content_frame, bg='#2A2A2A', relief='flat', bd=0)
        info_frame.pack(fill='x', pady=(0, 12))
        
        tk.Label(info_frame, text=f"📱 Accounts: {account_count}", 
                font=('Arial', 11), bg='#2A2A2A', fg='#00BCD4', anchor='w', padx=15, pady=8).pack(fill='x')
        tk.Label(info_frame, text="💳 Destination: M-Pesa linked to each account", 
                font=('Arial', 10), bg='#2A2A2A', fg='#888888', anchor='w', padx=15, pady=8).pack(fill='x')
        tk.Label(info_frame, text="💰 Withdraw enough to leave specified amount in each account", 
                font=('Arial', 10), bg='#2A2A2A', fg='#888888', anchor='w', padx=15, pady=8).pack(fill='x')
        
        # Amount input section
        tk.Label(content_frame, text="Amount to Leave in Account (KES)", 
                font=('Arial', 10, 'bold'), bg='#1E1E1E', fg='white', anchor='w').pack(fill='x', pady=(8, 4))
        
        # Amount entry with styled frame
        entry_frame = tk.Frame(content_frame, bg='#2A2A2A', relief='flat', bd=1, highlightthickness=1, highlightbackground='#00BCD4')
        entry_frame.pack(fill='x', pady=(0, 10))
        
        amount_var = tk.StringVar(value="0")
        amount_entry = tk.Entry(entry_frame, textvariable=amount_var, font=('Arial', 16, 'bold'), 
                               bg='#2A2A2A', fg='white', insertbackground='white', 
                               relief='flat', justify='center', bd=0)
        amount_entry.pack(fill='x', padx=2, pady=2, ipady=8)
        amount_entry.select_range(0, tk.END)
        amount_entry.focus()
        
        # Info label (updates in real-time)
        info_label = tk.Label(content_frame, text="", font=('Arial', 9), 
                              bg='#1E1E1E', fg='#888888', anchor='center', wraplength=440)
        info_label.pack(fill='x', pady=(4, 10))
        
        def update_info(*args):
            try:
                amount_to_leave = float(amount_var.get())
                if amount_to_leave < 0:
                    info_label.config(text="Amount cannot be negative", fg='#FF5555')
                else:
                    info_label.config(text=f"Will withdraw: (Current Balance - {amount_to_leave:.2f}) from each account", fg='#00BCD4')
            except:
                info_label.config(text="Enter a valid amount", fg='#FF5555')
        
        amount_var.trace('w', update_info)
        update_info()
        
        # Warning message
        warning_frame = tk.Frame(content_frame, bg='#2A2A2A', relief='flat', bd=0)
        warning_frame.pack(fill='x', pady=(0, 10))
        
        tk.Label(warning_frame, text="⚠️ Important Information", font=('Arial', 8, 'bold'), 
                bg='#2A2A2A', fg='#FFC107', anchor='w', padx=10, pady=4).pack(fill='x')
        tk.Label(warning_frame, text="• Balance will be checked for each account\n• Withdrawal = (Current Balance - Amount to Leave)\n• Min withdrawal: KES 100 | Max: KES 70,000 per account", 
                font=('Arial', 8), bg='#2A2A2A', fg='#888888', anchor='w', padx=10, pady=6, justify='left').pack(fill='x')
        
        # Buttons
        button_frame = tk.Frame(content_frame, bg='#1E1E1E')
        button_frame.pack(fill='x', pady=(10, 0))
        
        def on_confirm():
            try:
                # Get and validate amount
                amount_str = amount_var.get().strip()
                if not amount_str:
                    messagebox.showwarning("Invalid Amount", "Please enter an amount to leave", parent=dialog)
                    amount_entry.focus()
                    return
                
                # Convert to float
                try:
                    amount_to_leave = float(amount_str)
                except ValueError:
                    messagebox.showerror("Invalid Input", "Please enter a valid number (e.g., 0 or 100.50)", parent=dialog)
                    amount_entry.focus()
                    amount_entry.select_range(0, tk.END)
                    return
                
                # Validate range
                if amount_to_leave < 0:
                    messagebox.showwarning("Invalid Amount", "Amount to leave cannot be negative", parent=dialog)
                    amount_entry.focus()
                    amount_entry.select_range(0, tk.END)
                    return
                
                # Final confirmation
                confirm_msg = (
                    f"💰 BALANCE KEEPER - WITHDRAW TO M-PESA\n\n"
                    f"Amount to leave per account: KES {amount_to_leave:,.2f}\n"
                    f"Number of accounts: {account_count}\n\n"
                    f"💡 For each account:\n"
                    f"   • Current balance will be checked\n"
                    f"   • Withdrawal = (Balance - {amount_to_leave:,.2f})\n"
                    f"   • Minimum withdrawal: KES 100\n"
                    f"   • Funds sent to M-Pesa immediately\n\n"
                    f"⚠️ Funds will be sent immediately to M-Pesa.\n"
                    f"This action cannot be reversed.\n\n"
                    f"Do you want to proceed?"
                )
                
                if messagebox.askyesno("Confirm Balance Keeper", confirm_msg, parent=dialog):
                    result['amount'] = amount_to_leave
                    dialog.destroy()
                    
            except Exception as e:
                messagebox.showerror("Error", f"An error occurred: {str(e)}", parent=dialog)
        
        def on_cancel():
            result['amount'] = None
            dialog.destroy()
        
        # Accept button (left)
        confirm_btn = tk.Button(button_frame, text="✓ ACCEPT", command=on_confirm, 
                               bg='#00BCD4', fg='white', font=('Arial', 11, 'bold'), 
                               relief='flat', cursor='hand2', padx=20, pady=10)
        confirm_btn.pack(side='left', fill='x', expand=True, padx=(0, 5))
        
        # Hover effect for confirm button
        def on_enter_confirm(e):
            confirm_btn.config(bg='#00ACC1')
        def on_leave_confirm(e):
            confirm_btn.config(bg='#00BCD4')
        confirm_btn.bind('<Enter>', on_enter_confirm)
        confirm_btn.bind('<Leave>', on_leave_confirm)
        
        # Cancel button (right)
        cancel_btn = tk.Button(button_frame, text="✗ CANCEL", command=on_cancel, 
                              bg='#424242', fg='white', font=('Arial', 11, 'bold'), 
                              relief='flat', cursor='hand2', padx=20, pady=10)
        cancel_btn.pack(side='left', fill='x', expand=True, padx=(5, 0))
        
        # Hover effect for cancel button
        def on_enter_cancel(e):
            cancel_btn.config(bg='#505050')
        def on_leave_cancel(e):
            cancel_btn.config(bg='#424242')
        cancel_btn.bind('<Enter>', on_enter_cancel)
        cancel_btn.bind('<Leave>', on_leave_cancel)
        
        # Bind Enter key to confirm
        dialog.bind('<Return>', lambda e: on_confirm())
        dialog.bind('<Escape>', lambda e: on_cancel())
        
        # Wait for dialog to close
        dialog.wait_window()
        
        return result['amount']

    def odileague_supa5(self):
        """OdiLeague Supa5 - Place 5 bets × 50 KES, get 50 KES bonus"""
        phones = self.phone_text.get('1.0', tk.END).strip()
        if not phones:
            self.log("❌ Error: Please enter phone numbers for Supa5.")
            return
        
        password = self.password_entry.get()
        if not password:
            self.log("❌ Error: Please enter password for Supa5.")
            return
        
        phone_list = [line.strip() for line in phones.split('\n') if line.strip()]
        
        self.log("🎁 ODILEAGUE SUPA5 BONUS STRATEGY")
        self.log("=" * 50)
        self.log(f"📊 Accounts: {len(phone_list)}")
        self.log(f"💰 Strategy: 5 bets × 50 KES = Get 50 KES bonus")
        self.log(f"📈 Total: {len(phone_list) * 250} KES (5 bets × 50 KES each)")
        self.log(f"🎁 Expected bonus: {len(phone_list) * 50} KES")
        self.log("=" * 50)
        self.log("⚠️  Requirements:")
        self.log("  • Place 5 bets of 50 KES each within 1 day")
        self.log("  • Bonus awarded after 5th bet settles")
        self.log("  • Bonus can only be used as ONE bet")
        self.log("=" * 50)
        
        # Ask for confirmation
        confirmed = messagebox.askyesno(
            "OdiLeague Supa5 Confirmation",
            f"Start Supa5 bonus automation?\n\n"
            f"Accounts: {len(phone_list)}\n"
            f"Total cost: {len(phone_list) * 250} KES\n"
            f"Expected bonus: {len(phone_list) * 50} KES\n\n"
            f"This will place 5 bets of 50 KES on Odileague for each account.",
            icon='question'
        )
        
        if not confirmed:
            self.log("❌ Supa5 automation cancelled by user")
            return
        
        self.log("🚀 Starting Supa5 automation...")
        
        # Create enhanced callback
        def enhanced_callback(message):
            self.log(message)
            self.ensure_auto_scroll()
        
        # Run Supa5 automation in background thread
        threading.Thread(
            target=self.headless.odileague_supa5_automation,
            args=(phone_list, password, enhanced_callback),
            daemon=True
        ).start()

    def odileague_bonus(self):
        """Odi League Bonus - Place 20 bob virtual stake to get bonus"""
        phones = self.phone_text.get('1.0', tk.END).strip()
        if not phones:
            self.log("❌ Error: Please enter phone numbers for Odi League Bonus.")
            messagebox.showerror("Missing Data", "Please enter phone numbers")
            return
        
        password = self.password_entry.get()
        if not password:
            self.log("❌ Error: Please enter password for Odi League Bonus.")
            messagebox.showerror("Missing Password", "Please enter password")
            return
        
        phone_list = [line.strip() for line in phones.split('\n') if line.strip()]
        
        if len(phone_list) == 0:
            self.log("❌ Error: No valid phone numbers found")
            messagebox.showerror("Invalid Data", "No valid phone numbers found")
            return
        
        self.log("🎁 ODI LEAGUE BONUS - 20 bob virtual stake")
        self.log(f"🚀 Starting Odi League Bonus automation for {len(phone_list)} accounts...")
        
        # Create enhanced callback that ensures auto-scroll
        def enhanced_callback(message):
            self.log(message)
            self.ensure_auto_scroll()
        
        # Run Odi League Bonus automation in background thread
        threading.Thread(
            target=self.headless.run_odileague_bonus,
            args=(phone_list, password, enhanced_callback),
            daemon=True
        ).start()

    def set_telegram(self):
        """Elegant dialog for Telegram bot setup with instructions"""
        dialog = tk.Toplevel(self.root)
        dialog.title("⚡ Sportsape BitBot - Telegram Remote Control")
        dialog.geometry("600x500")
        dialog.configure(bg='#0a0a0a')
        dialog.resizable(False, False)
        
        # Center the dialog
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Main container
        main_frame = tk.Frame(dialog, bg='#0a0a0a', padx=30, pady=20)
        main_frame.pack(fill='both', expand=True)
        
        # Title
        title_label = tk.Label(
            main_frame,
            text="🤖 Telegram Remote Control",
            font=('Arial', 18, 'bold'),
            bg='#0a0a0a',
            fg='#00ff00'
        )
        title_label.pack(pady=(0, 10))
        
        subtitle_label = tk.Label(
            main_frame,
            text="Monitor & control your tool 24/7 from anywhere",
            font=('Arial', 10),
            bg='#0a0a0a',
            fg='#888888'
        )
        subtitle_label.pack(pady=(0, 20))
        
        # Instructions frame
        instructions_frame = tk.LabelFrame(
            main_frame,
            text=" 📖 Setup Instructions ",
            font=('Arial', 10, 'bold'),
            bg='#1a1a1a',
            fg='#00ff00',
            padx=15,
            pady=15
        )
        instructions_frame.pack(fill='x', pady=(0, 20))
        
        instructions_text = """1. Open Telegram and search for @BotFather
2. Send: /newbot
3. Choose a name (e.g., "My Sportsape BitBot Bot")
4. Choose a username (e.g., "mySportsapeV2_bot")
5. Copy the Bot Token provided
6. Start a chat with your new bot
7. Get your Chat ID from @userinfobot"""
        
        instructions_label = tk.Label(
            instructions_frame,
            text=instructions_text,
            font=('Consolas', 9),
            bg='#1a1a1a',
            fg='#ffffff',
            justify='left'
        )
        instructions_label.pack(anchor='w')
        
        # Bot Token field
        token_frame = tk.Frame(main_frame, bg='#0a0a0a')
        token_frame.pack(fill='x', pady=(0, 15))
        
        tk.Label(
            token_frame,
            text="🔑 Bot Token:",
            font=('Arial', 10, 'bold'),
            bg='#0a0a0a',
            fg='#00ff00'
        ).pack(anchor='w', pady=(0, 5))
        
        token_entry = tk.Entry(
            token_frame,
            textvariable=self.telegram_token,
            font=('Consolas', 10),
            bg='#1a1a1a',
            fg='#ffffff',
            insertbackground='#00ff00',
            relief='flat',
            width=50
        )
        token_entry.pack(fill='x', ipady=5)
        
        # Chat ID field
        chat_frame = tk.Frame(main_frame, bg='#0a0a0a')
        chat_frame.pack(fill='x', pady=(0, 20))
        
        tk.Label(
            chat_frame,
            text="💬 Chat ID:",
            font=('Arial', 10, 'bold'),
            bg='#0a0a0a',
            fg='#00ff00'
        ).pack(anchor='w', pady=(0, 5))
        
        chat_entry = tk.Entry(
            chat_frame,
            textvariable=self.telegram_chat_id,
            font=('Consolas', 10),
            bg='#1a1a1a',
            fg='#ffffff',
            insertbackground='#00ff00',
            relief='flat',
            width=50
        )
        chat_entry.pack(fill='x', ipady=5)
        
        # Status label
        status_label = tk.Label(
            main_frame,
            text="",
            font=('Arial', 9),
            bg='#0a0a0a',
            fg='#888888'
        )
        status_label.pack(pady=(0, 15))
        
        # Buttons frame
        buttons_frame = tk.Frame(main_frame, bg='#0a0a0a')
        buttons_frame.pack(fill='x')
        
        def test_connection():
            """Test the Telegram bot connection"""
            token = self.telegram_token.get().strip()
            chat_id = self.telegram_chat_id.get().strip()
            
            if not token or not chat_id:
                status_label.config(text="❌ Please fill in both fields", fg='#ff0000')
                return
            
            status_label.config(text="⏳ Testing connection...", fg='#ffaa00')
            dialog.update()
            
            try:
                import telegram
                bot = telegram.Bot(token=token)
                bot.send_message(
                    chat_id=chat_id,
                    text="✅ *Sportsape BitBot Connection Test Successful!*\n\nYour bot is ready for remote control.",
                    parse_mode='Markdown'
                )
                status_label.config(text="✅ Connection successful! Message sent to Telegram", fg='#00ff00')
            except Exception as e:
                status_label.config(text=f"❌ Connection failed: {str(e)[:50]}...", fg='#ff0000')
        
        def save_and_start():
            """Save configuration and start the bot"""
            token = self.telegram_token.get().strip()
            chat_id = self.telegram_chat_id.get().strip()
            
            if not token or not chat_id:
                status_label.config(text="❌ Please fill in both fields", fg='#ff0000')
                return
            
            # Save to config
            self.config['telegram_token'] = token
            self.config['telegram_chat_id'] = chat_id
            self.save_config()
            
            # Stop existing bot if running
            if self.telegram_bot and self.telegram_bot.running:
                self.telegram_bot.stop()
            
            # Start new bot
            self.telegram_bot = BetFlowTelegramBot(token, chat_id, self)
            success = self.telegram_bot.start()
            
            if success:
                self.log("✅ Telegram bot connected and ready for remote control!")
                messagebox.showinfo(
                    "Success",
                    "Telegram bot connected successfully!\n\nSend /help to your bot to see available commands."
                )
                dialog.destroy()
            else:
                status_label.config(text="❌ Failed to start bot", fg='#ff0000')
        
        # Test button
        test_btn = tk.Button(
            buttons_frame,
            text="🧪 Test Connection",
            command=test_connection,
            bg='#2196F3',
            fg='white',
            font=('Arial', 10, 'bold'),
            relief='flat',
            padx=20,
            pady=8,
            cursor='hand2'
        )
        test_btn.pack(side='left', padx=(0, 10))
        
        # Save button
        save_btn = tk.Button(
            buttons_frame,
            text="✅ Save & Connect",
            command=save_and_start,
            bg='#4CAF50',
            fg='white',
            font=('Arial', 10, 'bold'),
            relief='flat',
            padx=20,
            pady=8,
            cursor='hand2'
        )
        save_btn.pack(side='left', padx=(0, 10))
        
        # Cancel button
        cancel_btn = tk.Button(
            buttons_frame,
            text="Cancel",
            command=dialog.destroy,
            bg='#555555',
            fg='white',
            font=('Arial', 10),
            relief='flat',
            padx=20,
            pady=8,
            cursor='hand2'
        )
        cancel_btn.pack(side='right')
        
        # Auto-start bot if already configured
        if self.telegram_token.get() and self.telegram_chat_id.get():
            if not self.telegram_bot or not self.telegram_bot.running:
                status_label.config(text="💡 Bot credentials found. Click 'Save & Connect' to start.", fg='#ffaa00')

    def open_ai_hub(self):
        """Open AI HUB dialog - Control AI, API keys, training, and system health"""
        # Create AI HUB window
        hub_window = tk.Toplevel(self.root)
        hub_window.title("🤖 AI HUB - Control Center")
        hub_window.geometry("900x700")
        hub_window.configure(bg='#1e1e1e')
        
        # Center the window
        hub_window.transient(self.root)
        hub_window.grab_set()
        
        # Make it resizable for better UX
        hub_window.resizable(True, True)
        
        # Initialize training state (CRITICAL - prevents AttributeError)
        training_state = {'active': False, 'stop_requested': False}
        
        # Cleanup on window close
        def on_close():
            """Handle window close - cleanup resources"""
            try:
                # Stop any active training
                if training_state.get('active', False):
                    training_state['stop_requested'] = True
                    if hasattr(self, 'ai_learning') and self.ai_learning:
                        try:
                            if self.ai_learning.is_observing:
                                self.ai_learning.stop_observation_mode()
                        except:
                            pass
                # Cancel scheduled updates
                if hasattr(hub_window, '_update_jobs'):
                    for job_id in hub_window._update_jobs:
                        try:
                            hub_window.after_cancel(job_id)
                        except:
                            pass
            except:
                pass
            hub_window.destroy()
        
        hub_window.protocol("WM_DELETE_WINDOW", on_close)
        hub_window._update_jobs = []  # Track scheduled updates for cleanup
        
        # Header
        header_frame = tk.Frame(hub_window, bg='#2d2d2d', pady=10)
        header_frame.pack(fill='x')
        
        title_label = tk.Label(
            header_frame,
            text="🤖 AI HUB - Control Center",
            font=('Arial', 16, 'bold'),
            fg='#00ff00',
            bg='#2d2d2d'
        )
        title_label.pack()
        
        subtitle_label = tk.Label(
            header_frame,
            text="Manage AI API Keys, Training, System Health & Guidelines",
            font=('Arial', 9),
            fg='#888888',
            bg='#2d2d2d'
        )
        subtitle_label.pack()
        
        # Close button in header
        close_btn = tk.Button(
            header_frame,
            text="✕ Close",
            command=on_close,
            bg='#ff4444',
            fg='white',
            font=('Arial', 9, 'bold'),
            width=10
        )
        close_btn.pack(side='right', padx=10)
        
        # Notebook for tabs - OPTIMIZED FOR SMOOTH TAB SWITCHING
        notebook = ttk.Notebook(hub_window)
        notebook.pack(fill='both', expand=True, padx=10, pady=10)
        
        # Smooth tab switching - prevent glitches when changing tabs
        def on_tab_changed(event):
            """Handle tab change smoothly without glitches"""
            try:
                # Update display immediately for smooth transition
                selected_tab = event.widget.select()
                event.widget.update_idletasks()
                # Force small delay to ensure rendering completes
                hub_window.after(10, lambda: hub_window.update_idletasks())
            except:
                pass  # Ignore errors during tab switch
        
        notebook.bind("<<NotebookTabChanged>>", on_tab_changed)
        
        # Tab 1: API Keys
        api_tab = tk.Frame(notebook, bg='#1e1e1e')
        notebook.add(api_tab, text="🔑 API Keys")
        
        api_frame = tk.LabelFrame(api_tab, text="AI API Key Configuration", fg='#00ff00', bg='#1e1e1e', font=('Arial', 11, 'bold'))
        api_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        tk.Label(api_frame, text="DeepSeek / OpenRouter API Key:", fg='white', bg='#1e1e1e', font=('Arial', 10)).pack(anchor='w', padx=10, pady=5)
        
        api_key_frame = tk.Frame(api_frame, bg='#1e1e1e')
        api_key_frame.pack(fill='x', padx=10, pady=5)
        
        self.ai_api_key_entry = tk.Entry(api_key_frame, bg='#2d2d2d', fg='#00ff00', font=('Arial', 10), show='*')
        self.ai_api_key_entry.pack(side='left', fill='x', expand=True)
        
        # Load current API key if available
        current_key = os.getenv("DEEPSEEK_API_KEY") or os.getenv("OPENROUTER_API_KEY") or ""
        if current_key:
            self.ai_api_key_entry.insert(0, current_key[:20] + "..." if len(current_key) > 20 else current_key)
        
        def save_api_key():
            """Save API key and update system immediately"""
            new_key = self.ai_api_key_entry.get().strip()
            if not new_key:
                messagebox.showwarning("Warning", "Please enter an API key")
                return
            
            try:
                # Set environment variable
                os.environ["DEEPSEEK_API_KEY"] = new_key
                os.environ["OPENROUTER_API_KEY"] = new_key
                
                # Reinitialize AI engine with new key (robust error handling)
                if self.headless and hasattr(self.headless, 'ai_engine') and self.headless.ai_engine:
                    self.headless.ai_engine.api_key = new_key
                    self.headless.ai_engine.enabled = bool(new_key)
                    log_message(f"✅ AI API key updated - AI Engine {'enabled' if self.headless.ai_engine.enabled else 'disabled'}")
                else:
                    log_message("⚠️ AI Engine not available - key saved to environment only")
                
                # Also update ai_integration if available
                if hasattr(self, 'ai_integration') and self.ai_integration and self.ai_integration.ai_engine:
                    self.ai_integration.ai_engine.api_key = new_key
                    self.ai_integration.ai_engine.enabled = bool(new_key)
                
                messagebox.showinfo("Success", "✅ API key saved and applied immediately!\n\nAI Engine is now active.")
                self.log("✅ AI API key updated successfully")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save API key: {str(e)}")
                self.log(f"❌ Failed to save API key: {e}")
        
        tk.Button(api_key_frame, text="💾 Save & Apply", command=save_api_key, bg='#4CAF50', fg='white', font=('Arial', 9, 'bold')).pack(side='left', padx=5)
        
        tk.Label(api_frame, text="💡 Tip: Get API keys from:\n• OpenRouter.ai (supports DeepSeek, GPT-4, Claude, etc.)\n• DeepSeek.ai (direct API)", 
                fg='#888888', bg='#1e1e1e', font=('Arial', 8), justify='left').pack(anchor='w', padx=10, pady=10)
        
        # Tab 2: Training Mode
        training_tab = tk.Frame(notebook, bg='#1e1e1e')
        notebook.add(training_tab, text="🎓 Training")
        
        training_frame = tk.LabelFrame(training_tab, text="AI Training Mode", fg='#00ff00', bg='#1e1e1e', font=('Arial', 11, 'bold'))
        training_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        tk.Label(training_frame, text="Train AI by performing actions in visible browser:", fg='white', bg='#1e1e1e', font=('Arial', 10)).pack(anchor='w', padx=10, pady=5)
        
        training_buttons_frame = tk.Frame(training_frame, bg='#1e1e1e')
        training_buttons_frame.pack(fill='x', padx=10, pady=10)
        
        def start_training_mode(operation_type):
            """Start training mode for specific operation"""
            # Robust check for AI engine availability
            if not (hasattr(self, 'headless') and self.headless and 
                    hasattr(self.headless, 'ai_engine') and self.headless.ai_engine and 
                    self.headless.ai_engine.enabled):
                messagebox.showwarning("AI Disabled", "Please set an API key first in the API Keys tab")
                return
            
            phones = self.phone_text.get('1.0', tk.END).strip()
            password = self.password_entry.get().strip()
            
            if not phones or not password:
                messagebox.showwarning("Missing Info", "Please enter phone numbers and password")
                return
            
            phone_list = [p.strip() for p in phones.split('\n') if p.strip()]
            if not phone_list:
                messagebox.showwarning("No Accounts", "Please enter at least one phone number")
                return
            
            # Confirm training mode
            confirm = messagebox.askyesno(
                "Start Training Mode",
                f"Start AI training for {operation_type}?\n\n"
                "A visible browser will open.\n"
                "Perform actions manually and AI will learn from them.\n\n"
                "This helps AI understand your workflow better."
            )
            
            if not confirm:
                return
            
            # Mark training as active
            training_state['active'] = True
            training_state['stop_requested'] = False
            
            def run_training():
                training_active = {'value': True}
                observation_stopped = {'value': False}
                
                try:
                    self.log(f"🎓 Starting AI Training Mode for {operation_type}...")
                    self.log("📖 Opening visible browser - YOU will perform actions manually...")
                    self.log("💡 AI will watch and learn from your actions")
                    
                    # Get base URL
                    base_url = self.target_url.get() if hasattr(self, 'target_url') else 'https://www.odibets.com'
                    
                    # Check if AI learning system is available
                    if not self.ai_learning:
                        self.log("❌ AI Learning system not available - cannot start training mode")
                        return
                    
                    # Start observation mode (opens visible browser)
                    self.log("🌐 Opening visible browser window...")
                    success = self.ai_learning.start_observation_mode(base_url, operation_type.lower())
                    
                    if not success:
                        self.log("❌ Failed to open browser for training")
                        return
                    
                    self.log("="*60)
                    self.log("✅ VISIBLE BROWSER IS NOW OPEN!")
                    self.log("="*60)
                    self.log("📝 INSTRUCTIONS:")
                    self.log("   1. Browser window should be visible on your screen")
                    self.log("   2. Perform your actions manually (login, place bets, etc.)")
                    self.log("   3. AI is watching and learning from everything you do")
                    self.log("   4. When done, click the STOP button below")
                    self.log("="*60)
                    
                    # Wait for user to perform actions (keep browser open)
                    # Browser stays open until user clicks stop or closes window
                    self.log("⏳ Waiting for you to perform actions...")
                    self.log("💡 Take your time - perform all actions you want AI to learn")
                    
                    # Keep browser open and monitor for closure
                    max_wait_time = 3600  # 1 hour max
                    check_interval = 2  # Check every 2 seconds
                    elapsed = 0
                    
                    while training_active['value'] and elapsed < max_wait_time:
                        # Check if stop was requested
                        if training_state['stop_requested']:
                            self.log("🛑 Stop button clicked - stopping training...")
                            training_active['value'] = False
                            break
                        
                        time.sleep(check_interval)
                        elapsed += check_interval
                        
                        # Check if browser was closed
                        try:
                            if self.ai_learning.driver:
                                # Try to get current URL (will fail if browser closed)
                                try:
                                    current_url = self.ai_learning.driver.current_url
                                except:
                                    # Browser was closed
                                    self.log("⚠️ Browser window was closed")
                                    training_active['value'] = False
                                    break
                        except:
                            # Driver doesn't exist anymore
                            training_active['value'] = False
                            break
                        
                        # Give status update every 30 seconds
                        if elapsed % 30 == 0:
                            actions_count = self.ai_learning.session_stats.get('actions_observed', 0)
                            self.log(f"📊 Training in progress... ({actions_count} actions recorded so far)")
                    
                    # Stop observation and save learning
                    if not observation_stopped['value']:
                        self.log("🛑 Stopping observation mode...")
                        learning_data = self.ai_learning.stop_observation_mode()
                        observation_stopped['value'] = True
                        
                        # Process and save learned actions
                        actions_count = learning_data.get('actions_count', 0)
                        if actions_count > 0:
                            self.log(f"✅ Training complete! AI recorded {actions_count} actions")
                            self.log("🧠 AI has learned from your actions and will use them in future operations")
                            
                            # Save training session
                            if self.headless.ai_engine and self.headless.ai_engine.enabled:
                                try:
                                    self.headless.ai_engine.remember_repeated_task(
                                        f'training_{operation_type.lower()}',
                                        {
                                            'operation': operation_type,
                                            'actions_count': actions_count,
                                            'learned_selectors': learning_data.get('unique_selectors', 0),
                                            'session_duration': elapsed
                                        },
                                        True
                                    )
                                    self.log("💾 Training session saved to AI knowledge base")
                                except Exception as e:
                                    self.log(f"⚠️ Could not save training session: {e}")
                        else:
                            self.log("⚠️ No actions were recorded - browser may have been closed too quickly")
                            self.log("💡 Please try again and perform some actions before closing")
                    
                except Exception as e:
                    self.log(f"❌ Training error: {e}")
                    import traceback
                    self.log(f"   Details: {traceback.format_exc()[:200]}")
                    
                    # Ensure browser is closed
                    try:
                        if self.ai_learning and self.ai_learning.is_observing:
                            self.ai_learning.stop_observation_mode()
                    except:
                        pass
                    finally:
                        # Mark training as inactive
                        training_state['active'] = False
            
            threading.Thread(target=run_training, daemon=True).start()
        
        def stop_training():
            """Stop current training session"""
            if not training_state['active']:
                messagebox.showinfo("Not Active", "No training session is currently active")
                return
            
            training_state['stop_requested'] = True
            self.log("🛑 Stop requested - training will end after current action completes...")
        
        tk.Button(training_buttons_frame, text="🔄 Train Rollover", 
                 command=lambda: start_training_mode("Rollover"),
                 bg='#FF9800', fg='white', width=20, font=('Arial', 9, 'bold')).pack(side='left', padx=5, pady=5)
        
        tk.Button(training_buttons_frame, text="🎁 Train SUPA5", 
                 command=lambda: start_training_mode("SUPA5"),
                 bg='#E91E63', fg='white', width=20, font=('Arial', 9, 'bold')).pack(side='left', padx=5, pady=5)
        
        tk.Button(training_buttons_frame, text="🎯 Train Odileagues", 
                 command=lambda: start_training_mode("Odileagues"),
                 bg='#4CAF50', fg='white', width=20, font=('Arial', 9, 'bold')).pack(side='left', padx=5, pady=5)
        
        # Stop button
        stop_training_btn = tk.Button(training_buttons_frame, text="🛑 Stop Training", 
                                      command=stop_training,
                                      bg='#F44336', fg='white', width=20, font=('Arial', 9, 'bold'))
        stop_training_btn.pack(side='left', padx=5, pady=5)
        
        tk.Label(training_frame, 
                text="💡 How it works:\n"
                     "1. Click a training button above\n"
                     "2. Visible browser opens\n"
                     "3. Perform actions manually (login, place bets, etc.)\n"
                     "4. AI watches and learns from your actions\n"
                     "5. AI creates permanent fixes based on what works\n\n"
                     "📝 Note: Visible browser mode (stealth disabled) for easy observation",
                fg='#888888', bg='#1e1e1e', font=('Arial', 8), justify='left').pack(anchor='w', padx=10, pady=10)
        
        # Tab 3: System Health
        health_tab = tk.Frame(notebook, bg='#1e1e1e')
        notebook.add(health_tab, text="🏥 System Health")
        
        health_frame = tk.LabelFrame(health_tab, text="System Status", fg='#00ff00', bg='#1e1e1e', font=('Arial', 11, 'bold'))
        health_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        self.health_text = scrolledtext.ScrolledText(health_frame, height=20, bg='#2d2d2d', fg='#00ff00', font=('Courier', 9))
        self.health_text.pack(fill='both', expand=True, padx=10, pady=10)
        
        def update_health_display():
            """Update system health display"""
            try:
                health_info = []
                health_info.append("=" * 60)
                health_info.append("🤖 AI SYSTEM HEALTH")
                health_info.append("=" * 60)
                health_info.append("")
                
                # AI Engine Status (robust error handling)
                try:
                    if (hasattr(self, 'headless') and self.headless and 
                        hasattr(self.headless, 'ai_engine') and self.headless.ai_engine):
                        if self.headless.ai_engine.enabled:
                            health_info.append("✅ AI Engine: ENABLED")
                            health_info.append(f"   • API Key: {'Set' if getattr(self.headless.ai_engine, 'api_key', None) else 'Not Set'}")
                            health_info.append(f"   • Error Patterns Learned: {len(getattr(self.headless.ai_engine, 'error_patterns', {}))}")
                            health_info.append(f"   • Permanent Fixes: {len(getattr(self.headless.ai_engine, 'permanent_fixes', {}))}")
                            health_info.append(f"   • Selector Learnings: {len(getattr(self.headless.ai_engine, 'selector_learnings', {}))}")
                            health_info.append(f"   • Operation History: {len(getattr(self.headless.ai_engine, 'operation_history', []))} entries")
                        else:
                            health_info.append("⚠️  AI Engine: DISABLED (No API key)")
                    else:
                        health_info.append("❌ AI Engine: NOT INITIALIZED")
                except Exception as e:
                    health_info.append(f"❌ AI Engine: ERROR - {str(e)[:50]}")
                
                health_info.append("")
                health_info.append("-" * 60)
                health_info.append("🌐 NETWORK STATUS")
                health_info.append("-" * 60)
                health_info.append(f"   • Status: {'✅ Online' if self.network_online else '❌ Offline'}")
                
                health_info.append("")
                health_info.append("-" * 60)
                health_info.append("🔧 SYSTEM COMPONENTS")
                health_info.append("-" * 60)
                
                # Check components (robust error handling)
                try:
                    components = {
                        "BetFlowHeadless": hasattr(self, 'headless') and self.headless is not None,
                        "Browser Pool": (hasattr(self, 'headless') and self.headless and 
                                       hasattr(self.headless, 'browser_pool') and self.headless.browser_pool is not None),
                        "API Client": (hasattr(self, 'headless') and self.headless and 
                                     hasattr(self.headless, 'session') and self.headless.session is not None),
                        "Network Handler": (hasattr(self, 'headless') and self.headless and 
                                          hasattr(self.headless, 'network_status_callback')),
                        "AI Integration": hasattr(self, 'ai_integration') and self.ai_integration is not None,
                        "AI Learning": hasattr(self, 'ai_learning') and self.ai_learning is not None,
                    }
                    
                    for component, status in components.items():
                        health_info.append(f"   {'✅' if status else '❌'} {component}: {'OK' if status else 'Missing'}")
                except Exception as e:
                    health_info.append(f"   ⚠️ Component check error: {str(e)[:40]}")
                
                health_info.append("")
                health_info.append("-" * 60)
                health_info.append("📊 AI LEARNING STATS")
                health_info.append("-" * 60)
                
                try:
                    if (hasattr(self, 'headless') and self.headless and 
                        hasattr(self.headless, 'ai_engine') and self.headless.ai_engine and 
                        self.headless.ai_engine.enabled):
                        system_state = getattr(self.headless.ai_engine, 'system_state', {})
                        success_metrics = system_state.get('success_metrics', {})
                        if success_metrics:
                            health_info.append(f"   • Tracked Tasks: {len(success_metrics)}")
                            total_successes = sum(m.get('successes', 0) for m in success_metrics.values())
                            total_attempts = sum(m.get('attempts', 0) for m in success_metrics.values())
                            if total_attempts > 0:
                                overall_rate = (total_successes / total_attempts) * 100
                                health_info.append(f"   • Overall Success Rate: {overall_rate:.1f}%")
                except Exception as e:
                    health_info.append(f"   ⚠️ Stats error: {str(e)[:40]}")
                
                health_info.append("")
                health_info.append("=" * 60)
                
                self.health_text.delete(1.0, tk.END)
                self.health_text.insert(1.0, "\n".join(health_info))
                
                # Schedule next update (with cleanup tracking)
                if hub_window.winfo_exists():
                    job_id = hub_window.after(5000, update_health_display)  # Update every 5 seconds
                    if hasattr(hub_window, '_update_jobs'):
                        hub_window._update_jobs.append(job_id)
            except Exception as e:
                self.log(f"⚠️ Health update error: {e}")
        
        update_health_display()
        
        refresh_btn = tk.Button(health_frame, text="🔄 Refresh Now", command=update_health_display, bg='#2196F3', fg='white')
        refresh_btn.pack(pady=5)
        
        # Tab 4: AI Activity
        activity_tab = tk.Frame(notebook, bg='#1e1e1e')
        notebook.add(activity_tab, text="📡 AI Activity")
        
        activity_frame = tk.LabelFrame(activity_tab, text="Live AI Operations", fg='#00ff00', bg='#1e1e1e', font=('Arial', 11, 'bold'))
        activity_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        self.activity_text = scrolledtext.ScrolledText(activity_frame, height=20, bg='#2d2d2d', fg='#00ff00', font=('Courier', 9))
        self.activity_text.pack(fill='both', expand=True, padx=10, pady=10)
        
        def update_activity_display():
            """Update AI activity display"""
            try:
                activity_info = []
                activity_info.append("=" * 60)
                activity_info.append("🤖 LIVE AI ACTIVITY")
                activity_info.append("=" * 60)
                activity_info.append("")
                
                try:
                    if (hasattr(self, 'headless') and self.headless and 
                        hasattr(self.headless, 'ai_engine') and self.headless.ai_engine and 
                        self.headless.ai_engine.enabled):
                        # Show recent AI operations (robust access)
                        operation_history = getattr(self.headless.ai_engine, 'operation_history', [])
                        recent_ops = operation_history[-20:] if operation_history else []  # Last 20
                        if recent_ops:
                            activity_info.append("📋 RECENT OPERATIONS:")
                            for op in reversed(recent_ops):
                                if isinstance(op, dict):
                                    status_icon = "✅" if op.get('status') == 'success' else "❌"
                                    activity_info.append(f"   {status_icon} {op.get('operation', 'unknown')} - {str(op.get('timestamp', ''))[:19]}")
                            activity_info.append("")
                        
                        # Show active operations
                        system_state = getattr(self.headless.ai_engine, 'system_state', {})
                        active_ops = system_state.get('active_operations', [])
                        if active_ops:
                            activity_info.append("🔄 ACTIVE OPERATIONS:")
                            for op in active_ops:
                                activity_info.append(f"   • {op}")
                            activity_info.append("")
                        
                        # Show recent improvements
                        self_improvement_log = getattr(self.headless.ai_engine, 'self_improvement_log', [])
                        improvements = self_improvement_log[-10:] if self_improvement_log else []
                        if improvements:
                            activity_info.append("🧠 RECENT IMPROVEMENTS:")
                            for imp in reversed(improvements):
                                if isinstance(imp, dict):
                                    activity_info.append(f"   ✨ {imp.get('improvement', 'N/A')} - {str(imp.get('timestamp', ''))[:19]}")
                            activity_info.append("")
                        
                        # Show applied fixes
                        fix_history = getattr(self.headless.ai_engine, 'fix_history', [])
                        if fix_history:
                            recent_fixes = fix_history[-10:]
                            activity_info.append("🔧 RECENT FIXES APPLIED:")
                            for fix in reversed(recent_fixes):
                                if isinstance(fix, dict):
                                    activity_info.append(f"   🔧 {fix.get('operation', 'N/A')} - {str(fix.get('error', 'N/A'))[:40]}")
                    else:
                        activity_info.append("⚠️ AI Engine is disabled")
                        activity_info.append("   Set an API key in the API Keys tab to enable")
                except Exception as e:
                    activity_info.append(f"⚠️ Activity display error: {str(e)[:50]}")
                
                activity_info.append("")
                activity_info.append("=" * 60)
                
                self.activity_text.delete(1.0, tk.END)
                self.activity_text.insert(1.0, "\n".join(activity_info))
                
                # Schedule next update (with cleanup tracking)
                if hub_window.winfo_exists():
                    job_id = hub_window.after(3000, update_activity_display)  # Update every 3 seconds
                    if hasattr(hub_window, '_update_jobs'):
                        hub_window._update_jobs.append(job_id)
            except Exception as e:
                self.log(f"⚠️ Activity update error: {e}")
        
        update_activity_display()
        
        # Tab 5: Guidelines
        guidelines_tab = tk.Frame(notebook, bg='#1e1e1e')
        notebook.add(guidelines_tab, text="📚 Guidelines")
        
        guidelines_frame = tk.LabelFrame(guidelines_tab, text="System Operation Guidelines", fg='#00ff00', bg='#1e1e1e', font=('Arial', 11, 'bold'))
        guidelines_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        guidelines_text = scrolledtext.ScrolledText(guidelines_frame, height=25, bg='#2d2d2d', fg='#00ff00', font=('Arial', 9))
        guidelines_text.pack(fill='both', expand=True, padx=10, pady=10)
        
        guidelines_content = """╔══════════════════════════════════════════════════════════════╗
║        🤖 SPORTSAPE BITBOT BALANCE CHECKER - SYSTEM GUIDELINES        ║
╚══════════════════════════════════════════════════════════════╝

📋 HOW THE SYSTEM OPERATES:

┌─ 🔄 ROLLOVER OPERATION ──────────────────────────────────────┐
│                                                                │
│  Purpose: Transfer money between accounts at 1.88 odds       │
│                                                                │
│  How it works:                                                 │
│  1. Finds matches with Over/Under 2.5 odds = 1.88/1.88        │
│  2. Splits accounts 50/50 (half OVER, half UNDER)            │
│  3. Places bets - 50% lose stake, 50% win stake               │
│  4. Money consolidates at 1.88 odds                          │
│  5. Reuses matches if time allows (multi-round mode)          │
│                                                                │
│  Requirements:                                                 │
│  • Minimum 2 accounts (even number)                           │
│  • Each account balance >= stake amount                       │
│  • Match must be 80+ seconds away                             │
│                                                                │
│  AI Enhancements:                                              │
│  • Auto-fixes login/logout errors                             │
│  • Auto-fixes bet placement errors                            │
│  • Remembers successful patterns                              │
│  • Optimizes for large batches                                │
│                                                                │
└───────────────────────────────────────────────────────────────┘

┌─ 🎁 SUPA5 OPERATION ──────────────────────────────────────────┐
│                                                                │
│  Purpose: Claim 50 KES bonus by placing 5+ bets               │
│                                                                │
│  How it works:                                                 │
│  1. Navigates to Promotions page                              │
│  2. Logs in to account                                        │
│  3. Clicks "OdiLeague Supa5 Play Now" button                 │
│  4. Places 6 bets (3 pairs of Over/Under 2.5)                 │
│     • 50 KES per bet                                          │
│     • Same match, guaranteed win                              │
│  5. Logs out and repeats for next account                    │
│                                                                │
│  Strategy:                                                     │
│  • Targets 1.88/1.88 odds on O/U 2.5                         │
│  • Places Over + Under on same match                          │
│  • Ensures win in each account                                │
│                                                                │
│  AI Enhancements:                                              │
│  • AI selects best match for O/U 2.5 pairs                    │
│  • Auto-fixes navigation errors                               │
│  • Auto-fixes bet placement errors                            │
│                                                                │
└───────────────────────────────────────────────────────────────┘

┌─ 💰 WITHDRAWAL OPERATION ─────────────────────────────────────┐
│                                                                │
│  Purpose: Withdraw funds from accounts                        │
│                                                                │
│  How it works:                                                 │
│  1. Uses API-first approach (fastest)                          │
│  2. Falls back to browser if API fails                        │
│  3. Handles M-Pesa withdrawal flow                           │
│                                                                │
│  AI Enhancements:                                              │
│  • Auto-retries on failure                                    │
│  • Learns from successful withdrawals                         │
│                                                                │
└───────────────────────────────────────────────────────────────┘

┌─ 🤖 AI SYSTEM OPERATION ─────────────────────────────────────┐
│                                                                │
│  AI Role: Enhancement, not control                            │
│                                                                │
│  What AI Does:                                                 │
│  ✅ Fixes errors automatically                                │
│  ✅ Learns from patterns                                      │
│  ✅ Suggests improvements                                     │
│  ✅ Optimizes performance                                     │
│  ✅ Handles failures gracefully                               │
│                                                                │
│  What AI Does NOT:                                             │
│  ❌ Control operations (user always in control)               │
│  ❌ Bypass user controls                                      │
│  ❌ Make decisions alone                                      │
│                                                                │
│  How AI Learns:                                                │
│  1. Tracks all operations                                      │
│  2. Records success/failure patterns                          │
│  3. After 3+ failures → Creates permanent fix                │
│  4. Next time → Fix applies automatically                     │
│                                                                │
│  Permanent Fixes:                                              │
│  • Saved to disk (persist forever)                           │
│  • Apply automatically when error occurs                     │
│  • System gets better over time                               │
│                                                                │
└───────────────────────────────────────────────────────────────┘

┌─ 🛡️ STEALTH MODE ─────────────────────────────────────────────┐
│                                                                │
│  Purpose: Avoid bot detection                                 │
│                                                                │
│  Features:                                                     │
│  • Human-like delays                                          │
│  • Randomized timing                                          │
│  • Stealth browser headers                                    │
│  • Natural mouse movements                                    │
│  • Anti-bot bypass techniques                                │
│                                                                │
│  Always Active:                                                │
│  • All browser operations use stealth mode                    │
│  • AI operations are not flagged as bots                      │
│                                                                │
└───────────────────────────────────────────────────────────────┘

┌─ 📊 LARGE BATCH HANDLING ─────────────────────────────────────┐
│                                                                │
│  For 100+ accounts:                                            │
│  • Auto-chunks into smaller groups                            │
│  • Progress checkpoints                                       │
│  • Error threshold monitoring                                 │
│  • Memory optimization                                        │
│                                                                │
│  AI optimizes automatically based on account count           │
│                                                                │
└───────────────────────────────────────────────────────────────┘

💡 TIPS:
• Set API key in AI HUB for maximum intelligence
• Use training mode to teach AI your workflow
• Check System Health regularly
• AI gets smarter with each operation

⚡ Version 5.0.0 - AI-Powered & Production Ready"""
        
        guidelines_text.insert(1.0, guidelines_content)
        guidelines_text.config(state='disabled')  # Read-only
        
        # Footer with close button
        footer_frame = tk.Frame(hub_window, bg='#2d2d2d', pady=5)
        footer_frame.pack(fill='x', side='bottom')
        
        tk.Label(footer_frame, text="⚡ Sportsape BitBot Balance Checker v5.0.0", 
                fg='#888888', bg='#2d2d2d', font=('Arial', 8)).pack(side='left', padx=10)
        
        tk.Button(footer_frame, text="✕ Close AI HUB", command=on_close, 
                 bg='#ff4444', fg='white', font=('Arial', 9, 'bold')).pack(side='right', padx=10)

    def emergency_stop(self):
        """Emergency stop button - FORCEFULLY kills ALL running operations"""
        try:
            # Set kill switch flags IMMEDIATELY (CRITICAL - must be first!)
            self.headless.running = False
            self.running = False
            
            # Visual feedback
            self.stop_btn.config(bg='#FFD700', text='⏹️ STOPPING...')
            self.log("🛑 EMERGENCY STOP ACTIVATED - Forcefully stopping ALL operations...")
            
            # 🔥 CRITICAL: Stop browser pool IMMEDIATELY (stops all browser operations)
            try:
                if hasattr(self.headless, 'browser_pool') and self.headless.browser_pool:
                    self.log("🧹 Closing browser pool...")
                    self.headless.browser_pool.close_all()
            except Exception as e:
                self.log(f"⚠️ Browser pool close warning: {str(e)[:50]}")
            
            # 🔥 CRITICAL: Close selenium driver IMMEDIATELY (stops bet placement)
            try:
                if hasattr(self.headless, 'selenium_fetcher') and self.headless.selenium_fetcher:
                    if hasattr(self.headless.selenium_fetcher, 'driver') and self.headless.selenium_fetcher.driver:
                        self.log("🧹 Terminating Selenium driver...")
                        try:
                            self.headless.selenium_fetcher.driver.quit()
                        except:
                            pass
            except Exception as e:
                self.log(f"⚠️ Selenium driver close warning: {str(e)[:50]}")
            
            # 🔥 CRITICAL: Close standalone selenium driver
            try:
                if hasattr(self.headless, 'selenium_driver') and self.headless.selenium_driver:
                    self.log("🧹 Terminating standalone Selenium driver...")
                    try:
                        self.headless.selenium_driver.quit()
                    except:
                        pass
            except:
                pass
            
            # CRITICAL: Kill ALL browser processes IMMEDIATELY
            self.log("🧹 Terminating all browser processes...")
            try:
                from cleanup_and_killswitch_helper import kill_all_betflow_processes
                kill_all_betflow_processes()
            except:
                # Fallback: direct system commands
                import subprocess
                try:
                    subprocess.run('taskkill /F /IM chromedriver.exe /T 2>nul', shell=True, timeout=2)
                    subprocess.run('taskkill /F /IM node.exe /T 2>nul', shell=True, timeout=2)
                    # Note: We don't kill chrome.exe anymore (would close user's browser)
                except:
                    pass
            
            # 🔥 CRITICAL: Forcefully shutdown all ThreadPoolExecutors
            try:
                if hasattr(self.headless, 'shutdown_all_executors'):
                    self.log("🧹 Forcefully shutting down all thread pools...")
                    self.headless.shutdown_all_executors()
            except Exception as e:
                self.log(f"⚠️ Executor shutdown warning: {str(e)[:50]}")
            
            # 🔥 CRITICAL: Force stop all background threads and subprocesses
            import threading
            import sys
            import os
            import psutil
            
            try:
                # Get all active threads except main thread
                active_threads = [t for t in threading.enumerate() if t != threading.main_thread() and t.is_alive()]
                if active_threads:
                    self.log(f"🧹 Stopping {len(active_threads)} background threads...")
                    # Set their running flags to False (most threads check this)
                    for thread in active_threads:
                        try:
                            # Try to set running attribute if it exists
                            if hasattr(thread, '_target') and hasattr(thread, '_args'):
                                pass  # Threads will check self.running flag
                        except:
                            pass
            except Exception as e:
                self.log(f"⚠️ Thread stop warning: {str(e)[:50]}")
            
            # 🔥 CRITICAL: Kill ALL child processes (chromedriver, node, etc.)
            try:
                # Try to use psutil if available for better process management
                try:
                    import psutil
                    current_process = psutil.Process(os.getpid())
                    children = current_process.children(recursive=True)
                    if children:
                        self.log(f"🧹 Terminating {len(children)} child processes...")
                        for child in children:
                            try:
                                # Check if it's a process we created
                                name = child.name().lower()
                                if 'chromedriver' in name or 'node' in name:
                                    child.terminate()
                                    try:
                                        child.wait(timeout=1)
                                    except:
                                        child.kill()  # Force kill if terminate doesn't work
                            except:
                                pass
                except ImportError:
                    # psutil not available, use subprocess fallback
                    import subprocess
                    try:
                        self.log("🧹 Terminating child processes (chromedriver, node)...")
                        subprocess.run('taskkill /F /IM chromedriver.exe /T 2>nul', shell=True, timeout=2, creationflags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess, 'CREATE_NO_WINDOW') else 0)
                        subprocess.run('taskkill /F /IM node.exe /T 2>nul', shell=True, timeout=2, creationflags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess, 'CREATE_NO_WINDOW') else 0)
                    except:
                        pass
            except Exception as e:
                self.log(f"⚠️ Process termination warning: {str(e)[:50]}")
            
            # Log aggressive stop
            self.log("⏸️  All processes terminated - System halted")
            
            # Force garbage collection to clean up
            import gc
            gc.collect()
            
            # Re-enable buttons after stop
            def reset_system():
                time.sleep(3)  # Longer delay to ensure all threads stop
                try:
                    self.stop_btn.config(bg='#FF0000', text='⏹️ EMERGENCY STOP')
                    self.headless.running = True
                    self.running = True
                    
                    # Re-enable all action buttons
                    try:
                        self.check_balance_btn.config(state='normal')
                        self.extract_btn.config(state='normal')
                    except:
                        pass
                    
                    self.log("✅ System RESET - All operations stopped")
                    self.log("▶️  You can now start new operations safely")
                except:
                    pass
            
            threading.Thread(target=reset_system, daemon=True).start()
        except Exception as e:
            self.log(f"⚠️ Stop error: {str(e)}")
            # Still try to reset flags
            self.headless.running = False
            self.running = False
            self.headless.running = False
            self.running = False
    
    def check_network_status(self):
        """Check if network/internet is available"""
        try:
            # Try to connect to multiple reliable servers with stricter timeout
            test_urls = ['https://www.google.com', 'https://www.cloudflare.com', 'https://1.1.1.1']
            for url in test_urls:
                try:
                    response = requests.head(url, timeout=2)
                    if response.status_code < 500:  # Any response means network is up
                        return True
                except requests.exceptions.ConnectionError:
                    continue  # Try next URL
                except requests.exceptions.Timeout:
                    continue  # Try next URL
                except Exception as e:
                    # Check for specific network-down errors
                    error_str = str(e).lower()
                    if 'unreachable' in error_str or '10051' in error_str or 'failed to establish' in error_str:
                        return False  # Definitely offline
                    continue
            return False  # All attempts failed
        except Exception as e:
            return False
    
    def update_network_status(self):
        """Update network status indicator (runs in background thread)"""
        def check_and_update():
            try:
                is_online = self.check_network_status()
                
                if is_online != self.network_online:
                    self.network_online = is_online
                    
                    # Update GUI in main thread
                    self.root.after(0, lambda: self._update_network_ui(is_online))
            except:
                pass
        
        # Run check in background thread to avoid blocking GUI
        threading.Thread(target=check_and_update, daemon=True).start()
        
        # Schedule next check
        self.root.after(self.network_check_interval, self.update_network_status)
    
    def _update_network_ui(self, is_online):
        """Update network UI (must run in main thread)"""
        try:
            if is_online:
                self.network_label.config(text="● Online", fg='#4CAF50')
                # Only log if status changed from offline to online
                if hasattr(self, '_last_logged_status') and not self._last_logged_status:
                    self.log("✅ Network connection restored")
                    self._last_logged_status = True
            else:
                self.network_label.config(text="● Offline", fg='#F44336')
                # Only log if status changed from online to offline  
                if not hasattr(self, '_last_logged_status') or self._last_logged_status:
                    self.log("⚠️ Network connection lost - Operations will pause")
                    self._last_logged_status = False
        except:
            pass
    
    def start_network_monitor(self):
        """Start periodic network monitoring"""
        self.root.after(1000, self.update_network_status)  # Start after 1 second

    def toggle_auto_scroll(self):
        """Auto-scroll is always on for this version"""
        self.auto_scroll_enabled = True
        self.auto_scroll_btn.config(text="⏬ Auto-Scroll: ALWAYS ON", bg='#4CAF50')
        self.terminal.see(tk.END)
        self.terminal.update_idletasks()
    
    def clear_terminal(self):
        """Clear all terminal content"""
        self.terminal.delete('1.0', tk.END)
        self.log("🗑️ Terminal cleared")
    
    def jump_to_bottom(self):
        """Jump to bottom of terminal and enable auto-scroll"""
        self.terminal.see(tk.END)
        self.terminal.update_idletasks()
        if not self.auto_scroll_enabled:
            self.auto_scroll_enabled = True
            self.auto_scroll_btn.config(text="⏬ Auto-Scroll: ON", bg='#4CAF50')
    

    def toggle_theme(self):
        if self.theme.get() == 'dark':
            self.theme.set('light')
            self.colors = self.light_theme.copy()
            self.log("🌞 Switched to Light theme")
        else:
            self.theme.set('dark')
            self.colors = self.dark_theme.copy()
            self.log("🌙 Switched to Dark theme")

        self.apply_theme()
        self.save_config()  # Save theme preference

    def apply_theme(self):
        def update_widget_recursive(widget):
            try:
                widget_class = widget.winfo_class()
                
                # Handle different widget types
                if isinstance(widget, tk.Button):
                    # Update theme toggle button specifically using stored reference
                    if hasattr(self, 'theme_btn') and widget == self.theme_btn:
                        if self.theme.get() == 'dark':
                            widget.configure(text="🌙 Dark", bg=self.colors.get('panel_alt', '#1f4255'), fg='white')
                        else:
                            widget.configure(text="🌞 Light", bg=self.colors.get('panel_alt', '#e7f3fb'), fg='#12222e')
                    # Keep other buttons with their original colors
                    
                elif isinstance(widget, (tk.Label, tk.LabelFrame)):
                    widget.configure(bg=self.colors.get('panel', self.colors['bg']), fg=self.colors['fg'])
                    
                elif isinstance(widget, (tk.Text, scrolledtext.ScrolledText)):
                    # Keep terminal always green for techy feel
                    if hasattr(self, 'terminal') and widget == self.terminal:
                        widget.configure(
                            bg=self.colors.get('terminal_bg', '#050d12'),
                            fg=self.colors.get('terminal_fg', '#00ff9c')
                        )
                        widget.configure(
                            selectbackground=self.colors.get('terminal_fg', '#00ff9c'),
                            selectforeground=self.colors.get('terminal_bg', '#050d12')
                        )
                    else:
                        widget.configure(bg=self.colors['text_bg'], fg=self.colors['text_fg'])
                        # Update selection colors for better visibility
                        widget.configure(selectbackground='#00a8fa', selectforeground='white')
                    
                elif isinstance(widget, tk.Entry):
                    widget.configure(bg=self.colors['text_bg'], fg=self.colors['text_fg'])
                    widget.configure(insertbackground=self.colors['text_fg'])  # Cursor color
                    
                elif isinstance(widget, (tk.Frame, tk.Toplevel)):
                    widget.configure(bg=self.colors['bg'])
                    
                elif isinstance(widget, tk.PanedWindow):
                    widget.configure(bg=self.colors.get('panel', self.colors['bg']))
                    
                elif isinstance(widget, tk.Checkbutton):
                    widget.configure(
                        bg=self.colors['bg'], 
                        fg=self.colors['fg'],
                        selectcolor=self.colors['bg'],
                        activebackground=self.colors['bg'],
                        activeforeground=self.colors['fg']
                    )
                    
                elif widget_class == 'Scrollbar':
                    # Handle scrollbars
                    widget.configure(
                        bg=self.colors['bg'],
                        troughcolor=self.colors['text_bg'],
                        activebackground=self.colors.get('accent', '#00a8fa')
                    )
                    
                # Recursively update all children
                for child in widget.winfo_children():
                    update_widget_recursive(child)
                    
            except tk.TclError:
                # Skip widgets that don't support certain configurations
                pass

        # Start with root window
        self.root.configure(bg=self.colors['bg'])
        
        # Update all widgets recursively
        for widget in self.root.winfo_children():
            update_widget_recursive(widget)
            
        # Force update display
        self.root.update_idletasks()

    def save_tokens(self):
        phones_text = self.phone_text.get('1.0', tk.END).strip()
        if not phones_text:
            self.log("❌ No phone numbers provided - cannot save tokens")
            return
        
        phone_list = [line.strip() for line in phones_text.split('\n') if line.strip()]
        if not phone_list:
            self.log("❌ No valid phone numbers - cannot save tokens")
            return
        
        password = self.password_entry.get()
        if not password:
            self.log("❌ Please enter password for token saving")
            return
        
        self.log(f"🔑 Starting token extraction for {len(phone_list)} accounts...")
        
        # Create enhanced callback that ensures auto-scroll
        def enhanced_callback(message):
            self.log(message)
            self.ensure_auto_scroll()
        
        threading.Thread(target=self.headless.extract_tokens_for_accounts, args=(phone_list, password, enhanced_callback), daemon=True).start()

    def load_tokens(self):
        if self.headless.load_tokens():
            self.log("✅ Tokens loaded from file")
        else:
            self.log("❌ No tokens file found")

    def auto_discover_api(self):
        """
        Auto-discover API endpoints using Advanced AI approach
        """
        target_url = self.target_url.get().strip()
        if not target_url:
            self.log("❌ Error: Please enter a target URL first")
            return
        
        # Validate URL format
        if not target_url.startswith(('http://', 'https://')):
            target_url = 'https://' + target_url
            self.target_url.set(target_url)
        
        self.log(f"🚀 Starting API Auto-Discovery for: {target_url}")
        self.log("⏳ This may take 30-60 seconds...")
        
        # Get credentials if available (for dynamic discovery)
        phone = None
        password = None
        
        # Check if user provided test credentials
        phones_text = self.phone_text.get('1.0', tk.END).strip()
        if phones_text:
            phone_list = [line.strip() for line in phones_text.split('\n') if line.strip()]
            if phone_list:
                phone = phone_list[0]  # Use first phone for testing
                password = self.password_entry.get()
        
        # Create enhanced callback
        def enhanced_callback(message):
            self.log(message)
            self.ensure_auto_scroll()
        
        # Run discovery in background thread
        def run_discovery():
            try:
                categorized = self.browser_discovery.hybrid_discovery(
                    target_url, 
                    phone, 
                    password, 
                    enhanced_callback
                )
                
                if categorized:
                    total = sum(len(eps) for eps in categorized.values())
                    enhanced_callback(f"")
                    enhanced_callback(f"✅ AUTO-DISCOVERY SUCCESSFUL!")
                    enhanced_callback(f"📊 Total endpoints discovered: {total}")
                    enhanced_callback(f"💾 Results saved to config/discovered_endpoints.json")
                    enhanced_callback(f"")
                    enhanced_callback(f"🔄 You can now use these endpoints in your operations")
                else:
                    enhanced_callback(f"⚠️ No endpoints discovered. The site may use non-standard patterns.")
                    
            except Exception as e:
                enhanced_callback(f"❌ Discovery failed: {str(e)}")
        
        threading.Thread(target=run_discovery, daemon=True).start()

    def count_phones(self):
        """Count and display the number of phone numbers"""
        phones_text = self._get_phones_text()
        if phones_text:
            phone_list = [line.strip() for line in phones_text.split('\n') if line.strip()]
            count = len(phone_list)
            self.count_btn.config(text=f"📊 Count: {count}")
            self.log(f"📊 Total phone numbers: {count}")
        else:
            self.count_btn.config(text="📊 Count: 0")
            self.log("📊 No phone numbers found")

    def setup_keyboard_shortcuts(self):
        """Setup keyboard shortcuts for the application"""
        self.root.bind('<Control-o>', lambda e: self.upload_phones())
        self.root.bind('<Control-r>', lambda e: self.check_balance())
        self.root.bind('<Control-b>', lambda e: self.place_bets())
        self.root.bind('<Control-t>', lambda e: self.toggle_theme())

    def setup_drag_drop(self):
        """Setup drag and drop functionality (basic implementation)"""
        # Basic drag and drop would require tkinterdnd2 library
        # For now, just a placeholder
        pass

    def start_remote_server(self):
        """Start the remote control server"""
        try:
            self.remote_server = RemoteServer(self)
            self.remote_server.start()
            self.log("🔐 Remote control server started on port 8080")
        except Exception as e:
            self.log(f"❌ Failed to start remote server: {str(e)}")
            self.remote_server = None

    def toggle_persistence(self):
        # Apply persistence toggle globally
        set_persistence(self.allow_persist.get())
        state = "ENABLED" if self.allow_persist.get() else "DISABLED"
        self.log(f"🧯 Persistence {state} — {'files will be written' if self.allow_persist.get() else 'stateless: no disk writes'}")
    
    # AI Control Methods
    def toggle_ai(self):
        """Toggle AI system on/off"""
        enabled = self.ai_enabled.get()
        self.ai_integration.ai_engine.ai_enabled = enabled
        
        status = "🤖 AI Status: Active" if enabled else "🤖 AI Status: Disabled"
        color = '#4CAF50' if enabled else '#F44336'
        self.ai_status_label.config(text=status, fg=color)
        
        self.log(f"🤖 AI {'enabled' if enabled else 'disabled'}")
    
    def on_ai_mode_change(self, event=None):
        """Handle AI mode change"""
        mode = self.ai_mode.get()
        self.ai_integration.configure_ai_settings({'ai_mode': mode})
        
        # Update UI based on mode
        if mode == "full_auto":
            self.ai_status_label.config(text="🤖 AI Status: Full Automation", fg='#FF9800')
        elif mode == "assisted":
            self.ai_status_label.config(text="🤖 AI Status: Assisted Mode", fg='#2196F3')
        else:
            self.ai_status_label.config(text="🤖 AI Status: Manual Mode", fg='#9E9E9E')
    
    def on_confidence_change(self, value):
        """Handle confidence threshold change"""
        threshold = float(value)
        self.ai_integration.configure_ai_settings({'confidence_threshold': threshold})
        self.log(f"🎯 AI confidence threshold set to {threshold:.1%}")
    
    def run_ai_analysis(self):
        """Run AI analysis on current betting opportunity"""
        if not self.ai_enabled.get():
            self.log("❌ AI is disabled - enable AI first")
            return
        
        phones_text = self.phone_text.get('1.0', tk.END).strip()
        booking_code = self.booking_entry.get().strip()
        stake = self.stake_entry.get().strip()
        
        if not phones_text or not booking_code or not stake:
            self.log("❌ Please fill in phone numbers, booking code, and stake first")
            return
        
        try:
            stake_float = float(stake)
            phone_list = [line.strip() for line in phones_text.split('\n') if line.strip()]
            
            self.log(f"🧠 Running AI batch analysis for {len(phone_list)} accounts...")
            
            def run_analysis():
                results = self.ai_integration.smart_batch_analysis(
                    phone_list, booking_code, stake_float
                )
                
                # Update AI stats
                self.update_ai_stats_display()
                
                # Display batch advice
                if 'batch_advice' in results:
                    self.log("📋 AI Batch Recommendations:")
                    for advice in results['batch_advice']:
                        self.log(f"   {advice}")
            
            threading.Thread(target=run_analysis, daemon=True).start()
            
        except ValueError:
            self.log("❌ Invalid stake amount - please enter a number")
        except Exception as e:
            self.log(f"❌ AI analysis failed: {str(e)}")
    
    def show_ai_dashboard(self):
        """Show comprehensive AI dashboard"""
        dashboard_data = self.ai_integration.get_ai_dashboard_data()
        
        # Create dashboard window
        dashboard = tk.Toplevel(self.root)
        dashboard.title("🧠 AI Intelligence Dashboard")
        dashboard.geometry("800x600")
        dashboard.configure(bg=self.colors['bg'])
        
        # Create notebook for tabs - OPTIMIZED FOR SMOOTH TAB SWITCHING
        notebook = ttk.Notebook(dashboard)
        notebook.pack(fill='both', expand=True, padx=10, pady=10)
        
        # Smooth tab switching - prevent glitches when changing tabs
        def on_tab_changed(event):
            """Handle tab change smoothly without glitches"""
            try:
                # Update display immediately for smooth transition
                selected_tab = event.widget.select()
                event.widget.update_idletasks()
                # Force small delay to ensure rendering completes
                dashboard.after(10, lambda: dashboard.update_idletasks())
            except:
                pass  # Ignore errors during tab switch
        
        notebook.bind("<<NotebookTabChanged>>", on_tab_changed)
        
        # Performance Tab
        perf_frame = tk.Frame(notebook, bg=self.colors['bg'])
        notebook.add(perf_frame, text="📊 Performance")
        
        performance_text = tk.Text(perf_frame, bg=self.colors['text_bg'], fg=self.colors['text_fg'])
        performance_text.pack(fill='both', expand=True, padx=5, pady=5)
        
        # Format performance data
        perf_info = f"""🤖 AI PERFORMANCE DASHBOARD
{'='*50}

📈 SESSION STATISTICS:
Total AI Decisions: {dashboard_data['session_performance']['total_ai_decisions']}
Successful Predictions: {dashboard_data['session_performance']['successful_predictions']}
AI Accuracy: {dashboard_data['session_performance']['ai_accuracy']:.1%}
Total ROI: {dashboard_data['session_performance']['total_roi']:.2f}

🎯 AI CONFIGURATION:
Mode: {dashboard_data['ai_status']['mode'].title()}
Engine Active: {dashboard_data['ai_status']['engine_active']}
Learning Enabled: {dashboard_data['ai_status']['learning_enabled']}
Auto Improve: {dashboard_data['ai_status']['auto_improve']}
Confidence Threshold: {dashboard_data['confidence_threshold']:.1%}
Pending Decisions: {dashboard_data['pending_decisions']}

⚖️ STRATEGY WEIGHTS:
"""
        
        for strategy, weight in dashboard_data['current_strategy'].items():
            perf_info += f"{strategy.title()}: {weight:.1%}\n"
        
        perf_info += f"\n🎲 RISK SETTINGS:\nThreshold: {dashboard_data['risk_settings']['threshold'].title()}\nAuto Stake Optimization: {dashboard_data['risk_settings']['auto_stake_optimization']}\n"
        
        performance_text.insert('1.0', perf_info)
        performance_text.config(state='disabled')
        
        # Insights Tab
        insights_frame = tk.Frame(notebook, bg=self.colors['bg'])
        notebook.add(insights_frame, text="💡 Insights")
        
        insights_text = tk.Text(insights_frame, bg=self.colors['text_bg'], fg=self.colors['text_fg'])
        insights_text.pack(fill='both', expand=True, padx=5, pady=5)
        
        # Get recommendations
        recommendations = self.ai_integration.get_smart_recommendations()
        insights_info = "🧠 AI INSIGHTS & RECOMMENDATIONS\n" + "="*50 + "\n\n"
        
        if recommendations:
            insights_info += "💡 CURRENT RECOMMENDATIONS:\n"
            for i, rec in enumerate(recommendations, 1):
                insights_info += f"{i}. {rec}\n"
        else:
            insights_info += "✅ No specific recommendations at this time.\n"
        
        # Add AI insights
        ai_insights = dashboard_data['ai_insights']
        insights_info += f"\n📊 AI LEARNING PROGRESS:\n"
        insights_info += f"Total Learning Examples: {ai_insights['total_decisions']}\n"
        insights_info += f"Overall Success Rate: {ai_insights['success_rate']:.1%}\n"
        insights_info += f"Average ROI: {ai_insights['average_roi']:.2f}\n"
        
        insights_text.insert('1.0', insights_info)
        insights_text.config(state='disabled')
        
        self.log("📊 AI Dashboard opened")
    
    def ai_optimize_stakes(self):
        """Use AI to optimize stakes for current operation"""
        if not self.ai_enabled.get():
            self.log("❌ AI is disabled - enable AI first")
            return
        
        phones_text = self.phone_text.get('1.0', tk.END).strip()
        booking_code = self.booking_entry.get().strip()
        stake = self.stake_entry.get().strip()
        
        if not phones_text or not booking_code or not stake:
            self.log("❌ Please fill in phone numbers, booking code, and stake first")
            return
        
        try:
            stake_float = float(stake)
            phone_list = [line.strip() for line in phones_text.split('\n') if line.strip()]
            
            self.log(f"⚙️ AI optimizing stakes for {len(phone_list)} accounts...")
            
            def optimize():
                optimized_stakes = self.ai_integration.auto_optimize_stakes(
                    phone_list, booking_code, stake_float
                )
                
                # Display optimization results
                self.log("💰 Stake Optimization Results:")
                for phone, optimized_stake in list(optimized_stakes.items())[:5]:  # Show first 5
                    self.log(f"   {phone[-4:]}: {stake_float:.2f} → {optimized_stake:.2f}")
                
                if len(optimized_stakes) > 5:
                    self.log(f"   ... and {len(optimized_stakes) - 5} more accounts")
                
                self.update_ai_stats_display()
            
            threading.Thread(target=optimize, daemon=True).start()
            
        except ValueError:
            self.log("❌ Invalid stake amount - please enter a number")
        except Exception as e:
            self.log(f"❌ Stake optimization failed: {str(e)}")
    
    def reset_ai_learning(self):
        """Reset AI learning data"""
        if messagebox.askyesno("Reset AI Learning", 
                              "Are you sure you want to reset all AI learning data?\n\n"
                              "This will clear all accumulated knowledge and start fresh."):
            self.ai_integration.reset_ai_learning()
            self.update_ai_stats_display()
            self.log("🔄 AI learning data has been reset")
    
    def update_ai_stats_display(self):
        """Update AI statistics display"""
        dashboard_data = self.ai_integration.get_ai_dashboard_data()
        stats = dashboard_data['session_performance']
        
        accuracy_text = f"{stats['ai_accuracy']:.1%}" if stats['total_ai_decisions'] > 0 else "N/A"
        stats_text = f"Decisions: {stats['total_ai_decisions']} | Accuracy: {accuracy_text} | ROI: {stats['total_roi']:.2f}"
        
        self.ai_stats_label.config(text=stats_text)
    
    def update_live_clock(self):
        """
        Update live clock with Kenya time (EAT = UTC+3)
        Shows system is alive and helps with match timing
        """
        try:
            import pytz
            from datetime import datetime
            
            # Get Kenya time (EAT = UTC+3)
            kenya_tz = pytz.timezone('Africa/Nairobi')
            now = datetime.now(kenya_tz)
            
            # Format time nicely
            time_str = now.strftime("%H:%M:%S")
            date_str = now.strftime("%a, %d %b")
            
            # Update clock label
            clock_text = f"🕐 {time_str}\n{date_str}"
            self.clock_label.config(text=clock_text)
            
        except Exception as e:
            # Fallback to system time if pytz fails
            from datetime import datetime
            now = datetime.now()
            time_str = now.strftime("%H:%M:%S")
            date_str = now.strftime("%a, %d %b")
            clock_text = f"🕐 {time_str}\n{date_str}"
            self.clock_label.config(text=clock_text)
        
        # Update every 1 second (keeps UI alive and responsive)
        if hasattr(self, 'root') and self.root.winfo_exists():
            self.root.after(1000, self.update_live_clock)

if __name__ == "__main__":
    # 🔧 ROBUST SPLASH SCREEN: Always works, with graceful fallback
    splash = None
    root = None
    
    try:
        # Step 1: Import splash screen module (with fallback)
        try:
            from splash_screen import SplashScreen
            splash_available = True
        except ImportError as import_err:
            print(f"⚠️ Splash screen module not available: {import_err}")
            splash_available = False
        except Exception as import_err:
            print(f"⚠️ Splash screen import error: {import_err}")
            splash_available = False
        
        # Step 2: Create main root window first (always needed)
        root = tk.Tk()
        root.withdraw()
        
        # Step 3: Try to show splash screen (with fallback)
        if splash_available:
            try:
                splash = SplashScreen(parent=root)
                splash_shown = True
                # CRITICAL: Force splash screen to be visible immediately
                root.update_idletasks()
                root.update()
                # Small delay to ensure splash screen is fully rendered
                time.sleep(0.1)
            except Exception as splash_err:
                print(f"⚠️ Splash screen initialization failed: {splash_err}")
                print("   Starting without splash screen...")
                splash_shown = False
                splash = None
        else:
            splash_shown = False
        
        # Store splash screen reference for GUI initialization
        global splash_ref
        splash_ref = splash if splash_shown else None
        
        def initialize_app():
            """Initialize application in background with real progress tracking"""
            try:
                def update_splash(progress, status):
                    """Helper to update splash screen safely"""
                    if splash_ref and splash_shown:
                        try:
                            # Schedule update on main thread
                            root.after(0, lambda: splash_ref.update_progress(progress, status) if splash_ref else None)
                            root.update_idletasks()  # Process the update immediately
                        except:
                            pass
                
                # Initialize GUI - this does the actual heavy work
                # Pass splash screen reference so GUI can update progress during initialization
                app = BetFlowProGUI(root, splash_ref if splash_shown else None)
                
                # Complete splash with final message
                update_splash(100, "✅ Ready! Starting Sportsape BitBot Balance Checker...")
                time.sleep(0.3)
                
                # Force immediate rendering of all GUI elements
                root.update_idletasks()
                root.update()
                
                # Close splash and show main window (with error handling)
                if splash and splash_shown:
                    try:
                        splash.close()
                    except:
                        pass  # Continue even if splash close fails
                
                # CRITICAL: Ensure window is visible
                root.deiconify()
                root.update_idletasks()
                root.update()
                root.lift()
                root.focus_force()
                
                # Additional updates to ensure visibility on Windows
                root.after(50, lambda: root.lift() if root else None)
                root.after(100, lambda: root.focus_force() if root else None)
                
            except Exception as init_err:
                # If initialization fails, ensure main window is shown anyway
                print(f"⚠️ Initialization error: {init_err}")
                import traceback
                traceback.print_exc()
                try:
                    if splash and splash_shown:
                        splash.close()
                except:
                    pass
                try:
                    root.deiconify()
                    root.update_idletasks()
                    root.update()
                    root.lift()
                    root.focus_force()
                except:
                    pass
        
        # Start initialization in background thread after a brief delay
        # This ensures splash screen is fully visible first
        import threading
        def start_init():
            time.sleep(0.2)  # Brief delay to ensure splash screen is visible
            init_thread = threading.Thread(target=initialize_app, daemon=True)
            init_thread.start()
        
        threading.Thread(target=start_init, daemon=True).start()
        
        # Run main event loop - this must run to process splash screen updates
        root.mainloop()
        
    except Exception as e:
        # CRITICAL FALLBACK: If everything fails, start normally
        print(f"⚠️ Critical error during startup: {e}")
        print("   Starting without splash screen...")
        try:
            # Ensure splash is closed if it exists
            if splash:
                try:
                    splash.close()
                except:
                    pass
        except:
            pass
        
        # Start normally
        if root is None:
            root = tk.Tk()
        try:
            app = BetFlowProGUI(root)
            root.mainloop()
        except Exception as final_err:
            print(f"❌ Fatal error: {final_err}")
            import traceback
            traceback.print_exc()
