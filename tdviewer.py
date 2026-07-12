#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""tdviewer - minimal single-instance-per-display image viewer.

Designed for closed-network Linux hosts where only stock GNOME libraries
(GTK3, GdkPixbuf, PyGObject) are available.

Behaviour:
  * One viewer window per DISPLAY.  The first invocation opens the window;
    later invocations on the same DISPLAY hand the image path to the running
    window over a unix socket and exit immediately.
  * Different DISPLAY values get independent windows, so many user displays
    can be served at the same time.

Usage:
  DISPLAY=:1 tdviewer.py /path/to/image.jpg
"""

import errno
import os
import signal
import socket
import sys
import tempfile
import time

APP = "tdviewer"

# GTK modules are imported lazily (only when this process becomes the window
# owner) so the frequent "forward and exit" path stays fast.
Gtk = Gdk = GdkPixbuf = GLib = None


# ---------------------------------------------------------------------------
# single-instance plumbing
# ---------------------------------------------------------------------------

def normalize_display(display):
    """':1.0' and ':1' are the same X display; drop the screen suffix."""
    display = display.strip()
    host, _, num = display.rpartition(":")
    if "." in num:
        num = num.split(".", 1)[0]
    return "%s:%s" % (host, num)


def socket_address(display):
    key = "%s-%d-%s" % (APP, os.getuid(), normalize_display(display))
    if sys.platform.startswith("linux"):
        # Abstract namespace: no socket file on disk, vanishes with the
        # process, so stale sockets are impossible.
        return "\0" + key
    base = os.environ.get("XDG_RUNTIME_DIR") or tempfile.gettempdir()
    return os.path.join(base, key.replace("/", "_") + ".sock")


def try_forward(addr, path):
    """Hand the image to a running instance.

    Returns an exit code if an instance handled (or failed to handle) the
    request, or None when no instance is listening.
    """
    sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    sock.settimeout(5.0)
    try:
        sock.connect(addr)
    except OSError:
        sock.close()
        return None
    try:
        sock.sendall(path.encode("utf-8") + b"\n")
        reply = b""
        while b"\n" not in reply and len(reply) < 65536:
            chunk = sock.recv(4096)
            if not chunk:
                break
            reply += chunk
    except OSError:
        sys.stderr.write("%s: existing instance did not respond\n" % APP)
        return 1
    finally:
        sock.close()
    text = reply.decode("utf-8", "replace").strip()
    if text.startswith("OK"):
        return 0
    sys.stderr.write("%s\n" % (text or "%s: empty reply from existing instance" % APP))
    return 1


def try_bind(addr):
    """Become the instance owner.  Returns a listening socket or None if
    another process owns (or just grabbed) the address."""
    for _ in range(2):
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        try:
            sock.bind(addr)
            sock.listen(8)
            return sock
        except OSError as exc:
            sock.close()
            if exc.errno != errno.EADDRINUSE:
                raise
            if addr.startswith("\0"):
                return None
            # Filesystem socket: unlink only if nothing is listening there,
            # otherwise we would steal a live instance's socket.
            probe = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            probe.settimeout(1.0)
            try:
                probe.connect(addr)
            except OSError:
                pass  # dead leftover; safe to remove
            else:
                return None
            finally:
                probe.close()
            try:
                os.unlink(addr)
            except OSError:
                return None
    return None


# ---------------------------------------------------------------------------
# viewer window (GTK)
# ---------------------------------------------------------------------------

def import_gtk():
    global Gtk, Gdk, GdkPixbuf, GLib
    try:
        import gi
        gi.require_version("Gtk", "3.0")
        gi.require_version("GdkPixbuf", "2.0")
        from gi.repository import Gtk as _Gtk, Gdk as _Gdk, \
            GdkPixbuf as _GdkPixbuf, GLib as _GLib
    except (ImportError, ValueError) as exc:
        sys.stderr.write(
            "%s: PyGObject/GTK3 is required to open a window (%s)\n"
            "  verify with: python3 -c 'import gi; gi.require_version(\"Gtk\", \"3.0\")'\n"
            % (APP, exc))
        sys.exit(3)
    Gtk, Gdk, GdkPixbuf, GLib = _Gtk, _Gdk, _GdkPixbuf, _GLib


def workarea_size():
    try:
        display = Gdk.Display.get_default()
        monitor = display.get_primary_monitor() or display.get_monitor(0)
        area = monitor.get_workarea()
        return area.width, area.height
    except AttributeError:  # GTK < 3.22
        screen = Gdk.Screen.get_default()
        return screen.get_width(), screen.get_height()


class Viewer(object):
    ZOOM_STEP = 1.25
    ZOOM_MIN = 0.05
    ZOOM_MAX = 2.0

    def __init__(self, server_sock, first_path):
        self.server_sock = server_sock
        self.path = None
        self.pixbuf = None          # static image (already orientation-fixed)
        self.animation = None       # animated image (shown unscaled)
        self.fit_mode = True
        self.zoom = 1.0
        self.scale_shown = 1.0
        self.rendered_size = None

        self.window = Gtk.Window(title=APP)
        self.window.connect("destroy", lambda *a: Gtk.main_quit())
        self.window.connect("key-press-event", self.on_key)
        self.window.connect("focus-in-event", self.on_focus_in)

        self.image = Gtk.Image()
        self.scroll = Gtk.ScrolledWindow()
        self.scroll.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        self.scroll.add(self.image)
        self.scroll.add_events(Gdk.EventMask.SCROLL_MASK |
                               Gdk.EventMask.SMOOTH_SCROLL_MASK |
                               Gdk.EventMask.BUTTON_PRESS_MASK |
                               Gdk.EventMask.BUTTON_RELEASE_MASK |
                               Gdk.EventMask.BUTTON1_MOTION_MASK)
        self.scroll.connect("scroll-event", self.on_scroll)
        self.scroll.connect("button-press-event", self.on_button_press)
        self.scroll.connect("motion-notify-event", self.on_motion)
        self.scroll.connect("button-release-event", self.on_button_release)
        self.scroll.connect("size-allocate", self.on_size_allocate)
        self.drag_origin = None
        self.rescale_pending = None
        self.window.add(self.scroll)

        error = self.load(first_path)
        if error != "OK":
            sys.stderr.write("%s\n" % error)
            sys.exit(1)

        self.set_initial_size()
        self.window.show_all()

        GLib.io_add_watch(server_sock.fileno(), GLib.IO_IN, self.on_incoming)
        for signum in (signal.SIGINT, signal.SIGTERM):
            try:
                GLib.unix_signal_add(GLib.PRIORITY_DEFAULT, signum,
                                     lambda *a: (Gtk.main_quit(), False)[1])
            except AttributeError:
                pass

    # -- image loading -----------------------------------------------------

    def load(self, path):
        if not os.path.isfile(path):
            return "ERR no such file: %s" % path
        info = GdkPixbuf.Pixbuf.get_file_info(path)
        fmt = info[0] if isinstance(info, tuple) else info
        if fmt is None:
            return "ERR unsupported image format: %s" % path
        try:
            if fmt.get_name() == "gif":
                anim = GdkPixbuf.PixbufAnimation.new_from_file(path)
                self.animation, self.pixbuf = anim, None
            else:
                pixbuf = GdkPixbuf.Pixbuf.new_from_file(path)
                pixbuf = pixbuf.apply_embedded_orientation() or pixbuf
                self.animation, self.pixbuf = None, pixbuf
        except GLib.Error as exc:
            return "ERR %s: %s" % (path, exc.message)

        self.path = path
        self.fit_mode = True
        self.zoom = 1.0
        self.rendered_size = None
        if self.pixbuf is not None:
            self.rescale()
        else:
            self.image.set_from_animation(self.animation)
            self.scale_shown = 1.0
            self.update_title()
        return "OK"

    def image_size(self):
        if self.pixbuf is not None:
            return self.pixbuf.get_width(), self.pixbuf.get_height()
        return self.animation.get_width(), self.animation.get_height()

    def set_initial_size(self):
        max_w, max_h = [int(v * 0.9) for v in workarea_size()]
        img_w, img_h = self.image_size()
        self.window.set_default_size(max(min(img_w + 4, max_w), 320),
                                     max(min(img_h + 4, max_h), 240))

    # -- scaling -----------------------------------------------------------

    def rescale(self, alloc=None):
        if self.pixbuf is None:
            return
        img_w, img_h = self.pixbuf.get_width(), self.pixbuf.get_height()
        if self.fit_mode:
            if alloc is None:
                alloc = self.scroll.get_allocation()
            if alloc.width < 2 or alloc.height < 2:
                scale = 1.0  # not realized yet; size-allocate will re-fit
            else:
                scale = min((alloc.width - 2.0) / img_w,
                            (alloc.height - 2.0) / img_h, 1.0)
        else:
            scale = self.zoom
        width = max(1, int(round(img_w * scale)))
        height = max(1, int(round(img_h * scale)))
        if (width, height) == self.rendered_size:
            return
        self.rendered_size = (width, height)
        self.scale_shown = scale
        if (width, height) == (img_w, img_h):
            self.image.set_from_pixbuf(self.pixbuf)
        else:
            self.image.set_from_pixbuf(self.pixbuf.scale_simple(
                width, height, GdkPixbuf.InterpType.BILINEAR))
        self.update_title()

    def current_scale(self):
        """Zoom target, including one not rendered yet."""
        return self.scale_shown if self.fit_mode else self.zoom

    def set_zoom(self, value):
        if self.pixbuf is None:
            return
        self.fit_mode = False
        self.zoom = max(self.ZOOM_MIN, min(value, self.ZOOM_MAX))
        # Rescaling a large pixbuf is expensive; render once the burst of
        # zoom events (fast wheel spins) has been consumed instead of once
        # per event.
        if self.rescale_pending is None:
            self.rescale_pending = GLib.idle_add(self.on_rescale_idle)

    def on_rescale_idle(self):
        self.rescale_pending = None
        self.rescale()
        return False

    def update_title(self):
        name = os.path.basename(self.path or "")
        img_w, img_h = self.image_size()
        if self.animation is not None:
            detail = "%dx%d animation" % (img_w, img_h)
        else:
            detail = "%dx%d  %d%%" % (img_w, img_h, round(self.scale_shown * 100))
        self.window.set_title("%s  (%s) - %s" % (name, detail, APP))

    # -- events ------------------------------------------------------------

    def on_size_allocate(self, widget, allocation):
        if self.fit_mode:
            self.rescale(allocation)

    def on_key(self, widget, event):
        key = Gdk.keyval_name(event.keyval)
        if key in ("q", "Q", "Escape"):
            Gtk.main_quit()
        elif key in ("plus", "equal", "KP_Add"):
            self.set_zoom(self.current_scale() * self.ZOOM_STEP)
        elif key in ("minus", "KP_Subtract"):
            self.set_zoom(self.current_scale() / self.ZOOM_STEP)
        elif key in ("1", "KP_1"):
            self.set_zoom(1.0)
        elif key in ("f", "0", "KP_0"):
            self.fit_mode = True
            self.rescale()
        elif key == "F11":
            state = self.window.get_window().get_state() if self.window.get_window() else 0
            if state & Gdk.WindowState.FULLSCREEN:
                self.window.unfullscreen()
            else:
                self.window.fullscreen()
        else:
            return False
        return True

    def on_scroll(self, widget, event):
        if not event.state & Gdk.ModifierType.CONTROL_MASK:
            return False  # plain wheel keeps panning the scrolled window
        direction = 0
        if event.direction == Gdk.ScrollDirection.UP:
            direction = 1
        elif event.direction == Gdk.ScrollDirection.DOWN:
            direction = -1
        elif event.direction == Gdk.ScrollDirection.SMOOTH:
            ok, _dx, dy = event.get_scroll_deltas()
            if ok and dy:
                direction = 1 if dy < 0 else -1
        if direction > 0:
            self.set_zoom(self.current_scale() * self.ZOOM_STEP)
        elif direction < 0:
            self.set_zoom(self.current_scale() / self.ZOOM_STEP)
        return True

    def on_button_press(self, widget, event):
        if event.button != 1 or event.type != Gdk.EventType.BUTTON_PRESS:
            return False
        # Root coordinates stay stable while the adjustments move underneath.
        self.drag_origin = (event.x_root, event.y_root,
                            self.scroll.get_hadjustment().get_value(),
                            self.scroll.get_vadjustment().get_value())
        self.set_drag_cursor(True)
        return True

    def on_motion(self, widget, event):
        if self.drag_origin is None:
            return False
        x0, y0, h0, v0 = self.drag_origin
        self.scroll.get_hadjustment().set_value(h0 - (event.x_root - x0))
        self.scroll.get_vadjustment().set_value(v0 - (event.y_root - y0))
        return True

    def on_button_release(self, widget, event):
        if event.button != 1 or self.drag_origin is None:
            return False
        self.drag_origin = None
        self.set_drag_cursor(False)
        return True

    def set_drag_cursor(self, active):
        win = self.scroll.get_window()
        if win is None:
            return
        cursor = None
        if active:
            display = win.get_display()
            cursor = Gdk.Cursor.new_from_name(display, "grabbing") or \
                Gdk.Cursor.new_for_display(display, Gdk.CursorType.FLEUR)
        win.set_cursor(cursor)

    def on_focus_in(self, widget, event):
        self.window.set_urgency_hint(False)
        return False

    def present(self):
        self.window.show_all()
        self.window.deiconify()
        self.window.present_with_time(Gtk.get_current_event_time() or
                                      Gdk.CURRENT_TIME)
        # If the window manager blocks focus stealing, at least flash the
        # taskbar entry.
        self.window.set_urgency_hint(True)

    # -- incoming requests from later invocations ---------------------------

    def on_incoming(self, source, condition):
        try:
            conn, _ = self.server_sock.accept()
        except OSError:
            return True
        conn.settimeout(2.0)
        try:
            data = b""
            while b"\n" not in data and len(data) < 65536:
                chunk = conn.recv(4096)
                if not chunk:
                    break
                data += chunk
            path = data.decode("utf-8", "replace").strip()
            reply = self.load(path) if path else "ERR empty request"
            try:
                conn.sendall(reply.encode("utf-8") + b"\n")
            except OSError:
                pass
            if reply == "OK":
                self.present()
        finally:
            conn.close()
        return True


# ---------------------------------------------------------------------------
# entry point
# ---------------------------------------------------------------------------

def usage(stream):
    stream.write(
        "usage: %s IMAGE_FILE\n"
        "\n"
        "Opens IMAGE_FILE in a viewer window on $DISPLAY.  If a viewer is\n"
        "already running on that display, the image replaces the one in the\n"
        "existing window and this process exits immediately.\n"
        "\n"
        "keys: +/- zoom, 1 actual size, f/0 fit to window, F11 fullscreen,\n"
        "      Ctrl+wheel zoom, drag to pan, q/Esc quit\n" % APP)


def main(argv):
    if len(argv) != 2 or argv[1] in ("-h", "--help"):
        usage(sys.stderr if len(argv) != 2 else sys.stdout)
        return 0 if len(argv) == 2 else 2

    path = os.path.abspath(argv[1])
    if not os.path.isfile(path):
        sys.stderr.write("%s: no such file: %s\n" % (APP, path))
        return 1

    display = os.environ.get("DISPLAY")
    if not display:
        sys.stderr.write("%s: DISPLAY is not set\n" % APP)
        return 1

    addr = socket_address(display)
    server = None
    for _ in range(5):
        code = try_forward(addr, path)
        if code is not None:
            return code
        server = try_bind(addr)
        if server is not None:
            break
        time.sleep(0.2)
    if server is None:
        sys.stderr.write("%s: could not create or reach the instance socket\n" % APP)
        return 1

    if not addr.startswith("\0"):
        import atexit
        atexit.register(lambda: os.path.exists(addr) and os.unlink(addr))

    import_gtk()
    Viewer(server, path)
    Gtk.main()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
