import sys
import os
import inspect
import logging
import tokenize
from io import BytesIO
import keyword
import builtins
from functools import wraps

SINKS = ["exec", "eval", "execfile", "compile", "open", "input", "print"]  # list is updated though

PROJECT_ROOT = os.path.abspath(os.getcwd())

# Global state populated at runtime
_ACTIVE_SINK_LINES = {}  # filename -> {line_no: [sink_names]}
_TARGET_FILE = None

# --- Simple taint machinery ---------------------------------------------------

class Tainted:
    """
    Lightweight taint wrapper that tries to preserve taint across common operations.
    """
    __slots__ = ("value", "label")

    def __init__(self, value, label="user_input"):
        self.value = value
        self.label = label

    def __str__(self):
        return str(self.value)

    def __repr__(self):
        return f"Tainted({self.value!r}, label={self.label!r})"

    def __bytes__(self):
        return bytes(self.value)

    def __format__(self, spec):
        return format(self.value, spec)

    def __int__(self):
        return int(self.value)

    def __float__(self):
        return float(self.value)

    def __bool__(self):
        return bool(self.value)

    def __eq__(self, other):
        if isinstance(other, Tainted):
            return self.value == other.value
        return self.value == other

    def __lt__(self, other):
        return self.value < (other.value if isinstance(other, Tainted) else other)

    def __le__(self, other):
        return self.value <= (other.value if isinstance(other, Tainted) else other)

    def __gt__(self, other):
        return self.value > (other.value if isinstance(other, Tainted) else other)

    def __ge__(self, other):
        return self.value >= (other.value if isinstance(other, Tainted) else other)

    def _combine(self, other, op):
        if isinstance(other, Tainted):
            new_val = op(self.value, other.value)
            new_label = f"{self.label}|{other.label}"
            return Tainted(new_val, new_label)
        else:
            new_val = op(self.value, other)
            return Tainted(new_val, self.label)

    def __add__(self, other):
        return self._combine(other, lambda a, b: a + b)

    def __radd__(self, other):
        if isinstance(other, Tainted):
            return other.__add__(self)
        return Tainted(other + self.value, self.label)

    def __mul__(self, other):
        return self._combine(other, lambda a, b: a * b)

    def __rmul__(self, other):
        if isinstance(other, Tainted):
            return other.__mul__(self)
        return Tainted(other * self.value, self.label)

    def __getitem__(self, key):
        return Tainted(self.value[key], self.label)

    def __getattr__(self, name):
        attr = getattr(self.value, name)
        if callable(attr):
            from functools import wraps
            @wraps(attr)
            def wrapper(*args, **kwargs):
                res = attr(*_unwrap_all(args), **_unwrap_all(kwargs))
                if isinstance(res, (str, bytes, bytearray, int, float, bool)) or res is None:
                    return Tainted(res, self.label)
                return res
            return wrapper
        return attr


def taint(value, label="user_input"):
    if isinstance(value, Tainted):
        # Already tainted; optionally refine the label
        return Tainted(value.value, f"{value.label}|{label}")
    # For simple containers, taint elements too (shallow)
    if isinstance(value, list):
        return [taint(v, label) for v in value]
    if isinstance(value, tuple):
        return tuple(taint(v, label) for v in value)
    if isinstance(value, dict):
        return {k: taint(v, label) for k, v in value.items()}
    return Tainted(value, label)

def is_tainted(obj):
    if isinstance(obj, Tainted):
        return True
    # Shallow container check
    if isinstance(obj, (list, tuple, set)):
        return any(is_tainted(x) for x in obj)
    if isinstance(obj, dict):
        return any(is_tainted(v) for v in obj.values())
    return False

def get_taint_label(obj):
    if isinstance(obj, Tainted):
        return obj.label
    if isinstance(obj, (list, tuple, set)):
        labels = [get_taint_label(x) for x in obj if is_tainted(x)]
        return "|".join(l for l in labels if l)
    if isinstance(obj, dict):
        labels = [get_taint_label(v) for v in obj.values() if is_tainted(v)]
        return "|".join(l for l in labels if l)
    return None

def _unwrap(x):
    return x.value if isinstance(x, Tainted) else x

def _unwrap_all(obj):
    if isinstance(obj, dict):
        return {k: _unwrap(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple, set)):
        typ = type(obj)
        return typ(_unwrap(v) for v in obj)
    return _unwrap(obj)

# --- Token/line-based sink finding (your original) ----------------------------

def find_sink(filename):
    found_sink = {}
    with open(filename, 'rb') as f:  # read in binary mode for tokenize
        tokens = tokenize.tokenize(f.readline)
        prev = None
        for tok in tokens:
            if tok.type == tokenize.NAME and tok.string in SINKS:
                # naive: treat any NAME followed by '(' as a call site
                prev = tok
                continue
            if prev and tok.string == '(':
                sink_name = prev.string
                line_no = prev.start[0]
                found_sink.setdefault(sink_name, []).append(line_no)
            prev = None
    return found_sink

def _build_sink_line_index(filename, sinks_dict):
    # Invert to line -> [sinks]
    line_map = {}
    for name, lines in sinks_dict.items():
        for ln in lines:
            line_map.setdefault(ln, []).append(name)
    return {os.path.abspath(filename): line_map}

# --- Tracing (augmented) ------------------------------------------------------

def _log_taint_alert(sink_name, args, kwargs):
    if any(is_tainted(a) for a in args) or any(is_tainted(v) for v in kwargs.values()):
        labels = []
        for a in args:
            if is_tainted(a):
                labels.append(get_taint_label(a) or "unknown")
        for v in kwargs.values():
            if is_tainted(v):
                labels.append(get_taint_label(v) or "unknown")
        label_str = "|".join(sorted(set(l for l in labels if l)))
        logging.warning(f"[TAINT ALERT] Sink `{sink_name}` received tainted data (labels: {label_str})")

# Keep a minimal id->label map for non-wrapper flows (e.g., raw input return)
taint_map = {}

def trace_calls(frame, event, arg):
    fn = os.path.abspath(frame.f_code.co_filename)

    # --- Detect a source call (input) ---
    if event == "call" and frame.f_code.co_name == "input":
        frame.f_locals["_is_source"] = True
        return trace_calls

    # --- Capture return value from source ---
    if event == "return" and frame.f_locals.get("_is_source"):
        val = arg  # arg is the return value from input()
        # Note: the wrapped input() replaces this path; keep for completeness.
        taint_map[id(val)] = "user_input"
        return trace_calls

    # --- Detect sink execution by line (best-effort)
    if event == 'line':
        line_no = frame.f_lineno
        sinks_here = _ACTIVE_SINK_LINES.get(fn, {}).get(line_no)
        if sinks_here:
            # If any local is tainted (by id) warn
            for name, val in frame.f_locals.items():
                if id(val) in taint_map or is_tainted(val):
                    labels = []
                    if id(val) in taint_map:
                        labels.append(taint_map[id(val)])
                    if is_tainted(val):
                        labels.append(get_taint_label(val) or "unknown")
                    label_str = "|".join(sorted(set(l for l in labels if l)))
                    logging.warning(f"[TAINT ALERT] Sink {sinks_here} got tainted data from {label_str}")
    return trace_calls

# --- Sink wrappers ------------------------------------------------------------

_original_builtins = {}

def _wrap_sink(name, func):
    @wraps(func)
    def wrapped(*args, **kwargs):
        _log_taint_alert(name, args, kwargs)

        # Special case for eval/exec: if globals/locals not passed, preserve them
        if name in ("eval", "exec"):
            if len(args) == 1:  # only code string/object provided
                frame = inspect.currentframe().f_back
                args = (args[0], frame.f_globals, frame.f_locals)

        return func(*_unwrap_all(args), **_unwrap_all(kwargs))
    return wrapped


def _install_sink_wrappers():
    to_wrap = {
        "exec": builtins.exec,
        "eval": builtins.eval,
        "compile": builtins.compile,
        "open": builtins.open,
        "print": builtins.print,
    }
    for name, fn in to_wrap.items():
        _original_builtins[name] = fn
        setattr(builtins, name, _wrap_sink(name, fn))

def _restore_sink_wrappers():
    for name, fn in _original_builtins.items():
        setattr(builtins, name, fn)
    _original_builtins.clear()

# --- Source wrapper (input) ---------------------------------------------------

def _input_wrapper(prompt=None):
    # Use the original input if already replaced externally
    orig_input = _original_builtins.get("input", builtins.input)
    if prompt is not None:
        val = orig_input(prompt)
    else:
        val = orig_input()
    t = taint(val, "user_input")
    # Also backstop the id-based map
    taint_map[id(val)] = "user_input"
    taint_map[id(t)] = "user_input"
    return t

def _install_input_wrapper():
    # save original, then wrap
    if "input" not in _original_builtins:
        _original_builtins["input"] = builtins.input
    builtins.input = _input_wrapper

# --- Public API ---------------------------------------------------------------

def install():
    logging.basicConfig(level=logging.INFO, format='[IAST_AGENT] %(asctime)s %(levelname)s: %(message)s')
    sys.settrace(None)
    import atexit
    atexit.register(_restore_sink_wrappers)
    def start_tracing():
        sys.settrace(trace_calls)
    _install_sink_wrappers()
    _install_input_wrapper()
    import threading
    threading.Timer(0.01, start_tracing).start()  # Give imports time to finish

# --- CLI entrypoint -----------------------------------------------------------

if __name__ == "__main__":
    import runpy
    if len(sys.argv) < 2:
        print("Usage: python -m iast_agent <your_script.py> [args...]")
        sys.exit(1)

    target_script = sys.argv[1]
    sys.argv = sys.argv[1:]

    logging.basicConfig(level=logging.INFO, format='[IAST_AGENT] %(asctime)s %(levelname)s: %(message)s')

    sinks = find_sink(target_script)
    # Log all found sinks and their line numbers
    msg = [f"[IAST_AGENT] Sinks found in {target_script}:"]
    for sink_name, lines in sinks.items():
        msg.append(f"  {sink_name}: lines {lines}")
        logging.info("  %s: lines %s", sink_name, lines)
    print("\n".join(msg))
    # Prepare sink line index
    _TARGET_FILE = os.path.abspath(target_script)
    _ACTIVE_SINK_LINES = _build_sink_line_index(target_script, sinks)

    # Install wrappers + tracing for the target run
    _install_sink_wrappers()
    _install_input_wrapper()
    sys.settrace(trace_calls)

    runpy.run_path(target_script, run_name="__main__")
