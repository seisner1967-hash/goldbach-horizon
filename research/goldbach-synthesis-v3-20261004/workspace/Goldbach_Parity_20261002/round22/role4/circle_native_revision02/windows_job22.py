"""SOURCE ONLY: Windows x64 parent backend; never imported or exercised.

Creates a child suspended, configures a non-breakaway one-process Job, commit
and working-set quotas, then resumes. Failure at any setup call terminates the
still-suspended child. This source is not a measured OS enforcement result.
"""
import ctypes as C
from ctypes import wintypes as W
import os
from pathlib import Path
import threading
import time

SIZE = C.c_size_t
HANDLE = W.HANDLE
U64 = C.c_ulonglong


class IO(C.Structure):
    _fields_ = [(n, U64) for n in ("ReadOperationCount", "WriteOperationCount",
        "OtherOperationCount", "ReadTransferCount", "WriteTransferCount", "OtherTransferCount")]


class Basic(C.Structure):
    _fields_ = [("PerProcessUserTimeLimit", C.c_longlong),
        ("PerJobUserTimeLimit", C.c_longlong), ("LimitFlags", W.DWORD),
        ("MinimumWorkingSetSize", SIZE), ("MaximumWorkingSetSize", SIZE),
        ("ActiveProcessLimit", W.DWORD), ("Affinity", SIZE),
        ("PriorityClass", W.DWORD), ("SchedulingClass", W.DWORD)]


class Extended(C.Structure):
    _fields_ = [("BasicLimitInformation", Basic), ("IoInfo", IO),
        ("ProcessMemoryLimit", SIZE), ("JobMemoryLimit", SIZE),
        ("PeakProcessMemoryUsed", SIZE), ("PeakJobMemoryUsed", SIZE)]


class Startup(C.Structure):
    _fields_ = [("cb", W.DWORD), ("lpReserved", W.LPWSTR),
        ("lpDesktop", W.LPWSTR), ("lpTitle", W.LPWSTR)] + [
        (n, W.DWORD) for n in ("dwX", "dwY", "dwXSize", "dwYSize",
        "dwXCountChars", "dwYCountChars", "dwFillAttribute", "dwFlags")] + [
        ("wShowWindow", W.WORD), ("cbReserved2", W.WORD),
        ("lpReserved2", C.POINTER(W.BYTE)), ("hStdInput", HANDLE),
        ("hStdOutput", HANDLE), ("hStdError", HANDLE)]


class Process(C.Structure):
    _fields_ = [("hProcess", HANDLE), ("hThread", HANDLE),
        ("dwProcessId", W.DWORD), ("dwThreadId", W.DWORD)]


class StartupEx(C.Structure):
    _fields_ = [("StartupInfo", Startup), ("lpAttributeList", C.c_void_p)]


class Memory(C.Structure):
    _fields_ = [("cb", W.DWORD), ("PageFaultCount", W.DWORD)] + [
        (n, SIZE) for n in ("PeakWorkingSetSize", "WorkingSetSize",
        "QuotaPeakPagedPoolUsage", "QuotaPagedPoolUsage",
        "QuotaPeakNonPagedPoolUsage", "QuotaNonPagedPoolUsage",
        "PagefileUsage", "PeakPagefileUsage", "PrivateUsage")]


def api():
    if os.name != "nt" or C.sizeof(C.c_void_p) != 8:
        raise RuntimeError("WINDOWS_X64_REQUIRED")
    if tuple(map(C.sizeof, (Basic, Extended, Startup, Process, Memory, StartupEx))) != (64, 144, 104, 24, 80, 112):
        raise RuntimeError("WINDOWS_ABI_SIZE_MISMATCH")
    k = C.WinDLL(r"C:\Windows\System32\kernel32.dll", use_last_error=True)
    signatures = {
        "CreateJobObjectW": (HANDLE, [C.c_void_p, W.LPCWSTR]),
        "SetInformationJobObject": (W.BOOL, [HANDLE, C.c_int, C.c_void_p, W.DWORD]),
        "QueryInformationJobObject": (W.BOOL, [HANDLE, C.c_int, C.c_void_p, W.DWORD, C.c_void_p]),
        "AssignProcessToJobObject": (W.BOOL, [HANDLE, HANDLE]),
        "TerminateJobObject": (W.BOOL, [HANDLE, W.UINT]),
        "CreateProcessW": (W.BOOL, [W.LPCWSTR, W.LPWSTR, C.c_void_p,
            C.c_void_p, W.BOOL, W.DWORD, C.c_void_p, W.LPCWSTR,
            C.POINTER(Startup), C.POINTER(Process)]),
        "SetProcessWorkingSetSizeEx": (W.BOOL, [HANDLE, SIZE, SIZE, W.DWORD]),
        "GetProcessWorkingSetSizeEx": (W.BOOL, [HANDLE, C.POINTER(SIZE), C.POINTER(SIZE), C.POINTER(W.DWORD)]),
        "InitializeProcThreadAttributeList": (W.BOOL, [C.c_void_p, W.DWORD, W.DWORD, C.POINTER(SIZE)]),
        "UpdateProcThreadAttribute": (W.BOOL, [C.c_void_p, W.DWORD, SIZE, C.c_void_p, SIZE, C.c_void_p, C.c_void_p]),
        "DeleteProcThreadAttributeList": (None, [C.c_void_p]),
        "K32GetProcessMemoryInfo": (W.BOOL, [HANDLE, C.c_void_p, W.DWORD]),
        "ResumeThread": (W.DWORD, [HANDLE]),
        "WaitForSingleObject": (W.DWORD, [HANDLE, W.DWORD]),
        "GetExitCodeProcess": (W.BOOL, [HANDLE, C.POINTER(W.DWORD)]),
        "TerminateProcess": (W.BOOL, [HANDLE, W.UINT]),
        "CloseHandle": (W.BOOL, [HANDLE]),
    }
    for name, (result, args) in signatures.items():
        f = getattr(k, name)
        f.restype, f.argtypes = result, args
    return k


def checked(ok, operation):
    if not ok:
        raise OSError(C.get_last_error(), operation)


def quote_argument(value):
    if any(c in value for c in ('"', '\r', '\n')) or value.endswith('\\'):
        raise RuntimeError("UNSAFE_FIXED_ARGUMENT")
    return '"' + value + '"'


def run_child(exe, argument, cwd, deadline, commit_cap, rss_cap, writer,
              output_guard, notify_created, notify_resumed):
    """One direct child, no retries. Native trust/loader closure is external.

    `writer` limits pipe bytes before storing them. `output_guard` checks fixed
    generated file sizes. Wall deadline is external to cooperative native code.
    PeakWorkingSetSize catches any observed historical RSS excess at FIN.
    """
    import msvcrt
    k = api()
    job = k.CreateJobObjectW(None, None)
    checked(job, "CreateJobObjectW")
    limits = Extended()
    limits.BasicLimitInformation.LimitFlags = 0x2000 | 0x0008 | 0x0100 | 0x0200
    limits.BasicLimitInformation.ActiveProcessLimit = 1
    limits.ProcessMemoryLimit = limits.JobMemoryLimit = commit_cap
    pi, created, resumed = Process(), False, False
    attributes_ready, attributes = False, None
    stop, faults = threading.Event(), []
    readers, descriptors = [], []
    peak_rss, peak_private, peak_job_commit, reason, code, api_error = 0, 0, 0, None, None, None
    wait_signalled = False
    try:
        checked(k.SetInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits)),
                "SetInformationJobObject")
        actual_limits = Extended()
        checked(k.QueryInformationJobObject(job, 9, C.byref(actual_limits), C.sizeof(actual_limits), None),
                "QueryInformationJobObject")
        if (actual_limits.BasicLimitInformation.LimitFlags & 0x2308 != 0x2308 or
                actual_limits.BasicLimitInformation.ActiveProcessLimit != 1 or
                actual_limits.ProcessMemoryLimit != commit_cap or actual_limits.JobMemoryLimit != commit_cap):
            raise RuntimeError("JOB_LIMIT_READBACK_MISMATCH")
        pairs = [os.pipe(), os.pipe()]
        null_fd = os.open("NUL", os.O_RDONLY)
        descriptors = [null_fd] + [fd for pair in pairs for fd in pair]
        for fd in (null_fd, pairs[0][1], pairs[1][1]):
            os.set_inheritable(fd, True)
        sx = StartupEx()
        si = sx.StartupInfo
        si.cb, si.dwFlags, si.wShowWindow = C.sizeof(sx), 0x0101, 0
        si.hStdInput = msvcrt.get_osfhandle(null_fd)
        si.hStdOutput = msvcrt.get_osfhandle(pairs[0][1])
        si.hStdError = msvcrt.get_osfhandle(pairs[1][1])
        wanted_size = SIZE()
        k.InitializeProcThreadAttributeList(None, 1, 0, C.byref(wanted_size))
        if not 0 < wanted_size.value <= 65536:
            raise RuntimeError("ATTRIBUTE_LIST_SIZE")
        attributes = C.create_string_buffer(wanted_size.value)
        sx.lpAttributeList = C.cast(attributes, C.c_void_p)
        checked(k.InitializeProcThreadAttributeList(sx.lpAttributeList, 1, 0, C.byref(wanted_size)),
                "InitializeProcThreadAttributeList")
        attributes_ready = True
        allowed_handles = (HANDLE * 3)(si.hStdInput, si.hStdOutput, si.hStdError)
        checked(k.UpdateProcThreadAttribute(sx.lpAttributeList, 0, 0x00020002,
                C.byref(allowed_handles), C.sizeof(allowed_handles), None, None),
                "UpdateProcThreadAttribute_HANDLE_LIST")
        env = {"SystemRoot": r"C:\Windows", "WINDIR": r"C:\Windows",
            "PATH": r"C:\Windows\System32", "TEMP": str(cwd / "tmp"),
            "TMP": str(cwd / "tmp"), "TZ": "UTC"}
        block = C.create_unicode_buffer('\0'.join(k + '=' + v for k, v in sorted(env.items())) + '\0\0')
        command = C.create_unicode_buffer(quote_argument(str(exe)) + ' ' + quote_argument(str(argument)))
        checked(k.CreateProcessW(str(exe), command, None, None, True,
            0x0004 | 0x0400 | 0x08000000 | 0x00080000, C.cast(block, C.c_void_p), str(cwd),
            C.cast(C.byref(sx), C.POINTER(Startup)), C.byref(pi)), "CreateProcessW_SUSPENDED")
        created = True
        notify_created(int(pi.dwProcessId))
        checked(k.AssignProcessToJobObject(job, pi.hProcess), "AssignProcessToJobObject")
        # HARDWS_MAX_ENABLE=4; MIN_DISABLE=2. No quiet privilege fallback.
        checked(k.SetProcessWorkingSetSizeEx(pi.hProcess, 1 << 20, rss_cap, 0x0006),
                "SetProcessWorkingSetSizeEx_HARD_MAX")
        low, high, flags = SIZE(), SIZE(), W.DWORD()
        checked(k.GetProcessWorkingSetSizeEx(pi.hProcess, C.byref(low), C.byref(high), C.byref(flags)),
                "GetProcessWorkingSetSizeEx")
        if not (flags.value & 4) or high.value > rss_cap:
            raise RuntimeError("WORKING_SET_QUOTA_READBACK_MISMATCH")
        for fd in (null_fd, pairs[0][1], pairs[1][1]):
            os.close(fd)
            descriptors.remove(fd)

        def drain(fd, channel):
            try:
                while True:
                    data = os.read(fd, 4096)
                    if not data:
                        return
                    writer(channel, data)
            except BaseException as e:
                faults.append(type(e).__name__ + ":" + str(e))
                stop.set()
            finally:
                os.close(fd)

        for channel, pair in zip(("stdout", "stderr"), pairs):
            t = threading.Thread(target=drain, args=(pair[0], channel), daemon=True)
            readers.append(t)
            descriptors.remove(pair[0])
            t.start()
        if time.monotonic() >= deadline:
            raise RuntimeError("SHARED_WALL_BUDGET_EXHAUSTED_BEFORE_RESUME")
        if k.ResumeThread(pi.hThread) == 0xffffffff:
            raise OSError(C.get_last_error(), "ResumeThread")
        resumed = True
        notify_resumed(int(pi.dwProcessId))
        while True:
            state = k.WaitForSingleObject(pi.hProcess, 25)
            if state not in (0, 258):
                raise OSError(C.get_last_error(), "WaitForSingleObject")
            memory = Memory()
            memory.cb = C.sizeof(memory)
            checked(k.K32GetProcessMemoryInfo(pi.hProcess, C.byref(memory), C.sizeof(memory)),
                    "K32GetProcessMemoryInfo")
            peak_rss = max(peak_rss, int(memory.PeakWorkingSetSize))
            peak_private = max(peak_private, int(memory.PrivateUsage))
            usage = Extended()
            checked(k.QueryInformationJobObject(job, 9, C.byref(usage), C.sizeof(usage), None),
                    "QueryInformationJobObject_PEAK_COMMIT")
            peak_job_commit = max(peak_job_commit, int(usage.PeakJobMemoryUsed))
            if peak_rss > rss_cap or peak_private > commit_cap or peak_job_commit > commit_cap:
                reason = "MEMORY_LIMIT_NO_VERDICT"
            elif stop.is_set():
                reason = "PIPE_LIMIT_OR_ERROR_NO_VERDICT"
            elif time.monotonic() >= deadline:
                reason = "HARD_WALL_NO_VERDICT"
            else:
                output_guard()
            if reason:
                checked(k.TerminateJobObject(job, 0xee), "TerminateJobObject")
                checked(k.WaitForSingleObject(pi.hProcess, 5000) == 0, "WAIT_AFTER_TERMINATION")
                wait_signalled = True
                break
            if state == 0:
                wait_signalled = True
                break
        exit_value = W.DWORD()
        checked(k.GetExitCodeProcess(pi.hProcess, C.byref(exit_value)), "GetExitCodeProcess")
        code = int(exit_value.value)
    except BaseException as error:
        api_error = type(error).__name__ + ":" + str(error)
        if created:
            # Assignment can fail, so TerminateProcess is required as fallback.
            k.TerminateJobObject(job, 0xee)
            k.TerminateProcess(pi.hProcess, 0xee)
            wait_signalled = k.WaitForSingleObject(pi.hProcess, 5000) == 0
            observed_exit = W.DWORD()
            if k.GetExitCodeProcess(pi.hProcess, C.byref(observed_exit)):
                code = int(observed_exit.value)
    finally:
        if attributes_ready:
            k.DeleteProcThreadAttributeList(C.cast(attributes, C.c_void_p))
        if created:
            k.CloseHandle(pi.hThread)
            k.CloseHandle(pi.hProcess)
        k.CloseHandle(job)  # KILL_ON_JOB_CLOSE applies even on a parent exception.
        for fd in descriptors:
            os.close(fd)
        for t in readers:
            t.join(5)
        if any(t.is_alive() for t in readers):
            faults.append("PIPE_THREAD_DID_NOT_CLOSE")
    return {"pid": int(pi.dwProcessId), "created_suspended": created,
        "resumed": resumed, "exit_code": code, "termination_reason": reason,
        "wait_signalled": wait_signalled,
        "FIN_kind": "CONFIRMED_PROCESS_EXIT" if wait_signalled else "CONTROL_RETURN_EXIT_UNCONFIRMED",
        "api_or_control_error": api_error,
        "peak_rss_bytes": peak_rss, "observed_peak_private_bytes": peak_private,
        "peak_job_committed_bytes": peak_job_commit,
        "pipe_faults": faults, "commit_quota_bytes": commit_cap,
        "hard_working_set_requested_bytes": rss_cap}
