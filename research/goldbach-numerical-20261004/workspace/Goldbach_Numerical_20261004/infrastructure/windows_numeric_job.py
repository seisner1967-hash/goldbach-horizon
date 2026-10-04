"""Windows numerical process control derived from the working build04 backend.

No hard working-set requests: these can require unavailable privileges.
Commit limits and kill-on-close remain enforced by a Windows Job. Console
helpers inherit this Job, so process accounting includes them.
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


class Pids(C.Structure):
    _fields_ = [("NumberOfAssignedProcesses", W.DWORD),
        ("NumberOfProcessIdsInList", W.DWORD), ("ProcessIdList", SIZE * 16)]


class Accounting(C.Structure):
    _fields_ = [(n, C.c_longlong) for n in ("TotalUserTime", "TotalKernelTime",
        "ThisPeriodTotalUserTime", "ThisPeriodTotalKernelTime")] + [
        (n, W.DWORD) for n in ("TotalPageFaultCount", "TotalProcesses",
        "ActiveProcesses", "TotalTerminatedProcesses")]


def api():
    if os.name != "nt" or C.sizeof(C.c_void_p) != 8:
        raise RuntimeError("WINDOWS_X64_REQUIRED")
    if tuple(map(C.sizeof, (Basic, Extended, Startup, Process, Memory, StartupEx, Pids, Accounting))) != (64, 144, 104, 24, 80, 112, 136, 48):
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
        "InitializeProcThreadAttributeList": (W.BOOL, [C.c_void_p, W.DWORD, W.DWORD, C.POINTER(SIZE)]),
        "UpdateProcThreadAttribute": (W.BOOL, [C.c_void_p, W.DWORD, SIZE, C.c_void_p, SIZE, C.c_void_p, C.c_void_p]),
        "DeleteProcThreadAttributeList": (None, [C.c_void_p]),
        "K32GetProcessMemoryInfo": (W.BOOL, [HANDLE, C.c_void_p, W.DWORD]),
        "OpenProcess": (HANDLE, [W.DWORD, W.BOOL, W.DWORD]),
        "IsProcessInJob": (W.BOOL, [HANDLE, HANDLE, C.POINTER(W.BOOL)]),
        "ResumeThread": (W.DWORD, [HANDLE]),
        "WaitForSingleObject": (W.DWORD, [HANDLE, W.DWORD]),
        "GetExitCodeProcess": (W.BOOL, [HANDLE, C.POINTER(W.DWORD)]),
        "GetProcessTimes": (W.BOOL, [HANDLE, C.POINTER(W.FILETIME),
            C.POINTER(W.FILETIME), C.POINTER(W.FILETIME), C.POINTER(W.FILETIME)]),
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


def run_child(exe, arguments, cwd, deadline, commit_cap, rss_cap, writer,
              output_guard, notify_created, notify_resumed, progress=None,
              progress_seconds=30):
    """One numerical invocation with its console helpers, no retries.

    `writer` limits pipe bytes before storing them. `output_guard` checks fixed
    generated file sizes. Wall deadline is external to cooperative native code.
    Commit applies to the whole Job and each member. Working-set limits are
    not requested: per-process peak RSS and the sum of live RSS are monitored,
    not represented as hard kernel RSS quotas. Every enumerated process is
    required to belong to this Job. Short-lived process RSS peaks may escape
    enumeration; job commit remains independently OS limited.
    """
    import msvcrt
    k = api()
    job = k.CreateJobObjectW(None, None)
    checked(job, "CreateJobObjectW")
    limits = Extended()
    # No JOB_OBJECT_LIMIT_WORKINGSET (0x0001), no priority/scheduling change,
    # no privilege enabling, and no reduced-control retry on API failure.
    requested_flags = 0x2000 | 0x0008 | 0x0100 | 0x0200
    limits.BasicLimitInformation.LimitFlags = requested_flags
    limits.BasicLimitInformation.ActiveProcessLimit = 16
    limits.BasicLimitInformation.MinimumWorkingSetSize = 0
    limits.BasicLimitInformation.MaximumWorkingSetSize = 0
    limits.ProcessMemoryLimit = limits.JobMemoryLimit = commit_cap
    pi, created, resumed = Process(), False, False
    attributes_ready, attributes = False, None
    stop, faults = threading.Event(), []
    readers, descriptors = [], []
    peak_rss, peak_private, reason, code, api_error = 0, 0, None, None, None
    peak_job_rss, peak_job_commit, total_processes, observed_pids = 0, 0, 0, set()
    wait_signalled, job_empty = False, False
    entered, last_progress = time.monotonic(), 0.0
    user_seconds, kernel_seconds, live_rss = 0.0, 0.0, 0
    try:
        checked(k.SetInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits)),
                "SetInformationJobObject")
        actual_limits = Extended()
        checked(k.QueryInformationJobObject(job, 9, C.byref(actual_limits), C.sizeof(actual_limits), None),
                "QueryInformationJobObject")
        if (actual_limits.BasicLimitInformation.LimitFlags != requested_flags or
                actual_limits.BasicLimitInformation.ActiveProcessLimit != 16 or
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
            "PATH": r"C:\msys64\ucrt64\bin;C:\Windows\System32", "TEMP": str(cwd / "tmp"),
            "TMP": str(cwd / "tmp"), "TZ": "UTC"}
        block = C.create_unicode_buffer('\0'.join(k + '=' + v for k, v in sorted(env.items())) + '\0\0')
        command = C.create_unicode_buffer(' '.join(quote_argument(str(a)) for a in [exe] + arguments))
        checked(k.CreateProcessW(str(exe), command, None, None, True,
            0x0004 | 0x0400 | 0x08000000 | 0x00080000, C.cast(block, C.c_void_p), str(cwd),
            C.cast(C.byref(sx), C.POINTER(Startup)), C.byref(pi)), "CreateProcessW_SUSPENDED")
        created = True
        notify_created(int(pi.dwProcessId))
        checked(k.AssignProcessToJobObject(job, pi.hProcess), "AssignProcessToJobObject")
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
            account, members = Accounting(), Pids()
            checked(k.QueryInformationJobObject(job, 1, C.byref(account), C.sizeof(account), None),
                    "QueryInformationJobObject_ACCOUNTING")
            checked(k.QueryInformationJobObject(job, 3, C.byref(members), C.sizeof(members), None),
                    "QueryInformationJobObject_PIDS")
            if members.NumberOfProcessIdsInList > 16:
                raise RuntimeError("JOB_PID_LIST_OVERFLOW")
            total_processes = max(total_processes, int(account.TotalProcesses))
            live_rss = 0
            for pid in members.ProcessIdList[:members.NumberOfProcessIdsInList]:
                observed_pids.add(int(pid))
                ph = k.OpenProcess(0x0410, False, int(pid))
                if not ph:
                    if C.get_last_error() == 87:  # exited during enumeration
                        continue
                    raise OSError(C.get_last_error(), "OpenProcess_JOB_MEMBER")
                try:
                    belongs = W.BOOL()
                    checked(k.IsProcessInJob(ph, job, C.byref(belongs)), "IsProcessInJob")
                    if not belongs.value:  # possible PID reuse after exit
                        continue
                    memory = Memory()
                    memory.cb = C.sizeof(memory)
                    checked(k.K32GetProcessMemoryInfo(ph, C.byref(memory), C.sizeof(memory)),
                            "K32GetProcessMemoryInfo_JOB_MEMBER")
                    live_rss += int(memory.WorkingSetSize)
                    peak_rss = max(peak_rss, int(memory.PeakWorkingSetSize))
                    peak_private = max(peak_private, int(memory.PrivateUsage))
                finally:
                    k.CloseHandle(ph)
            peak_job_rss = max(peak_job_rss, live_rss)
            usage = Extended()
            checked(k.QueryInformationJobObject(job, 9, C.byref(usage), C.sizeof(usage), None),
                    "QueryInformationJobObject_PEAK_COMMIT")
            peak_job_commit = max(peak_job_commit, int(usage.PeakJobMemoryUsed))
            created_ft, exited_ft, kernel_ft, user_ft = (W.FILETIME() for _ in range(4))
            checked(k.GetProcessTimes(pi.hProcess, C.byref(created_ft), C.byref(exited_ft),
                C.byref(kernel_ft), C.byref(user_ft)), "GetProcessTimes")
            user_seconds = ((user_ft.dwHighDateTime << 32) | user_ft.dwLowDateTime) / 10000000
            kernel_seconds = ((kernel_ft.dwHighDateTime << 32) | kernel_ft.dwLowDateTime) / 10000000
            now = time.monotonic()
            if progress is not None and (now - last_progress >= progress_seconds or state == 0):
                progress({"pid": int(pi.dwProcessId), "elapsed_seconds": now - entered,
                    "cpu_user_seconds": user_seconds, "cpu_kernel_seconds": kernel_seconds,
                    "cpu_total_seconds": user_seconds + kernel_seconds,
                    "live_rss_bytes": live_rss, "peak_rss_bytes": peak_rss,
                    "peak_private_bytes": peak_private, "peak_job_commit_bytes": peak_job_commit,
                    "active_processes": int(account.ActiveProcesses), "process_exited": state == 0})
                last_progress = now
            if peak_rss > rss_cap or peak_private > commit_cap or live_rss > 4294967296 or peak_job_commit > commit_cap:
                reason = "MEMORY_LIMIT_NO_VERDICT"
            elif total_processes > 32:
                reason = "JOB_TOTAL_PROCESS_CAP_NO_VERDICT"
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
            if state == 0 and account.ActiveProcesses == 0:
                wait_signalled, job_empty = True, True
                break
            if state == 0:
                time.sleep(0.025)  # driver finished while owned descendants remain
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
        final_account = Accounting()
        if k.QueryInformationJobObject(job, 1, C.byref(final_account), C.sizeof(final_account), None):
            job_empty = final_account.ActiveProcesses == 0
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
        "api_or_control_error": api_error,
        "wait_signalled": wait_signalled, "job_empty_confirmed": job_empty,
        "FIN_kind": "CONFIRMED_DRIVER_AND_JOB_EXIT" if wait_signalled and job_empty else "CONTROL_RETURN_EXIT_UNCONFIRMED",
        "peak_rss_bytes": peak_rss, "observed_peak_private_bytes": peak_private,
        "wall_seconds": time.monotonic() - entered,
        "cpu_user_seconds": user_seconds, "cpu_kernel_seconds": kernel_seconds,
        "cpu_total_seconds": user_seconds + kernel_seconds,
        "pipe_faults": faults, "commit_quota_bytes": commit_cap,
        "job_limit_flags_requested": requested_flags,
        "working_set_limit_flag_requested": False,
        "rss_os_enforced": False,
        "rss_control": "SAMPLED_PROCESS_PEAK_AND_LIVE_JOB_SUM",
        "rss_per_process_monitor_bytes": rss_cap,
        "job_committed_memory_OS_limit_requested": True,
        "max_active_job_processes": 16, "max_total_job_processes": 32,
        "total_job_processes": total_processes, "observed_job_pids": sorted(observed_pids),
        "peak_job_committed_bytes": peak_job_commit,
        "observed_peak_live_job_rss": peak_job_rss, "sampled_job_rss_cap_bytes": 4294967296}
