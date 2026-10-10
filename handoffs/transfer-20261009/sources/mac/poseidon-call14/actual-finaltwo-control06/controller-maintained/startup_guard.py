"""Single-thread POSIX claim-to-owned-process transition; no spawning here."""
import signal,threading
CATCHABLE={signal.SIGTERM,signal.SIGHUP,signal.SIGINT}
class StartupGuard:
 def __init__(self):self.active=False;self.previous=None
 def block(self):
  assert not self.active and threading.active_count()==1,'single-thread startup required'
  previous=signal.pthread_sigmask(signal.SIG_BLOCK,CATCHABLE)
  if previous & CATCHABLE:
   signal.pthread_sigmask(signal.SIG_SETMASK,previous)
   raise RuntimeError('catchable termination already blocked before startup')
  self.previous=previous;self.active=True
 def child_unmask(self):
  # preexec_fn is used ONLY by this single-thread runner. The new session leader
  # must not inherit the parent critical-section mask: group SIGTERM must work.
  signal.pthread_sigmask(signal.SIG_SETMASK,self.previous)
 def restore(self):
  if self.active:
   self.active=False
   signal.pthread_sigmask(signal.SIG_SETMASK,self.previous)
