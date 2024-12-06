/* Premise and conclusion predicates (index, pattern). */
:- dynamic prem/2.
:- dynamic cncl/2.

/* Forward hint predicate (index, list of (conclusion) patterns). */
:- dynamic fwd/2.

/* Forward hint predicate (index, list of (premise) patterns). */
:- dynamic bwd/2.

/* Cancel hint predicate (index, list of (premise) patterns, list of (conclusion) patterns). */
:- dynamic cancel/3.

/* CancelX hint predicate (index, list of (premise) patterns, list of (conclusion) patterns). */
:- dynamic cancelx/3.

/* Observe hint predicate (index, list of (premise) patterns, list of (conclusion) patterns). */
:- dynamic observe/3.

/* Learnable hint predicate (index, list of (premise) patterns, list of (conclusion) patterns). */
:- dynamic learnable/3.

/* Cleanup ******************************************************************/

cleanup :-
  retractall(prem(_, _)),
  retractall(cncl(_, _)),
  retractall(fwd(_, _)),
  retractall(bwd(_, _)),
  retractall(cancel(_, _, _)),
  retractall(cancelx(_, _, _)),
  retractall(observe(_, _, _)),
  retractall(learnable(_, _, _)).

/* Forward hints ************************************************************/

match_fwd([], [], []).

match_fwd([FPAT|FPATS], [PID|PIDS], [PPAT|PPATS]) :-
  unify_with_occurs_check(FPAT, PPAT),
  prem(PID, PPAT),
  assertion(integer(PID)),
  match_fwd(FPATS, PIDS, PPATS).

match_fwd_toplevel(HID, PIDS) :-
  fwd(HID, FPATS),
  match_fwd(FPATS, PIDS, _),
  assertion(integer(HID)),
  is_set(PIDS).

:- discontiguous match_any/4.
match_any(fwd, HID, PIDS, []) :-
  match_fwd_toplevel(HID, PIDS).

/* Backward hints ***********************************************************/

match_bwd([], [], []).

match_bwd([BPAT|BPATS], [CID|CIDS], [CPAT|CPATS]) :-
  unify_with_occurs_check(BPAT, CPAT),
  cncl(CID, CPAT),
  assertion(integer(CID)),
  match_bwd(BPATS, CIDS, CPATS).

match_bwd_toplevel(HID, CIDS) :-
  bwd(HID, BPATS),
  match_bwd(BPATS, CIDS, _),
  assertion(integer(HID)),
  is_set(CIDS).

match_any(bwd, HID, [], CIDS) :-
  match_bwd_toplevel(HID, CIDS).

/* Cancel hints *************************************************************/

match_cancel_toplevel(HID, PIDS, CIDS) :-
  cancel(HID, FPATS, BPATS),
  match_fwd(FPATS, PIDS, _),
  is_set(PIDS),
  match_bwd(BPATS, CIDS, _),
  is_set(CIDS).

match_any(cancel, HID, PIDS, CIDS) :-
  match_cancel_toplevel(HID, PIDS, CIDS).

/* CancelX hints ************************************************************/

match_cancelx_toplevel(HID, PIDS, CIDS) :-
  cancelx(HID, FPATS, BPATS),
  match_fwd(FPATS, PIDS, _),
  is_set(PIDS),
  match_bwd(BPATS, CIDS, _),
  is_set(CIDS).

match_any(cancelx, HID, PIDS, CIDS) :-
  match_cancelx_toplevel(HID, PIDS, CIDS).

/* Observe hints ************************************************************/

match_observe_toplevel(HID, PIDS, CIDS) :-
  observe(HID, FPATS, BPATS),
  match_fwd(FPATS, PIDS, _),
  is_set(PIDS),
  match_bwd(BPATS, CIDS, _),
  is_set(CIDS).

match_any(observe, HID, PIDS, CIDS) :-
  match_observe_toplevel(HID, PIDS, CIDS).

/* Learnable hints **********************************************************/

match_learnable_toplevel(HID, PIDS, CIDS) :-
  learnable(HID, FPATS, BPATS),
  match_fwd(FPATS, PIDS, _),
  is_set(PIDS),
  match_bwd(BPATS, CIDS, _),
  is_set(CIDS).

match_any(learnable, HID, PIDS, CIDS) :-
  match_learnable_toplevel(HID, PIDS, CIDS).
