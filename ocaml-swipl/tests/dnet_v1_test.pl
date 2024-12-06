/* Making sure we [exit 1] on a user-error. */
set_prolog_flag(on_error, halt).

/* Loading the file with our rules. */
[dnet_v1].

/* Adding the premises. */
assertz(prem(0, 'P')).
assertz(prem(1, 'Q')).
assertz(prem(2, 'R')).
assertz(prem(3, 'S')).
assertz(prem(4, 'T')).

/* Adding the conclusions. */
assertz(cncl(0, 'A')).
assertz(cncl(1, 'Q')).
assertz(cncl(2, 'B')).
assertz(cncl(3, 'P')).
assertz(cncl(4, 'C')).

/* Adding cancel hints. */
assertz(cancel(0, [X], [X])).

/* Query. */
call_nth(
  (match_any(KIND, HID, PIDS, CIDS),
   format("KIND=~w, HID=~w, PIDS=~w, CIDS=~w~n", [KIND, HID, PIDS, CIDS])),
  100
).
