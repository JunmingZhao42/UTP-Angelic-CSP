section \<open>Reactive Angelic Design Core\<close>

theory utp_rad_core
  imports utp_ades
begin

subsection \<open>Alphabet (Paper Definition 26)\<close>

text \<open>
  A reactive angelic design retains the outer design observations @{term ok}
  and @{term "ok\<^sup>>"}.  Its initial state @{term s} and every state offered
  in the final angelic choice @{term ac} contain a trace, a refusal set, and a
  waiting flag.  Thus this record is the inner observation state, rather than
  a replacement for the complete reactive-process alphabet.
\<close>

(* Paper Definition 26. *)
alphabet 'e rad_state =
  tr :: "'e list"
  ref :: "'e set"
  wait :: bool

type_synonym 'e reactive_angelic_rel = "'e rad_state angelic_rel"
type_synonym 'e reactive_angelic_design = "'e rad_state angelic_design"

end
