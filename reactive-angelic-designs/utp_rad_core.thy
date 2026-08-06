section \<open>Reactive Angelic Design Core\<close>

theory utp_rad_core
  imports "UTP-Angelic-Designs.utp_ades" "UTP-Reactive.utp_rea_core"
begin

subsection \<open>Alphabet (Paper Definition 26)\<close>

text \<open>
  A reactive angelic design retains the outer design observations @{term ok}
  and @{term "ok\<^sup>>"}.  Its initial state @{term s} and every state offered
  in the final angelic choice @{term ac} contain a trace, a refusal set, and a
  waiting flag.  Thus this record is the inner observation state, rather than
  a replacement for the complete reactive-process alphabet.
\<close>

(* Paper Definition 26, with the trace generalised from event lists to
   the trace algebra of Circus_Toolkit, as in reactive designs. *)
alphabet ('t::trace, 'e) rad_state =
  tr :: "'t"
  ref :: "'e set"
  wait :: bool

type_synonym ('t, 'e) reactive_angelic_rel =
  "('t, 'e) rad_state angelic_rel"
type_synonym ('t, 'e) reactive_angelic_design =
  "('t, 'e) rad_state angelic_design"

end
