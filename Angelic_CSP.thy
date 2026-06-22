section \<open>Angelic CSP via UTP\<close>

theory Angelic_CSP
  imports "UTP-Reactive-Designs.utp_rea_designs"
begin

term "pre\<^sub>R"
term "post\<^sub>R"
term "SRD"
term "NSRD"
thm SRD_def
find_theorems pre\<^sub>R

end
