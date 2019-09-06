def cmovoq1 : instruction :=
  definst "cmovoq" $ do
    pattern fun (v_3217 : reg (bv 64)) (v_3218 : reg (bv 64)) => do
      v_4985 <- getRegister of;
      v_4986 <- getRegister v_3217;
      v_4987 <- getRegister v_3218;
      setRegister (lhs.of_reg v_3218) (mux v_4985 v_4986 v_4987);
      pure ()
    pat_end;
    pattern fun (v_3213 : Mem) (v_3214 : reg (bv 64)) => do
      v_8240 <- getRegister of;
      v_8241 <- evaluateAddress v_3213;
      v_8242 <- load v_8241 8;
      v_8243 <- getRegister v_3214;
      setRegister (lhs.of_reg v_3214) (mux v_8240 v_8242 v_8243);
      pure ()
    pat_end
