def cmovnoq1 : instruction :=
  definst "cmovnoq" $ do
    pattern fun (v_3085 : reg (bv 64)) (v_3086 : reg (bv 64)) => do
      v_4851 <- getRegister of;
      v_4853 <- getRegister v_3085;
      v_4854 <- getRegister v_3086;
      setRegister (lhs.of_reg v_3086) (mux (notBool_ v_4851) v_4853 v_4854);
      pure ()
    pat_end;
    pattern fun (v_3081 : Mem) (v_3082 : reg (bv 64)) => do
      v_8154 <- getRegister of;
      v_8156 <- evaluateAddress v_3081;
      v_8157 <- load v_8156 8;
      v_8158 <- getRegister v_3082;
      setRegister (lhs.of_reg v_3082) (mux (notBool_ v_8154) v_8157 v_8158);
      pure ()
    pat_end
