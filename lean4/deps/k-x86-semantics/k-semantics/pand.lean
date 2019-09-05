def pand1 : instruction :=
  definst "pand" $ do
    pattern fun (v_3257 : reg (bv 128)) (v_3258 : reg (bv 128)) => do
      v_6281 <- getRegister v_3258;
      v_6282 <- getRegister v_3257;
      setRegister (lhs.of_reg v_3258) (bv_and v_6281 v_6282);
      pure ()
    pat_end;
    pattern fun (v_3252 : Mem) (v_3253 : reg (bv 128)) => do
      v_10188 <- getRegister v_3253;
      v_10189 <- evaluateAddress v_3252;
      v_10190 <- load v_10189 16;
      setRegister (lhs.of_reg v_3253) (bv_and v_10188 v_10190);
      pure ()
    pat_end
