def shlxq1 : instruction :=
  definst "shlxq" $ do
    pattern fun (v_2915 : reg (bv 64)) (v_2916 : reg (bv 64)) (v_2917 : reg (bv 64)) => do
      v_5146 <- getRegister v_2916;
      v_5147 <- getRegister v_2915;
      setRegister (lhs.of_reg v_2917) (extract (shl v_5146 (bv_and v_5147 (expression.bv_nat 64 63))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_2905 : reg (bv 64)) (v_2904 : Mem) (v_2906 : reg (bv 64)) => do
      v_9029 <- evaluateAddress v_2904;
      v_9030 <- load v_9029 8;
      v_9031 <- getRegister v_2905;
      setRegister (lhs.of_reg v_2906) (extract (shl v_9030 (bv_and v_9031 (expression.bv_nat 64 63))) 0 64);
      pure ()
    pat_end
