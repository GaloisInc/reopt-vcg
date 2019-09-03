def orpd1 : instruction :=
  definst "orpd" $ do
    pattern fun (v_2978 : reg (bv 128)) (v_2979 : reg (bv 128)) => do
      v_4810 <- getRegister v_2979;
      v_4811 <- getRegister v_2978;
      setRegister (lhs.of_reg v_2979) (bv_or v_4810 v_4811);
      pure ()
    pat_end;
    pattern fun (v_2973 : Mem) (v_2974 : reg (bv 128)) => do
      v_9148 <- getRegister v_2974;
      v_9149 <- evaluateAddress v_2973;
      v_9150 <- load v_9149 16;
      setRegister (lhs.of_reg v_2974) (bv_or v_9148 v_9150);
      pure ()
    pat_end
