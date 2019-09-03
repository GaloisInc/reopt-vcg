def vandps1 : instruction :=
  definst "vandps" $ do
    pattern fun (v_2751 : Mem) (v_2754 : reg (bv 128)) (v_2755 : reg (bv 128)) => do
      v_11164 <- getRegister v_2754;
      v_11165 <- evaluateAddress v_2751;
      v_11166 <- load v_11165 16;
      setRegister (lhs.of_reg v_2755) (bv_and v_11164 v_11166);
      pure ()
    pat_end;
    pattern fun (v_2762 : Mem) (v_2763 : reg (bv 256)) (v_2764 : reg (bv 256)) => do
      v_11169 <- getRegister v_2763;
      v_11170 <- evaluateAddress v_2762;
      v_11171 <- load v_11170 32;
      setRegister (lhs.of_reg v_2764) (bv_and v_11169 v_11171);
      pure ()
    pat_end
