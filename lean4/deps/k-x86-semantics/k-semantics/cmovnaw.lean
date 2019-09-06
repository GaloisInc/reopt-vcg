def cmovnaw1 : instruction :=
  definst "cmovnaw" $ do
    pattern fun (v_2851 : reg (bv 16)) (v_2852 : reg (bv 16)) => do
      v_4548 <- getRegister cf;
      v_4549 <- getRegister zf;
      v_4551 <- getRegister v_2851;
      v_4552 <- getRegister v_2852;
      setRegister (lhs.of_reg v_2852) (mux (bit_or v_4548 v_4549) v_4551 v_4552);
      pure ()
    pat_end;
    pattern fun (v_2847 : Mem) (v_2848 : reg (bv 16)) => do
      v_7929 <- getRegister cf;
      v_7930 <- getRegister zf;
      v_7932 <- evaluateAddress v_2847;
      v_7933 <- load v_7932 2;
      v_7934 <- getRegister v_2848;
      setRegister (lhs.of_reg v_2848) (mux (bit_or v_7929 v_7930) v_7933 v_7934);
      pure ()
    pat_end
