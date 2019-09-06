def cmovnal1 : instruction :=
  definst "cmovnal" $ do
    pattern fun (v_2836 : reg (bv 32)) (v_2837 : reg (bv 32)) => do
      v_4526 <- getRegister cf;
      v_4527 <- getRegister zf;
      v_4529 <- getRegister v_2836;
      v_4530 <- getRegister v_2837;
      setRegister (lhs.of_reg v_2837) (mux (bit_or v_4526 v_4527) v_4529 v_4530);
      pure ()
    pat_end;
    pattern fun (v_2829 : Mem) (v_2832 : reg (bv 32)) => do
      v_7913 <- getRegister cf;
      v_7914 <- getRegister zf;
      v_7916 <- evaluateAddress v_2829;
      v_7917 <- load v_7916 4;
      v_7918 <- getRegister v_2832;
      setRegister (lhs.of_reg v_2832) (mux (bit_or v_7913 v_7914) v_7917 v_7918);
      pure ()
    pat_end
