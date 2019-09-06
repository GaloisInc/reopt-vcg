def cmovcl1 : instruction :=
  definst "cmovcl" $ do
    pattern fun (v_2599 : reg (bv 32)) (v_2600 : reg (bv 32)) => do
      v_4262 <- getRegister cf;
      v_4263 <- getRegister v_2599;
      v_4264 <- getRegister v_2600;
      setRegister (lhs.of_reg v_2600) (mux v_4262 v_4263 v_4264);
      pure ()
    pat_end;
    pattern fun (v_2592 : Mem) (v_2595 : reg (bv 32)) => do
      v_7736 <- getRegister cf;
      v_7737 <- evaluateAddress v_2592;
      v_7738 <- load v_7737 4;
      v_7739 <- getRegister v_2595;
      setRegister (lhs.of_reg v_2595) (mux v_7736 v_7738 v_7739);
      pure ()
    pat_end
