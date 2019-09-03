def por1 : instruction :=
  definst "por" $ do
    pattern fun (v_2872 : reg (bv 128)) (v_2873 : reg (bv 128)) => do
      v_6564 <- getRegister v_2873;
      v_6565 <- getRegister v_2872;
      setRegister (lhs.of_reg v_2873) (bv_or v_6564 v_6565);
      pure ()
    pat_end;
    pattern fun (v_2867 : Mem) (v_2868 : reg (bv 128)) => do
      v_13797 <- getRegister v_2868;
      v_13798 <- evaluateAddress v_2867;
      v_13799 <- load v_13798 16;
      setRegister (lhs.of_reg v_2868) (bv_or v_13797 v_13799);
      pure ()
    pat_end
