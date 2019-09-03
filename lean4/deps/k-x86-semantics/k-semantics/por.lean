def por1 : instruction :=
  definst "por" $ do
    pattern fun (v_2886 : reg (bv 128)) (v_2887 : reg (bv 128)) => do
      v_6415 <- getRegister v_2887;
      v_6416 <- getRegister v_2886;
      setRegister (lhs.of_reg v_2887) (bv_or v_6415 v_6416);
      pure ()
    pat_end;
    pattern fun (v_2882 : Mem) (v_2883 : reg (bv 128)) => do
      v_13322 <- getRegister v_2883;
      v_13323 <- evaluateAddress v_2882;
      v_13324 <- load v_13323 16;
      setRegister (lhs.of_reg v_2883) (bv_or v_13322 v_13324);
      pure ()
    pat_end
