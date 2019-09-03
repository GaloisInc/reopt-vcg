def vorps1 : instruction :=
  definst "vorps" $ do
    pattern fun (v_3165 : Mem) (v_3166 : reg (bv 128)) (v_3167 : reg (bv 128)) => do
      v_11635 <- getRegister v_3166;
      v_11636 <- evaluateAddress v_3165;
      v_11637 <- load v_11636 16;
      setRegister (lhs.of_reg v_3167) (bv_or v_11635 v_11637);
      pure ()
    pat_end;
    pattern fun (v_3176 : Mem) (v_3177 : reg (bv 256)) (v_3178 : reg (bv 256)) => do
      v_11640 <- getRegister v_3177;
      v_11641 <- evaluateAddress v_3176;
      v_11642 <- load v_11641 32;
      setRegister (lhs.of_reg v_3178) (bv_or v_11640 v_11642);
      pure ()
    pat_end
