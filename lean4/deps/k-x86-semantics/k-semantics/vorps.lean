def vorps1 : instruction :=
  definst "vorps" $ do
    pattern fun (v_3241 : Mem) (v_3242 : reg (bv 128)) (v_3243 : reg (bv 128)) => do
      v_10483 <- getRegister v_3242;
      v_10484 <- evaluateAddress v_3241;
      v_10485 <- load v_10484 16;
      setRegister (lhs.of_reg v_3243) (bv_or v_10483 v_10485);
      pure ()
    pat_end;
    pattern fun (v_3252 : Mem) (v_3253 : reg (bv 256)) (v_3254 : reg (bv 256)) => do
      v_10488 <- getRegister v_3253;
      v_10489 <- evaluateAddress v_3252;
      v_10490 <- load v_10489 32;
      setRegister (lhs.of_reg v_3254) (bv_or v_10488 v_10490);
      pure ()
    pat_end
