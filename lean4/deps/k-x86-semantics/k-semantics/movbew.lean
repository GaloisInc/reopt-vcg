def movbew1 : instruction :=
  definst "movbew" $ do
    pattern fun (v_2448 : reg (bv 16)) (v_2447 : Mem) => do
      v_8404 <- evaluateAddress v_2447;
      v_8405 <- getRegister v_2448;
      store v_8404 (concat (extract v_8405 8 16) (extract v_8405 0 8)) 2;
      pure ()
    pat_end;
    pattern fun (v_2455 : Mem) (v_2456 : reg (bv 16)) => do
      v_8672 <- evaluateAddress v_2455;
      v_8673 <- load v_8672 2;
      setRegister (lhs.of_reg v_2456) (concat (extract v_8673 8 16) (extract v_8673 0 8));
      pure ()
    pat_end
