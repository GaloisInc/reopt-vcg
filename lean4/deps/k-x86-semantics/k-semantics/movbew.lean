def movbew1 : instruction :=
  definst "movbew" $ do
    pattern fun (v_2398 : reg (bv 16)) (v_2397 : Mem) => do
      v_8540 <- evaluateAddress v_2397;
      v_8541 <- getRegister v_2398;
      store v_8540 (concat (extract v_8541 8 16) (extract v_8541 0 8)) 2;
      pure ()
    pat_end;
    pattern fun (v_2405 : Mem) (v_2406 : reg (bv 16)) => do
      v_8808 <- evaluateAddress v_2405;
      v_8809 <- load v_8808 2;
      setRegister (lhs.of_reg v_2406) (concat (extract v_8809 8 16) (extract v_8809 0 8));
      pure ()
    pat_end
